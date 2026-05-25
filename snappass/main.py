import os
import sys
import uuid
import tempfile
import zipfile
from io import BytesIO
import threading
import time
from functools import wraps

import redis

from cryptography.fernet import Fernet
from flask import abort, Flask, render_template, request, jsonify, make_response, send_from_directory, redirect, send_file, url_for
from redis.exceptions import ConnectionError
from urllib.parse import quote_plus
from urllib.parse import unquote_plus
from urllib.parse import urljoin
# distutils removed in Python 3.12; keep local helper for compatibility.

def strtobool(value):
    """
    Convert a string representation of truth to True or False.
    Raises ValueError if the value is not recognized.
    """
    if isinstance(value, bool):
        return int(value)
    if value is None:
        raise ValueError("invalid truth value")
    val = str(value).strip().lower()
    if val in ("y", "yes", "t", "true", "on", "1"):
        return 1
    if val in ("n", "no", "f", "false", "off", "0"):
        return 0
    raise ValueError("invalid truth value")
# _ is required to get the Jinja templates translated
from flask_babel import Babel, _  # noqa: F401
from werkzeug.utils import secure_filename
from werkzeug.exceptions import RequestEntityTooLarge, BadRequest
from flask_cors import CORS

NO_SSL = bool(strtobool(os.environ.get('NO_SSL', 'False')))
URL_PREFIX = os.environ.get('URL_PREFIX', None)
HOST_OVERRIDE = os.environ.get('HOST_OVERRIDE', None)
TOKEN_SEPARATOR = '~'

# Define upload directory - configurable for Docker volume mounts
UPLOAD_FOLDER = os.environ.get('UPLOAD_FOLDER', '/tmp/uploads')
UPLOAD_FOLDER = os.path.abspath(UPLOAD_FOLDER)
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

# Ensure upload directory is writable at startup
try:
    _test_fd, _test_path = tempfile.mkstemp(dir=UPLOAD_FOLDER)
    os.close(_test_fd)
    os.remove(_test_path)
except OSError as e:
    print(f"WARNING: Upload folder {UPLOAD_FOLDER} is not writable: {e}", file=sys.stderr)

# Set temp directory environment
os.environ['TMPDIR'] = UPLOAD_FOLDER
tempfile.tempdir = UPLOAD_FOLDER

# Initialize Flask Application
app = Flask(__name__)
CORS(app)  # Enable CORS, required for frontend requests
if os.environ.get('DEBUG'):
    app.debug = True
app.secret_key = os.environ.get('SECRET_KEY', 'Secret Key')
app.config.update(
    dict(STATIC_URL=os.environ.get('STATIC_URL', 'static')))
# Force HTTPS when behind ingress; ProxyFix trusts X-Forwarded-Proto / X-Forwarded-Host
app.config['PREFERRED_URL_SCHEME'] = 'https' if not NO_SSL else 'http'
try:
    from werkzeug.middleware.proxy_fix import ProxyFix
    app.wsgi_app = ProxyFix(app.wsgi_app, x_proto=1, x_host=1)
except ImportError:
    pass
# Max upload size in MB (default 50); set MAX_UPLOAD_MB env to override
_max_upload_mb = int(os.environ.get('MAX_UPLOAD_MB', '50'))
app.config['MAX_CONTENT_LENGTH'] = _max_upload_mb * 1024 * 1024


# Set up Babel
def get_locale():
    return request.accept_languages.best_match(['en', 'es', 'de', 'nl'])


babel = Babel(app, locale_selector=get_locale)

# Initialize Redis
if os.environ.get('MOCK_REDIS'):
    from fakeredis import FakeStrictRedis

    redis_client = FakeStrictRedis()
elif os.environ.get('REDIS_URL'):
    redis_client = redis.StrictRedis.from_url(os.environ.get('REDIS_URL'))
else:
    redis_host = os.environ.get('REDIS_HOST', 'localhost')
    redis_port = os.environ.get('REDIS_PORT', 6379)
    redis_db = os.environ.get('SNAPPASS_REDIS_DB', 0)
    redis_client = redis.StrictRedis(
        host=redis_host, port=redis_port, db=redis_db)
REDIS_PREFIX = os.environ.get('REDIS_PREFIX', 'snappass')

TIME_CONVERSION = {'two weeks': 1209600, 'week': 604800, 'day': 86400,
                   'hour': 3600}
DEFAULT_API_TTL = 3600
MAX_TTL = 1209600


def check_redis_alive(fn):
    @wraps(fn)
    def inner(*args, **kwargs):
        try:
            if fn.__name__ == 'main':
                redis_client.ping()
            return fn(*args, **kwargs)
        except ConnectionError as e:
            print('Failed to connect to redis! %s' % e.message)
            if fn.__name__ == 'main':
                sys.exit(0)
            else:
                return abort(500)

    return inner


def encrypt(password):
    """
    Take a password string, encrypt it with Fernet symmetric encryption,
    and return the result (bytes), with the decryption key (bytes)
    """
    encryption_key = Fernet.generate_key()
    fernet = Fernet(encryption_key)
    encrypted_password = fernet.encrypt(password.encode('utf-8'))
    return encrypted_password, encryption_key


def decrypt(password, decryption_key):
    """
    Decrypt a password (bytes) using the provided key (bytes),
    and return the plain-text password (bytes).
    """
    fernet = Fernet(decryption_key)
    return fernet.decrypt(password)


def parse_token(token):
    token_fragments = token.split(TOKEN_SEPARATOR, 1)  # Split once, not more.
    storage_key = token_fragments[0]

    try:
        decryption_key = token_fragments[1].encode('utf-8')
    except IndexError:
        decryption_key = None

    return storage_key, decryption_key


def as_validation_problem(request, problem_type, problem_title, invalid_params):
    base_url = set_base_url(request)

    problem = {
        "type": base_url + problem_type,
        "title": problem_title,
        "invalid-params": invalid_params
    }
    return as_problem_response(problem)


def as_not_found_problem(request, problem_type, problem_title, invalid_params):
    base_url = set_base_url(request)

    problem = {
        "type": base_url + problem_type,
        "title": problem_title,
        "invalid-params": invalid_params
    }
    return as_problem_response(problem, 404)


def as_problem_response(problem, status_code=None):
    if not isinstance(status_code, int) or not status_code:
        status_code = 400

    response = make_response(jsonify(problem), status_code)
    response.headers['Content-Type'] = 'application/problem+json'
    return response


@check_redis_alive
def set_password(password, ttl, max_access_count):
    """
    Encrypt and store the password with a specified lifetime and access count.

    Returns a token comprised of the key where the encrypted password
    is stored, and the decryption key.
    """
    storage_key = REDIS_PREFIX + uuid.uuid4().hex
    encrypted_password, encryption_key = encrypt(password)
    
    # Store both encrypted password and max_access_count in a Redis hash
    redis_client.hset(storage_key, mapping={
        "password": encrypted_password,
        "decryption_key": encryption_key.decode('utf-8'),
        "access_count": max_access_count
    })
    # Set the expiry time for the hash
    redis_client.expire(storage_key, ttl)
    
    token = TOKEN_SEPARATOR.join([storage_key, encryption_key.decode('utf-8')])
    return token


@check_redis_alive
def get_password(token):
    """
    Retrieve and manage password access, decrementing the remaining access count.
    If the access count reaches zero, the password is deleted.
    """
    storage_key, decryption_key = parse_token(token)
    password_data = redis_client.hgetall(storage_key)
    
    if not password_data:
        return None
    
    # Decrypt the password
    encrypted_password = password_data.get(b"password")
    if encrypted_password is None:
        return None
    
    if decryption_key is not None:
        decrypted_password = decrypt(encrypted_password, decryption_key)
    else:
        decrypted_password = encrypted_password.decode('utf-8')
    
    # Decrement the access count
    access_count = int(password_data.get(b"access_count", 0))
    if access_count > 1:
        redis_client.hset(storage_key, "access_count", access_count - 1)
    else:
        redis_client.delete(storage_key)  # Delete after last access
    
    return decrypted_password.decode('utf-8')


@check_redis_alive
def password_exists(token):
    """
    Check if the password still exists based on both TTL and access count.
    """
    storage_key, _ = parse_token(token)
    if not redis_client.exists(storage_key):
        return False
    
    password_data = redis_client.hgetall(storage_key)
    access_count = int(password_data.get(b"access_count", 0))
    return access_count > 0


def empty(value):
    if not value:
        return True


def clean_input():
    """
    Make sure we're not getting bad data from the front end,
    format data to be machine readable
    """
    if empty(request.form.get('password', '')) or empty(request.form.get('ttl', '')) or empty(request.form.get('max_access_count', '')):
        abort(400)

    time_period = request.form['ttl'].lower()
    max_access_count = request.form.get('max_access_count')
    if time_period not in TIME_CONVERSION or not max_access_count.isdigit() or int(max_access_count) < 1:
        abort(400)

    return TIME_CONVERSION[time_period], request.form['password'], int(max_access_count)


def set_base_url(req):
    if NO_SSL:
        if HOST_OVERRIDE:
            base_url = f'http://{HOST_OVERRIDE}/'
        else:
            base_url = req.url_root
    else:
        if HOST_OVERRIDE:
            base_url = f'https://{HOST_OVERRIDE}/'
        else:
            base_url = req.url_root.replace("http://", "https://")
    if URL_PREFIX:
        base_url = base_url + URL_PREFIX.strip("/") + "/"
    return base_url

@app.route('/favicon.ico')
def favicon():
    return send_from_directory(
        os.path.join(app.root_path, 'static/snappass/images'),
        'favicon.svg',
        mimetype='image/svg+xml'
    )

@app.route('/')
def index():
    # Use the set_base_url function to determine the base URL dynamically
    upload_url = f"{set_base_url(request)}upload"
    base_url = set_base_url(request)

    return render_template('set_password.html', upload_url=upload_url, base_url=base_url)

@app.route('/', methods=['POST'])
def handle_password():
    ttl, password, max_access_count = clean_input()
    token = set_password(password, ttl, max_access_count)
    base_url = set_base_url(request)
    link = base_url + quote_plus(token)
    
    # Return JSON if explicitly requested via Accept header or if it's an AJAX request
    wants_json = (
        request.accept_mimetypes.accept_json and 
        request.accept_mimetypes.best_match(['application/json', 'text/html']) == 'application/json'
    ) or request.headers.get('Accept', '').startswith('application/json')
    
    if wants_json:
        return jsonify(link=link, ttl=ttl, max_access_count=max_access_count)
    else:
        return render_template('confirm.html', password_link=link)


@app.route('/api/set_password/', methods=['POST'])
def api_handle_password():
    password = request.json.get('password')
    ttl = int(request.json.get('ttl', DEFAULT_API_TTL))
    max_access_count = int(request.json.get('max_access_count', 1))
    
    if password and isinstance(ttl, int) and ttl <= MAX_TTL and isinstance(max_access_count, int) and max_access_count > 0:
        token = set_password(password, ttl, max_access_count)
        base_url = set_base_url(request)
        link = base_url + quote_plus(token)
        return jsonify(link=link, ttl=ttl, max_access_count=max_access_count)
    else:
        abort(500)


@app.route('/api/v2/passwords', methods=['POST'])
def api_v2_set_password():
    password = request.json.get('password')
    ttl = int(request.json.get('ttl', DEFAULT_API_TTL))

    invalid_params = []

    if not password:
        invalid_params.append({
            "name": "password",
            "reason": "The password is required and should not be null or empty."
        })

    if not isinstance(ttl, int) or ttl > MAX_TTL:
        invalid_params.append({
            "name": "ttl",
            "reason": "The specified TTL is longer than the maximum supported."
        })

    if len(invalid_params) > 0:
        # Return a ProblemDetails expliciting issue with Password and/or TTL
        return as_validation_problem(
            request,
            "set-password-validation-error",
            "The password and/or the TTL are invalid.",
            invalid_params
        )

    token = set_password(password, ttl)
    url_token = quote_plus(token)
    base_url = set_base_url(request)
    api_link = urljoin(base_url, request.path + "/" + url_token)
    web_link = urljoin(base_url, url_token)
    response_content = {
        "token": token,
        "links": [{
            "rel": "self",
            "href": api_link
        }, {
            "rel": "web-view",
            "href": web_link
        }],
        "ttl": ttl
    }
    return jsonify(response_content)


@app.route('/api/v2/passwords/<token>', methods=['HEAD'])
def api_v2_check_password(token):
    token = unquote_plus(token)
    if not password_exists(token):
        # Return NotFound, to indicate that password does not exists (anymore or at all)
        return ('', 404)
    else:
        # Return OK, to indicate that password still exists
        return ('', 200)


@app.route('/api/v2/passwords/<token>', methods=['GET'])
def api_v2_retrieve_password(token):
    token = unquote_plus(token)
    password = get_password(token)
    if not password:
        # Return NotFound, to indicate that password does not exists (anymore or at all)
        return as_not_found_problem(
            request,
            "get-password-error",
            "The password doesn't exist.",
            [{"name": "token"}]
        )
    else:
        # Return OK and the password in JSON message
        return jsonify(password=password)


@app.route('/<password_key>', methods=['GET'])
def preview_password(password_key):
    password_key = unquote_plus(password_key)
    if not password_exists(password_key):
        return render_template('expired.html'), 404

    return render_template('preview.html')


@app.route('/<password_key>', methods=['POST'])
def show_password(password_key):
    password_key = unquote_plus(password_key)
    password = get_password(password_key)
    if not password:
        return render_template('expired.html'), 404

    return render_template('password.html', password=password)


@app.route('/_/_/health', methods=['GET'])
@check_redis_alive
def health_check():
    return {}


@app.route('/.well-known/appspecific/com.chrome.devtools.json', methods=['GET'])
def chrome_devtools_well_known():
    """Respond to Chrome DevTools probe to avoid 404 in logs."""
    return '', 204

# Allowed file types: any (no extension whitelist). Common image/document types all work.
# Examples: png, jpg, jpeg, gif, webp, svg, pdf, txt, zip, etc.
def allowed_file(filename):
    return filename and filename.strip() != ''

def get_unique_filename(original_filename):
    """Generate a unique filename to avoid collisions."""
    if not original_filename:
        return f"{uuid.uuid4().hex}"
    
    # Get file extension
    if '.' in original_filename:
        ext = '.' + original_filename.rsplit('.', 1)[1].lower()
    else:
        ext = ''
    
    # Generate unique filename: UUID + original extension
    unique_name = f"{uuid.uuid4().hex}{ext}"
    return unique_name

@app.route('/upload', methods=['POST'])
@check_redis_alive
def upload_file():
    """Handle file uploads with robust error handling and unique file storage."""
    try:
        # Validate file input (accessing request.files can raise 413 if body too large)
        if 'file' not in request.files:
            return jsonify(error="No file part in request"), 400

        files = request.files.getlist('file')
        if not files or all(f.filename == '' for f in files):
            return jsonify(error="No files selected"), 400

        # Validate and get TTL
        file_ttl_str = request.form.get('file_ttl', '').strip()
        if not file_ttl_str:
            return jsonify(error="TTL not specified"), 400
        
        file_ttl_str = file_ttl_str.lower()
        ttl_seconds = TIME_CONVERSION.get(file_ttl_str, DEFAULT_API_TTL)
        
        if ttl_seconds <= 0 or ttl_seconds > MAX_TTL:
            return jsonify(error=f"Invalid TTL value. Must be between 1 and {MAX_TTL} seconds."), 400

        file_max_access_count_str = request.form.get('file_max_access_count', '').strip()
        if not file_max_access_count_str or not file_max_access_count_str.isdigit() or int(file_max_access_count_str) < 1:
            return jsonify(error="Access count must be a positive integer"), 400
        file_max_access_count = int(file_max_access_count_str)

        # Filter out empty files
        valid_files = [f for f in files if f.filename and f.filename.strip()]
        if not valid_files:
            return jsonify(error="No valid files to upload"), 400

        # Generate unique file key
        file_key = f"file:{uuid.uuid4().hex}"
        
        if len(valid_files) == 1:
            # Single file upload
            file = valid_files[0]
            
            if not allowed_file(file.filename):
                return jsonify(error=f"Invalid file type: {file.filename}"), 400

            # Generate unique filename
            original_filename = secure_filename(file.filename)
            unique_filename = get_unique_filename(original_filename)
            file_path = os.path.join(UPLOAD_FOLDER, unique_filename)
            
            try:
                # Save file
                file.save(file_path)
                
                # Verify file was saved
                if not os.path.exists(file_path):
                    app.logger.error(f"File not found after save: {file_path}")
                    return jsonify(error="Failed to save file: file not found after write. Check server disk and permissions."), 500
                if os.path.getsize(file_path) == 0:
                    try:
                        os.remove(file_path)
                    except OSError:
                        pass
                    app.logger.error(f"File saved as 0 bytes: {file_path}")
                    return jsonify(error="Failed to save file: file is empty. Try again or use a different file."), 500
                
                # Store metadata in Redis
                redis_client.hset(file_key, mapping={
                    "path": file_path,
                    "filename": original_filename,
                    "unique_filename": unique_filename,
                    "access_count": file_max_access_count
                })
                redis_client.expire(file_key, ttl_seconds)
                
                # Schedule cleanup (only after Redis entry expires)
                schedule_file_deletion(file_path, file_key, ttl_seconds)
                
                # Generate download link
                download_link = f"{set_base_url(request)}uploads/{quote_plus(file_key)}"
                return jsonify(download_link=download_link, ttl=ttl_seconds, max_access_count=file_max_access_count)
                
            except OSError as e:
                # Clean up on error (permission, disk full, etc.)
                if os.path.exists(file_path):
                    try:
                        os.remove(file_path)
                    except OSError:
                        pass
                app.logger.error(f"Error saving file to {file_path}: {e}")
                return jsonify(error=f"Failed to save file: {e.strerror or str(e)}"), 500
            except Exception as e:
                if os.path.exists(file_path):
                    try:
                        os.remove(file_path)
                    except OSError:
                        pass
                app.logger.error(f"Error saving file: {e}")
                return jsonify(error=f"Failed to save file: {str(e)}"), 500

        else:
            # Multiple files - create zip
            zip_unique_name = f"{uuid.uuid4().hex}.zip"
            zip_path = os.path.join(UPLOAD_FOLDER, zip_unique_name)
            temp_files = []  # Track temp files for cleanup
            
            try:
                with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
                    for file in valid_files:
                        if not allowed_file(file.filename):
                            raise ValueError(f"Invalid file type: {file.filename}")
                        
                        original_filename = secure_filename(file.filename)
                        unique_filename = get_unique_filename(original_filename)
                        temp_file_path = os.path.join(UPLOAD_FOLDER, unique_filename)
                        
                        # Save file temporarily
                        file.save(temp_file_path)
                        temp_files.append(temp_file_path)
                        
                        # Verify file was saved
                        if not os.path.exists(temp_file_path) or os.path.getsize(temp_file_path) == 0:
                            raise ValueError(f"Failed to save file: {original_filename}")
                        
                        # Add to zip
                        zipf.write(temp_file_path, arcname=original_filename)
                
                # Verify zip was created
                if not os.path.exists(zip_path) or os.path.getsize(zip_path) == 0:
                    raise ValueError("Failed to create zip file")
                
                # Store zip metadata in Redis
                redis_client.hset(file_key, mapping={
                    "path": zip_path,
                    "filename": "snappass_files.zip",
                    "unique_filename": zip_unique_name,
                    "is_zip": "true",
                    "access_count": file_max_access_count
                })
                redis_client.expire(file_key, ttl_seconds)
                
                # Schedule cleanup
                schedule_file_deletion(zip_path, file_key, ttl_seconds)
                
                # Clean up temp files
                for temp_file in temp_files:
                    try:
                        if os.path.exists(temp_file):
                            os.remove(temp_file)
                    except Exception as e:
                        app.logger.warning(f"Failed to remove temp file {temp_file}: {e}")
                
                # Generate download link
                download_link = f"{set_base_url(request)}uploads/{quote_plus(file_key)}"
                return jsonify(download_link=download_link, ttl=ttl_seconds, max_access_count=file_max_access_count)
                
            except Exception as e:
                # Clean up on error
                for temp_file in temp_files:
                    try:
                        if os.path.exists(temp_file):
                            os.remove(temp_file)
                    except:
                        pass
                if os.path.exists(zip_path):
                    try:
                        os.remove(zip_path)
                    except:
                        pass
                app.logger.error(f"Error creating zip: {e}")
                return jsonify(error=f"Failed to process files: {str(e)}"), 500

    except RequestEntityTooLarge:
        max_mb = app.config['MAX_CONTENT_LENGTH'] // (1024 * 1024)
        return jsonify(error=f"File too large. Maximum size is {max_mb} MB."), 413
    except BadRequest as e:
        app.logger.error(f"Bad request in upload_file: {e}")
        return jsonify(
            error="Invalid request. Use multipart/form-data with 'file', 'file_ttl', and 'file_max_access_count' fields."
        ), 400
    except Exception as e:
        app.logger.error(f"Unexpected error in upload_file: {e}")
        return jsonify(error=f"An unexpected error occurred: {str(e)}"), 500

def schedule_file_deletion(file_path, file_key, ttl_seconds):
    """Schedule the deletion of a file after the TTL expires and Redis entry is gone."""
    def delete_file():
        try:
            # Check if Redis entry still exists (might have been deleted on download)
            if redis_client.exists(file_key):
                # Redis entry still exists, don't delete yet
                return
            
            # Redis entry is gone, safe to delete file
            if os.path.exists(file_path):
                os.remove(file_path)
                app.logger.info(f"File {file_path} deleted after TTL expiration.")
        except Exception as e:
            app.logger.error(f"Error deleting file {file_path}: {e}")

    # Schedule the file deletion using a thread
    timer = threading.Timer(ttl_seconds, delete_file)
    timer.daemon = True  # Allow thread to exit when main program exits
    timer.start()

def _parse_file_access_count(file_metadata):
    """Read remaining access count from Redis hash (default 1 for legacy entries)."""
    raw = file_metadata.get(b"access_count")
    if raw is None:
        return 1
    if isinstance(raw, bytes):
        raw = raw.decode('utf-8')
    try:
        return int(raw)
    except (TypeError, ValueError):
        return 1


def _get_file_metadata(file_key):
    """Fetch and validate file metadata from Redis. Returns (file_path, filename, access_count) or (None, error_response)."""
    file_key = unquote_plus(file_key)
    if not file_key.startswith('file:'):
        return None, (jsonify(error="Invalid file key format"), 400)
    file_metadata = redis_client.hgetall(file_key)
    if not file_metadata:
        return None, (jsonify(error="File not found or has expired"), 404)
    access_count = _parse_file_access_count(file_metadata)
    if access_count <= 0:
        return None, (jsonify(error="File not found or has expired"), 404)
    try:
        file_path = file_metadata.get(b"path")
        filename = file_metadata.get(b"filename")
        if not file_path or not filename:
            return None, (jsonify(error="Invalid file metadata"), 500)
        file_path = file_path.decode('utf-8')
        filename = filename.decode('utf-8')
    except (AttributeError, UnicodeDecodeError) as e:
        app.logger.error(f"Error decoding file metadata: {e}")
        return None, (jsonify(error="Invalid file metadata format"), 500)
    if not os.path.exists(file_path):
        try:
            redis_client.delete(file_key)
        except Exception:
            pass
        return None, (jsonify(error="File not found on disk"), 404)
    if not os.access(file_path, os.R_OK):
        return None, (jsonify(error="File is not accessible"), 403)
    return (file_path, filename, access_count), None


@app.route('/uploads/<file_key>', methods=['GET'])
@check_redis_alive
def download_file(file_key):
    """Preview: show page with Download button. Download: serve file and delete only when ?download=true."""
    try:
        result, err = _get_file_metadata(file_key)
        if err is not None:
            return err
        file_path, filename, access_count = result
        file_key_decoded = unquote_plus(file_key)

        # Explicit download trigger: serve file and consume one access
        if request.args.get('download') == 'true':
            try:
                response = send_file(
                    file_path,
                    as_attachment=True,
                    download_name=filename,
                    mimetype="application/octet-stream"
                )
                response.direct_passthrough = False

                if access_count > 1:
                    redis_client.hset(file_key_decoded, "access_count", access_count - 1)
                else:
                    try:
                        redis_client.delete(file_key_decoded)
                    except Exception as e:
                        app.logger.warning(f"Failed to delete Redis key {file_key_decoded}: {e}")

                    def delete_after_download():
                        try:
                            if os.path.exists(file_path):
                                os.remove(file_path)
                                app.logger.info(f"File {file_path} deleted after download.")
                        except Exception as e:
                            app.logger.warning(f"Failed to delete file {file_path} after download: {e}")

                    timer = threading.Timer(5.0, delete_after_download)
                    timer.daemon = True
                    timer.start()

                return response
            except Exception as e:
                app.logger.error(f"Error serving file {file_key_decoded}: {e}")
                return jsonify(error="An error occurred while serving the file"), 500

        # No download param: show preview page (do not consume access)
        download_url = url_for(
            'download_file', file_key=file_key_decoded, download='true', _external=True
        )
        return render_template(
            'file_preview.html',
            filename=filename,
            download_url=download_url,
            access_count=access_count
        )

    except Exception as e:
        app.logger.error(f"Unexpected error in download_file: {e}")
        return jsonify(error="An unexpected error occurred"), 500

@check_redis_alive
def main():
    app.run(host=os.environ.get('SNAPPASS_BIND_ADDRESS', '0.0.0.0'),
            debug=True,
            port=os.environ.get('SNAPPASS_PORT', 5000))


if __name__ == '__main__':
    main()
