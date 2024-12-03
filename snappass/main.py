import os
import sys
import uuid
import tempfile
import zipfile
from io import BytesIO
import threading
import time

import redis

from cryptography.fernet import Fernet
from flask import abort, Flask, render_template, request, jsonify, make_response, send_from_directory, redirect, send_file
from redis.exceptions import ConnectionError
from urllib.parse import quote_plus
from urllib.parse import unquote_plus
from urllib.parse import urljoin
from distutils.util import strtobool
# _ is required to get the Jinja templates translated
from flask_babel import Babel, _  # noqa: F401
from werkzeug.utils import secure_filename
from flask_cors import CORS

NO_SSL = bool(strtobool(os.environ.get('NO_SSL', 'False')))
URL_PREFIX = os.environ.get('URL_PREFIX', None)
HOST_OVERRIDE = os.environ.get('HOST_OVERRIDE', None)
TOKEN_SEPARATOR = '~'

os.environ['TMPDIR'] = '/tmp/uploads'
tempfile.tempdir = '/tmp/uploads'

# Define a folder where uploaded files will be stored
UPLOAD_FOLDER = os.path.join(os.getcwd(), '/tmp/uploads')
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

# Initialize Flask Application
app = Flask(__name__)
CORS(app)  # Enable CORS, required for frontend requests
if os.environ.get('DEBUG'):
    app.debug = True
app.secret_key = os.environ.get('SECRET_KEY', 'Secret Key')
app.config.update(
    dict(STATIC_URL=os.environ.get('STATIC_URL', 'static')))
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024  # 100 MB limit


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
    redis_client.hmset(storage_key, {
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
    
    if request.accept_mimetypes.accept_json and not request.accept_mimetypes.accept_html:
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

# Set the allowed file types
# ALLOWED_EXTENSIONS = {'txt', 'pdf', 'png', 'jpg', 'jpeg', 'gif'}

# Function to check allowed file types
def allowed_file(filename):
    # return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS
    return '.' in filename and filename.rsplit('.', 1)[1].lower()

@app.route('/upload', methods=['POST'])
def upload_file():

    # app.logger.debug(f"Form data: {request.form}")

    if 'file' not in request.files:
        return jsonify(error="No file part"), 400

    files = request.files.getlist('file')  # Get list of uploaded files
    file_ttl_str = request.form['file_ttl'].lower()

    # Convert TTL string to seconds using TIME_CONVERSION dictionary
    ttl_seconds = TIME_CONVERSION.get(file_ttl_str, DEFAULT_API_TTL)

    if ttl_seconds <= 0 or ttl_seconds > MAX_TTL:
        return jsonify(error=f"Invalid TTL value. Must be between 1 and {MAX_TTL} seconds."), 400

    if not files:
        return jsonify(error="No selected files"), 400

    if len(files) == 1:
        # Single file upload logic
        file = files[0]
        if file.filename == '':
            return jsonify(error="No selected file"), 400

        if file and allowed_file(file.filename):
            filename = secure_filename(file.filename)
            file_path = os.path.join(UPLOAD_FOLDER, filename)
            file.save(file_path)

            # Generate a unique key for this file
            file_key = f"file:{uuid.uuid4().hex}"
            
            # Store file metadata in Redis hash with TTL
            redis_client.hmset(file_key, {
                "path": file_path,
                "filename": filename
            })
            redis_client.expire(file_key, ttl_seconds)  # Use ttl_seconds from the form

            # Schedule file deletion
            schedule_file_deletion(file_path, ttl_seconds)

            # Generate a download link for the uploaded file
            download_link = f"{set_base_url(request)}uploads/{file_key}"
            return jsonify(download_link=download_link, ttl=ttl_seconds)
        else:
            return jsonify(error=f"Invalid file type: {file.filename}"), 400

    else:
        # Multiple file upload logic
        zip_filename = "snappass_files.zip"
        zip_path = os.path.join(UPLOAD_FOLDER, zip_filename)

        # Create a zip file
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for file in files:
                if file.filename == '':
                    continue  # Skip files with no name

                if file and allowed_file(file.filename):
                    filename = secure_filename(file.filename)
                    file_path = os.path.join(UPLOAD_FOLDER, filename)
                    file.save(file_path)

                    # Add file to zip archive
                    zipf.write(file_path, arcname=filename)

                    # Optionally, remove the saved file after adding it to the zip
                    os.remove(file_path)
                else:
                    return jsonify(error=f"Invalid file type: {file.filename}"), 400

        # Store the zip file metadata in Redis hash with TTL
        zip_file_key = f"file:{uuid.uuid4().hex}"
        redis_client.hmset(zip_file_key, {
            "path": zip_path,
            "filename": zip_filename
        })
        redis_client.expire(zip_file_key, ttl_seconds)  # Use ttl_seconds from the form

        # Schedule zip file deletion
        schedule_file_deletion(zip_path, ttl_seconds)

        # Generate a download link for the zip file
        download_link = f"{set_base_url(request)}uploads/{zip_file_key}"

        return jsonify(download_link=download_link, ttl=ttl_seconds)

def schedule_file_deletion(file_path, ttl_seconds):
    """Schedule the deletion of a file after the TTL expires."""
    def delete_file():
        try:
            if os.path.exists(file_path):
                os.remove(file_path)
                print(f"File {file_path} deleted after TTL.")
        except Exception as e:
            print(f"Error deleting file {file_path}: {e}")

    # Schedule the file deletion using a thread
    timer = threading.Timer(ttl_seconds, delete_file)
    timer.start()

@app.route('/uploads/<file_key>', methods=['GET'])
def download_file(file_key):
    # Retrieve file metadata from Redis using the provided file_key
    file_metadata = redis_client.hgetall(file_key)
    
    if not file_metadata:
        return jsonify(error="File not found or has expired"), 404

    # Decode metadata
    file_path = file_metadata.get(b"path").decode('utf-8')
    filename = file_metadata.get(b"filename").decode('utf-8')

    # Verify file existence
    if not os.path.exists(file_path):
        return jsonify(error="File not found"), 404

    try:
        # Serve the file with attachment and a proper filename
        response = send_file(
            file_path, 
            as_attachment=True, 
            download_name=filename,  # Sets the download filename
            mimetype="application/octet-stream"  # Default mimetype for binary files
        )
        response.direct_passthrough = False  # Ensure file is fully served before deletion

        # Clean up the file after serving
        os.remove(file_path)
        return response
    except Exception as e:
        app.logger.error(f"Error serving file {file_key}: {e}")
        return jsonify(error="An error occurred while serving the file"), 500

@check_redis_alive
def main():
    app.run(host=os.environ.get('SNAPPASS_BIND_ADDRESS', '0.0.0.0'),
            debug=True,
            port=os.environ.get('SNAPPASS_PORT', 5000))


if __name__ == '__main__':
    main()
