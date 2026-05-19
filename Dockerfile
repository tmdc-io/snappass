# ---------- Build stage ----------
FROM dhi.io/python:3-alpine3.23-dev AS build

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PYTHONPATH=/app

WORKDIR /build

COPY setup.py requirements.txt MANIFEST.in README.rst AUTHORS.rst ./
COPY snappass ./snappass

# Install deps into /app
RUN pip install --no-cache-dir -r requirements.txt --target /app

# Compile translations
RUN python -m babel.messages.frontend compile -d snappass/translations

# Install the application itself
RUN pip install --no-cache-dir . --target /app


# ---------- Runtime stage ----------
FROM dhi.io/python:3-alpine3.23

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PYTHONPATH=/app

WORKDIR /app

# Copy installed app + deps
COPY --from=build /app /app

# Run as non-root (DHI default UID-safe)
USER 1000

# Default Flask port
EXPOSE 5000

CMD ["python", "-m", "snappass.main"]