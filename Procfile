web: gunicorn server:app --bind 0.0.0.0:$PORT --workers 1 --threads 2 --timeout 180 --keep-alive 5 --max-requests 800 --max-requests-jitter 100
