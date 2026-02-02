# Zenith Full App: Firebase Auth + MongoDB Atlas

## What’s added
1) **Firebase Authentication**
- Email/Password signup + login
- Google Sign-In (Popup)

2) **MongoDB Atlas storage**
- `users` collection: stores firebase uid, email, name, photoURL, providerId
- `course_states` collection: caches roadmap + videos so **re-access doesn’t recall APIs**
- `transcripts`, `quizzes`, `summaries` collections: cache transcript/quiz/summary per user & video
- `progress` collection: stores watch progress per user, per course, per videoUrl

3) **UI**
- Navbar shows **Hi, <user name>** on landing page and all pages

---

## Backend setup (Flask)
### 1) Install
```bash
cd final-sem-proj-main
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```

### 2) Create `.env` for backend
Add these:
```env
# Existing keys
YOUTUBE_API_KEY=...
GOOGLE_API_KEY=...
SUPADATA_KEY=...

# ✅ MongoDB Atlas
MONGODB_URI="mongodb+srv://<user>:<pass>@<cluster>.mongodb.net/?retryWrites=true&w=majority"
MONGODB_DB="zenith"

# ✅ Firebase Admin (server-side verification)
FIREBASE_SERVICE_ACCOUNT_PATH="/absolute/path/to/firebase-service-account.json"
# OR:
# FIREBASE_SERVICE_ACCOUNT_JSON='{"type":"service_account", ... }'
```

### 3) Run backend
```bash
python3 server.py
```

---

## Firebase setup (Frontend)
### 1) Create Firebase project
- Enable **Authentication**
- Enable providers:
  - Email/Password
  - Google

### 2) Create `.env` for Vite frontend (in project root)
```env
VITE_API_BASE="http://127.0.0.1:5000"
VITE_FIREBASE_API_KEY="..."
VITE_FIREBASE_AUTH_DOMAIN="..."
VITE_FIREBASE_PROJECT_ID="..."
VITE_FIREBASE_STORAGE_BUCKET="..."
VITE_FIREBASE_MESSAGING_SENDER_ID="..."
VITE_FIREBASE_APP_ID="..."
```

### 3) Run frontend
```bash
npm install
npm run dev
```

---

## How caching/progress works
### A) User credentials
- When user logs in (Email/Password or Google), frontend gets Firebase **ID token**
- Backend verifies token via **firebase-admin**
- Backend **upserts** the user into MongoDB (`users`)

### B) Course re-access without recalling APIs
- When you submit the course form:
  - App first calls `/course/state/get`
  - If found, it uses cached `roadmap + videos`
  - Else it calls `/generate-roadmap` and then saves to Mongo via `/course/state/save`

### C) Transcript/Quiz/Summary caching
- `/get-transcript`, `/generate-mcq`, `/summarize` now check Mongo first.
- If cached, backend returns cached results (no external API calls).

### D) Watch progress persistence
- Video page syncs progress every ~5 seconds per video to:
  - `POST /progress/upsert`
- On course open, it loads:
  - `GET /progress/get`
  and merges into localStorage so the UI resumes correctly.

---

## MongoDB collections
- `users`
- `course_states`
- `transcripts`
- `quizzes`
- `summaries`
- `progress`

---

## Notes
- If backend isn’t running, UI still loads, but caching/sync will not work (console warning).
- For production: secure CORS, use HTTPS, and store secrets in hosting environment variables.
