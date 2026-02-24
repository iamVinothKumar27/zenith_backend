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


## Mock Test (Gemini + Judge0) Configuration

### 1) Gemini
Set your Gemini key (same as other Zenith AI features):
- `GEMINI_API_KEY=...`

### 2) Judge0 (Code Execution)
This project supports **Java, C, C++, Python** for coding mock tests via Judge0.

Set one of the following:

#### Option A: RapidAPI (Judge0 CE proxy)
- `JUDGE0_BASE_URL=https://judge0-ce.p.rapidapi.com`
- `JUDGE0_RAPIDAPI_KEY=YOUR_RAPIDAPI_KEY`
- `JUDGE0_RAPIDAPI_HOST=judge0-ce.p.rapidapi.com`

#### Option B: Self-hosted Judge0 (recommended for scale)
- `JUDGE0_BASE_URL=http://YOUR_JUDGE0_HOST:2358`
- (No RapidAPI headers required)

> Note: Language IDs can vary by Judge0 deployment. If your instance uses different language IDs, update `_JUDGE0_LANG_IDS` in `server.py`.

### 3) Endpoints
- `POST /mocktest/session/create` → generate a test based on pattern (general/tech/coding)
- `GET /mocktest/sessions` → history list
- `GET /mocktest/sessions/<id>` → load a session
- `POST /mocktest/sessions/<id>/submit` → score + Gemini strengths/weakness analysis
- `DELETE /mocktest/sessions/<id>` → delete from history

---

## ✅ Fix: Mock Test Coding (Piston) – local Docker setup

### Why you are seeing 401
- Your backend was calling the **public** Piston endpoint (`emkc.org`). As of **Feb 15, 2026**, the public API requires authorization. citeturn3view0
- So the safe solution is: **self-host Piston** (Docker) and point Zenith to it.

### 1) Install runtimes inside your Piston container (your `runtimes` is empty = `[]`)
By default, the container starts with **no language packages installed**. citeturn3view0turn2view0

Run these (choose what you need):

```bash
# See what packages are available
curl -s http://localhost:2000/api/v2/packages | head

# Install Python
curl -s -X POST http://localhost:2000/api/v2/packages \
  -H 'Content-Type: application/json' \
  -d '{"language":"python","version":"3.x"}'

# Install C++ (use "cpp")
curl -s -X POST http://localhost:2000/api/v2/packages \
  -H 'Content-Type: application/json' \
  -d '{"language":"cpp","version":"*"}'

# Install Java
curl -s -X POST http://localhost:2000/api/v2/packages \
  -H 'Content-Type: application/json' \
  -d '{"language":"java","version":"*"}'

# After install, runtimes should NOT be empty
curl -s http://localhost:2000/api/v2/runtimes | head
```

### 2) Point Zenith backend to your self-hosted Piston
In your backend `.env` add:

```env
# Self-hosted piston (local)
PISTON_BASE_URL=http://127.0.0.1:2000/api/v2

# Optional: only if you use a hosted/public piston that needs auth
# PISTON_AUTH=Bearer <token>
```

### 3) If backend runs on Render/VPS (not on your laptop)
Your Render backend **cannot** reach `localhost:2000` on your laptop.
You must host Piston somewhere reachable:
- Same VPS as backend (best)
- A separate service and set `PISTON_BASE_URL=https://<your-piston-domain>/api/v2`

(If you want, I can give a Render + Docker deployment plan for Piston too.)

