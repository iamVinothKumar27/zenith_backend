# server.py
from flask import Flask, jsonify, request, send_from_directory
from flask_cors import CORS
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
from supadata import Supadata

from PyPDF2 import PdfReader

from dotenv import load_dotenv
import google.generativeai as genai

import os, json, re
import time
import uuid
import math

import hashlib
from datetime import datetime, timezone

from werkzeug.utils import secure_filename

from flask import g
from pymongo import MongoClient
import gridfs
from bson.objectid import ObjectId
import firebase_admin
from firebase_admin import credentials as fb_credentials
from firebase_admin import auth as fb_auth
load_dotenv()  
# ----------------- MONGODB + FIREBASE AUTH -----------------
MONGODB_URI = os.getenv("MONGODB_URI", "")
MONGODB_DB = os.getenv("MONGODB_DB", "zenith")
_mongo_client = None

def get_db():
    global _mongo_client
    if not MONGODB_URI:
        raise RuntimeError("MONGODB_URI is not set")
    if _mongo_client is None:
        _mongo_client = MongoClient(MONGODB_URI, serverSelectionTimeoutMS=5000)
    return _mongo_client[MONGODB_DB]

def _init_firebase_admin():
    if firebase_admin._apps:
        return
    # Option A: Path to service account json
    sa_path = os.getenv("FIREBASE_SERVICE_ACCOUNT_PATH", "").strip()
    sa_json = os.getenv("FIREBASE_SERVICE_ACCOUNT_JSON", "").strip()
    if sa_path:
        cred = fb_credentials.Certificate(sa_path)
        firebase_admin.initialize_app(cred)
        return
    if sa_json:
        cred = fb_credentials.Certificate(json.loads(sa_json))
        firebase_admin.initialize_app(cred)
        return
    raise RuntimeError("Firebase Admin is not configured. Set FIREBASE_SERVICE_ACCOUNT_PATH or FIREBASE_SERVICE_ACCOUNT_JSON")

def require_user():
    """Verify Firebase ID token from Authorization: Bearer <token>."""
    auth_header = request.headers.get("Authorization", "")
    if not auth_header.startswith("Bearer "):
        return None, ("Missing Authorization Bearer token", 401)
    token = auth_header.split(" ", 1)[1].strip()
    try:
        _init_firebase_admin()
        decoded = fb_auth.verify_id_token(token)
        g.user = decoded
        return decoded, None
    except Exception as e:
        return None, (f"Invalid token: {e}", 401)


def require_admin():
    """Verify token + check the user's role in MongoDB."""
    user, err = require_user()
    if err:
        return None, err

    try:
        db = get_db()
        doc = db.users.find_one({"uid": user.get("uid")}, projection={"_id": 0, "role": 1})
        role = (doc or {}).get("role") or "user"
        if role != "admin":
            return None, ("Admin access required", 403)
        return user, None
    except Exception as e:
        return None, (f"Admin check failed: {e}", 500)


# ----------------- COURSE HOLD (ADMIN CONTROL) -----------------
def is_course_held(uid: str, course_title: str) -> bool:
    """Return True if the given course is on hold for the user."""
    if not uid or not course_title:
        return False
    try:
        db = get_db()
        doc = db.course_holds.find_one({"uid": uid, "courseTitle": course_title}, projection={"_id": 0, "held": 1})
        return bool((doc or {}).get("held"))
    except Exception:
        return False


def block_if_held(uid: str, course_title: str):
    """Return (response, status_code) on block, else None."""
    if is_course_held(uid, course_title):
        return (jsonify({"error": "This course is currently on hold by admin."}), 403)
    return None


def derive_course_title_from_video(uid: str, video_url: str):
    """Best-effort: find which course contains a given video_url for the user."""
    if not uid or not video_url:
        return None
    db = get_db()
    # Only project the minimum fields.
    states = db.course_states.find({"uid": uid}, projection={"_id": 0, "courseTitle": 1, "videos": 1})

    def iter_urls(obj):
        if obj is None:
            return
        if isinstance(obj, list):
            for it in obj:
                yield from iter_urls(it)
        elif isinstance(obj, dict):
            # week wrapper
            if isinstance(obj.get("videos"), list):
                for v in obj.get("videos"):
                    yield from iter_urls(v)
                return
            # single video
            if isinstance(obj.get("video"), str):
                yield obj.get("video")
                return
            # build_weekly_json shape
            for _, v in obj.items():
                yield from iter_urls(v)

    for st in states:
        vids = st.get("videos")
        for u in iter_urls(vids):
            if u == video_url:
                return st.get("courseTitle")
    return None

def formdata_hash(obj) -> str:
    try:
        raw = json.dumps(obj or {}, sort_keys=True, ensure_ascii=False).encode("utf-8")
    except Exception:
        raw = str(obj).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()



# ----------------- QUIZ STATE -----------------
QUIZ_STORE = {}       # quiz_id -> quiz(with answers)
QUIZ_ATTEMPTS = {}    # quiz_id -> attempts_count (0,1,2)
MAX_ATTEMPTS = None  # unlimited attempts until pass
PASS_PERCENT = 0.40  # 40% to pass         # pass score for quiz

# ✅ NEW: cache quiz per video_url
QUIZ_BY_VIDEO = {}    # video_url -> {quiz_id, questions_only, full_quiz}

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 10 * 1024 * 1024  # 10MB upload limit (PDF chat)

# ----------------- PROFILE PHOTO UPLOADS -----------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
PROFILE_UPLOAD_DIR = os.path.join(BASE_DIR, "uploads", "profile")
os.makedirs(PROFILE_UPLOAD_DIR, exist_ok=True)

ALLOWED_IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp"}


@app.route("/uploads/profile/<path:filename>")
def serve_profile_upload(filename):
    # Public endpoint to serve profile photos
    return send_from_directory(PROFILE_UPLOAD_DIR, filename)

ALLOWED_ORIGINS = [
    "https://zenith.vinothkumarts.in",
    "https://zenith-frontend-red.vercel.app",   # your vercel domain
    "http://localhost:5173",
    "http://127.0.0.1:5173",
    "https://www.zenithlearning.site"
]

from flask_cors import CORS

CORS(
  app,
  resources={r"/*": {"origins": ALLOWED_ORIGINS}},
  supports_credentials=True,
  allow_headers=["Content-Type", "Authorization"],
  methods=["GET","POST","DELETE","OPTIONS"]
)


# ----------------- AUTH: SYNC FIREBASE USER TO MONGODB -----------------
@app.route("/auth/firebase", methods=["POST"])
def auth_firebase():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    payload = request.get_json() or {}
    uid = payload.get("uid") or user.get("uid")
    email = payload.get("email") or user.get("email")
    name = payload.get("name") or user.get("name") or ""
    photoURL = payload.get("photoURL") or ""
    providerId = payload.get("providerId") or "firebase"

    if not uid:
        return jsonify({"error": "uid missing"}), 400

    db = get_db()
    now = datetime.now(timezone.utc)

    db.users.update_one(
        {"uid": uid},
        {"$set": {
            "uid": uid,
            "email": email,
            "name": name,
            "photoURL": photoURL,
            "providerId": providerId,
            "updatedAt": now,
        },
         # ✅ IMPORTANT:
         # We MUST NOT overwrite an existing role (e.g., you manually set role="admin" in Atlas).
         # So role is set ONLY on first insert.
         "$setOnInsert": {"createdAt": now, "role": "user"}},
        upsert=True
    )

    user_doc = db.users.find_one({"uid": uid}, {"_id": 0})
    return jsonify({"ok": True, "user": user_doc})


# ----------------- PROFILE (EXTRA FIELDS + LOCAL PHOTO) -----------------
@app.route("/profile/me", methods=["GET"])
def profile_me_get():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code
    db = get_db()
    doc = db.users.find_one({"uid": user["uid"]}, {"_id": 0})
    return jsonify({"ok": True, "user": doc or {}})


@app.route("/profile/me", methods=["POST"])
def profile_me_post():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    # Only allow these fields to be written from the client
    allowed = [
        "name",
        "dob",
        "education",
        "college",
        "degree",
        "department",
        "yearBatch",
        "year",
        "phone",
        "location",
        "bio",
        "photoURL",
        "photoLocalURL",
    ]
    update = {k: (data.get(k) or "") for k in allowed if k in data}
    # Normalize strings
    for k, v in list(update.items()):
        if isinstance(v, str):
            update[k] = v.strip()

    # Backward compatibility: accept `year` from client and also set `yearBatch`
    if update.get("year") and not update.get("yearBatch"):
        update["yearBatch"] = update["year"]

    # Keep empty strings out (optional) except name
    update["name"] = (update.get("name") or "").strip()
    now = datetime.now(timezone.utc)
    update["updatedAt"] = now

    db = get_db()
    db.users.update_one({"uid": user["uid"]}, {"$set": update}, upsert=True)
    doc = db.users.find_one({"uid": user["uid"]}, {"_id": 0})
    return jsonify({"ok": True, "user": doc})


def _remove_existing_avatar_files(uid: str):
    """Remove any existing avatar files for the user (uid.*)"""
    try:
        for fn in os.listdir(PROFILE_UPLOAD_DIR):
            if fn.startswith(f"{uid}."):
                try:
                    os.remove(os.path.join(PROFILE_UPLOAD_DIR, fn))
                except:
                    pass
    except:
        pass


def _profile_avatar_url(uid: str):
    host = (request.host_url or "").rstrip("/")
    return f"{host}/profile/photo/{uid}"


@app.route("/profile/photo/<uid>", methods=["GET"])
def profile_photo_get(uid):
    """Serve the user's avatar from MongoDB GridFS if available, else from local uploads."""
    db = get_db()
    fs = gridfs.GridFS(db)

    user_doc = db.users.find_one({"uid": uid}, {"_id": 0, "avatarFileId": 1}) or {}
    fid = user_doc.get("avatarFileId")
    if fid:
        try:
            gf = fs.get(ObjectId(fid))
            data = gf.read()
            ct = getattr(gf, "content_type", None) or getattr(gf, "contentType", None) or "application/octet-stream"
            return (data, 200, {"Content-Type": ct, "Cache-Control": "no-store"})
        except:
            pass

    # Fallback: try to serve local file uid.* if exists
    try:
        for fn in os.listdir(PROFILE_UPLOAD_DIR):
            if fn.startswith(f"{uid}."):
                return send_from_directory(PROFILE_UPLOAD_DIR, fn)
    except:
        pass

    return jsonify({"error": "photo not found"}), 404


@app.route("/profile/photo", methods=["POST"])
def profile_photo_upload():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    if "photo" not in request.files:
        return jsonify({"error": "photo file missing"}), 400

    f = request.files.get("photo")
    if not f or not f.filename:
        return jsonify({"error": "invalid photo"}), 400

    db = get_db()
    fs = gridfs.GridFS(db)
    uid = user["uid"]

    original = f.filename
    _, ext = os.path.splitext(original)
    ext = (ext or "").lower()
    if not ext:
        # Try to infer from mimetype
        mt = (f.mimetype or "").lower()
        if "jpeg" in mt or "jpg" in mt:
            ext = ".jpg"
        elif "png" in mt:
            ext = ".png"
        elif "webp" in mt:
            ext = ".webp"

    if ext not in ALLOWED_IMAGE_EXTS:
        return jsonify({"error": "Only JPG / PNG / WEBP allowed"}), 400

    # Replace existing avatar (GridFS) if present
    current = db.users.find_one({"uid": uid}, {"_id": 0, "avatarFileId": 1}) or {}
    old_fid = current.get("avatarFileId")
    if old_fid:
        try:
            fs.delete(ObjectId(old_fid))
        except:
            pass

    # Store in GridFS (more reliable on hosting than local disk)
    content_type = (f.mimetype or "").strip() or "application/octet-stream"
    file_id = fs.put(f.stream.read(), filename=f"avatar_{uid}{ext}", contentType=content_type)
    public_url = _profile_avatar_url(uid)

    # Also clean any old local file leftovers
    _remove_existing_avatar_files(uid)

    db.users.update_one(
        {"uid": uid},
        {"$set": {
            "avatarFileId": str(file_id),
            "photoLocalURL": public_url,
            "photoURL": "",
            "updatedAt": datetime.now(timezone.utc)
        }},
        upsert=True,
    )
    doc = db.users.find_one({"uid": user["uid"]}, {"_id": 0})
    return jsonify({"ok": True, "user": doc})


@app.route("/profile/photo", methods=["DELETE"])
def profile_photo_delete():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    uid = user["uid"]
    db = get_db()
    fs = gridfs.GridFS(db)

    # Delete from GridFS if present
    current = db.users.find_one({"uid": uid}, {"_id": 0, "avatarFileId": 1}) or {}
    old_fid = current.get("avatarFileId")
    if old_fid:
        try:
            fs.delete(ObjectId(old_fid))
        except:
            pass

    # Also remove any local leftovers
    _remove_existing_avatar_files(uid)

    db.users.update_one(
        {"uid": uid},
        {"$set": {"photoLocalURL": "", "photoURL": "", "avatarFileId": "", "updatedAt": datetime.now(timezone.utc)}},
        upsert=True,
    )
    doc = db.users.find_one({"uid": uid}, {"_id": 0})
    return jsonify({"ok": True, "user": doc})


# ----------------- COURSE STATE CACHE (ROADMAP + VIDEOS) -----------------
@app.route("/course/state/get", methods=["POST"])
def course_state_get():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    courseTitle = (data.get("courseTitle") or "").strip()

    # If "Other Domains" is used, resolve to actual subject if present
    if courseTitle.lower() in ["other domains", "other domain"] and isinstance(data.get("formData"), dict) and data.get("formData", {}).get("subject"):
        courseTitle = str(data.get("formData", {}).get("subject")).strip()
    formData = data.get("formData")

    if not courseTitle:
        return jsonify({"error": "courseTitle required"}), 400

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    db = get_db()
    q = {"uid": user["uid"], "courseTitle": courseTitle}
    if formData is not None:
        q["formHash"] = formdata_hash(formData)

    doc = db.course_states.find_one(q, sort=[("updatedAt", -1)], projection={"_id": 0})
    if not doc:
        # fallback: latest for the course (any formData)
        doc = db.course_states.find_one({"uid": user["uid"], "courseTitle": courseTitle}, sort=[("updatedAt", -1)], projection={"_id": 0})

    if not doc:
        return jsonify({"found": False}), 200

    return jsonify({"found": True, "state": doc})


@app.route("/course/state/save", methods=["POST"])
def course_state_save():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    courseTitle = (data.get("courseTitle") or "").strip()
    formData = data.get("formData") or {}
    # If user selected "Other Domains", store the actual subject as the course title
    if courseTitle.lower() in ["other domains", "other domain"] and isinstance(formData, dict) and formData.get("subject"):
        courseTitle = str(formData.get("subject")).strip()
    roadmap = data.get("roadmap")
    videos = data.get("videos")

    if not courseTitle or roadmap is None or videos is None:
        return jsonify({"error": "courseTitle, roadmap, videos required"}), 400

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    db = get_db()
    now = datetime.now(timezone.utc)
    h = formdata_hash(formData)

    db.course_states.update_one(
        {"uid": user["uid"], "courseTitle": courseTitle, "formHash": h},
        {"$set": {"uid": user["uid"], "courseTitle": courseTitle, "formHash": h, "formData": formData, "roadmap": roadmap, "videos": videos, "updatedAt": now},
         "$setOnInsert": {"createdAt": now}},
        upsert=True
    )

    return jsonify({"ok": True})


@app.route("/course/state/delete", methods=["POST"])
def course_state_delete():
    """User-initiated discontinue/remove course.

    Removes saved course state, progress, quiz progress, cached quizzes, and hold entries
    for the current user + course.
    """
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    payload = request.get_json() or {}
    course_title = (payload.get("courseTitle") or "").strip()
    if not course_title:
        return jsonify({"error": "courseTitle missing"}), 400

    uid = user.get("uid")
    db = get_db()

    # Main state
    db.course_states.delete_many({"uid": uid, "courseTitle": course_title})
    # Video watch progress
    db.progress.delete_many({"uid": uid, "courseTitle": course_title})
    # Quiz progress per video
    db.quiz_progress.delete_many({"uid": uid, "courseTitle": course_title})
    # Cached quizzes
    db.quizzes.delete_many({"uid": uid, "courseTitle": course_title})
    # Holds (if any)
    db.course_holds.delete_many({"uid": uid, "courseTitle": course_title})

    return jsonify({"ok": True})



@app.route("/courses/list", methods=["GET"])
def courses_list():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    db = get_db()

    states = list(db.course_states.find(
        {"uid": user["uid"]},
        projection={"_id": 0, "courseTitle": 1, "formData": 1, "videos": 1, "updatedAt": 1, "createdAt": 1}
    ))

    progress_docs = list(db.progress.find(
        {"uid": user["uid"]},
        projection={"_id": 0, "courseTitle": 1, "progressByVideo": 1, "updatedAt": 1}
    ))
    progress_by_course = {d.get("courseTitle"): d for d in progress_docs}

    # ✅ Course unlock / quiz state (passed/completed per video)
    course_progress_docs = list(db.course_progress.find(
        {"uid": user["uid"]},
        projection={"_id": 0, "courseTitle": 1, "quizPassedMap": 1, "quizCompletedMap": 1, "currentGlobalId": 1, "highestUnlockedId": 1, "updatedAt": 1}
    ))
    course_progress_by_course = {d.get("courseTitle"): d for d in course_progress_docs}

    items = []
    for st in states:
        title = st.get("courseTitle")
        videos = st.get("videos") or []
        # ✅ Robust total video counter
        # We support multiple shapes because different parts of the app store videos differently:
        # 1) [{"week": "Week 1", "videos": [..]}]
        # 2) [{"Week 1": [..]}, {"Week 2": [..]}]   (current build_weekly_json output)
        # 3) flat list of video dicts: [{"topic":..., "video":...}]
        def count_videos(obj):
            if obj is None:
                return 0
            # list/array
            if isinstance(obj, list):
                total_local = 0
                for it in obj:
                    total_local += count_videos(it)
                return total_local
            # dict/object
            if isinstance(obj, dict):
                # week wrapper with "videos" array
                if isinstance(obj.get("videos"), list):
                    return len(obj.get("videos"))
                # single video
                if "video" in obj and ("topic" in obj or "title" in obj):
                    return 1
                # build_weekly_json shape: {"Week 1": [..]}
                total_local = 0
                for _, v in obj.items():
                    if isinstance(v, list):
                        total_local += len(v)
                    elif isinstance(v, dict):
                        total_local += count_videos(v)
                return total_local
            return 0

        total = count_videos(videos)

        pd = progress_by_course.get(title) or {}
        pmap = pd.get("progressByVideo") or {}

        cp = course_progress_by_course.get(title) or {}
        qp_map = cp.get("quizPassedMap") or {}
        qc_map = cp.get("quizCompletedMap") or {}

        def _count_true(dct):
            if not isinstance(dct, dict):
                return 0
            return sum(1 for _, v in dct.items() if bool(v))

        passed_quizzes = _count_true(qp_map)
        completed_quizzes = _count_true(qc_map)

        completed = 0
        started = False
        best_resume = None  # (scoreTuple, url)
        for vurl, p in pmap.items():
            if not isinstance(p, dict):
                continue
            percent = float(p.get("percent") or 0)
            current = float(p.get("current") or 0)
            if percent > 0 or current > 0:
                started = True
            is_completed = bool(p.get("completed")) or percent >= 98
            if is_completed:
                completed += 1
            else:
                score = (percent, current)
                if best_resume is None or score > best_resume[0]:
                    best_resume = (score, vurl)

        # ✅ Status: Not Started / Doing / Completed
        # - Completed when all videos completed OR all quizzes passed
        # - Doing when ANY video progress exists OR any quiz completed/passed
        if total > 0 and (completed >= total or passed_quizzes >= total):
            status = "Completed"
        elif started or completed > 0 or passed_quizzes > 0 or completed_quizzes > 0:
            status = "Doing"
        else:
            status = "Not Started"

        held = is_course_held(user["uid"], title)

        items.append({
            "courseTitle": title,
            "displayTitle": (st.get("formData") or {}).get("subject") if (str(title).strip().lower() in ["other domains","other domain"]) else title,
            "totalVideos": total,
            "completedVideos": completed,
            "totalQuizzes": total,
            "passedQuizzes": passed_quizzes,
            "completedQuizzes": completed_quizzes,
            "resumeGlobalId": int(cp.get("currentGlobalId") or 1),
            "highestUnlockedId": int(cp.get("highestUnlockedId") or 1),
            "status": status,
            "held": held,
            "resumeVideoUrl": best_resume[1] if best_resume else None,
            "updatedAt": (st.get("updatedAt") or st.get("createdAt") or pd.get("updatedAt"))
        })

    def _ts(item):
        d = item.get("updatedAt")
        if not d:
            return 0
        try:
            return int(d.timestamp())
        except Exception:
            return 0

    items.sort(key=_ts, reverse=True)
    return jsonify({"items": items})


# ----------------- ADMIN: USERS OVERVIEW -----------------
@app.route("/admin/users", methods=["GET"])
def admin_users():
    _, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    db = get_db()

    def count_videos(obj):
        if obj is None:
            return 0
        if isinstance(obj, list):
            return sum(count_videos(it) for it in obj)
        if isinstance(obj, dict):
            if isinstance(obj.get("videos"), list):
                return len(obj.get("videos"))
            if "video" in obj and ("topic" in obj or "title" in obj):
                return 1
            total_local = 0
            for _, v in obj.items():
                if isinstance(v, list):
                    total_local += len(v)
                elif isinstance(v, dict):
                    total_local += count_videos(v)
            return total_local
        return 0

    def count_true(dct):
        if not isinstance(dct, dict):
            return 0
        return sum(1 for _, v in dct.items() if bool(v))

    users_out = []
    for u in db.users.find({}, projection={"_id": 0, "uid": 1, "email": 1, "name": 1, "role": 1}):
        uid = u.get("uid")
        role = u.get("role") or "user"

        # ✅ Requirement: do not show learning progress for admin accounts
        if role == "admin":
            users_out.append({
                "uid": uid,
                "email": u.get("email"),
                "name": u.get("name"),
                "role": role,
                "courses": [],
                "overallPercent": 0,
                "heldCourses": [],
            })
            continue

        states = list(db.course_states.find({"uid": uid}, projection={"_id": 0, "courseTitle": 1, "videos": 1}))
        holds = list(db.course_holds.find({"uid": uid, "held": True}, projection={"_id": 0, "courseTitle": 1}))
        held_set = set([h.get("courseTitle") for h in holds if h.get("courseTitle")])
        courses = []
        percents = []
        for st in states:
            title = st.get("courseTitle")
            total = count_videos(st.get("videos"))
            cp = db.course_progress.find_one({"uid": uid, "courseTitle": title}, projection={"_id": 0, "quizPassedMap": 1}) or {}
            passed = count_true(cp.get("quizPassedMap") or {})
            percent = 0
            if total > 0:
                percent = (passed / total) * 100
                percents.append(percent)
            courses.append({
                "courseKey": title,
                "courseTitle": title,
                "totalQuizzes": total,
                "passedQuizzes": passed,
                "percent": round(percent, 2),
                "held": title in held_set,
            })

        overall = round(sum(percents) / len(percents), 2) if percents else 0
        users_out.append({
            "uid": uid,
            "email": u.get("email"),
            "name": u.get("name"),
            "role": role,
            "courses": courses,
            "overallPercent": overall,
            "heldCourses": sorted(list(held_set)),
        })

    users_out.sort(key=lambda x: (x.get("role") != "admin", x.get("email") or ""))
    return jsonify({"ok": True, "users": users_out})


# ----------------- ADMIN: ROLE MANAGEMENT -----------------
@app.route("/admin/promote", methods=["POST"])
def admin_promote():
    """Promote a user to admin.

    Body: {"uid": "<firebase uid>"} OR {"email": "<email>"}
    """
    admin_user, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    target_uid = (data.get("uid") or "").strip()
    target_email = (data.get("email") or "").strip().lower()
    if not target_uid and not target_email:
        return jsonify({"error": "uid or email required"}), 400

    db = get_db()
    q = {"uid": target_uid} if target_uid else {"email": target_email}
    doc = db.users.find_one(q, projection={"_id": 0, "uid": 1, "email": 1, "role": 1})
    if not doc:
        return jsonify({"error": "User not found"}), 404

    db.users.update_one(q, {"$set": {"role": "admin", "updatedAt": datetime.now(timezone.utc)}})
    return jsonify({"ok": True, "uid": doc.get("uid"), "role": "admin"})


@app.route("/admin/demote", methods=["POST"])
def admin_demote():
    """Demote an admin back to user.

    Body: {"uid": "<firebase uid>"} OR {"email": "<email>"}
    Safety: an admin cannot demote themselves.
    """
    admin_user, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    target_uid = (data.get("uid") or "").strip()
    target_email = (data.get("email") or "").strip().lower()
    if not target_uid and not target_email:
        return jsonify({"error": "uid or email required"}), 400

    # Prevent self-demotion (avoids locking yourself out)
    if target_uid and admin_user.get("uid") == target_uid:
        return jsonify({"error": "You cannot demote your own account."}), 400
    if target_email and (admin_user.get("email") or "").lower() == target_email:
        return jsonify({"error": "You cannot demote your own account."}), 400

    db = get_db()
    q = {"uid": target_uid} if target_uid else {"email": target_email}
    doc = db.users.find_one(q, projection={"_id": 0, "uid": 1, "email": 1, "role": 1})
    if not doc:
        return jsonify({"error": "User not found"}), 404

    db.users.update_one(q, {"$set": {"role": "user", "updatedAt": datetime.now(timezone.utc)}})
    return jsonify({"ok": True, "uid": doc.get("uid"), "role": "user"})


# ----------------- ADMIN: DELETE USER -----------------
@app.route("/admin/delete-user", methods=["POST"])
def admin_delete_user():
    """Delete a user and all their learning data.

    Body: {"uid": "<firebase uid>"}
    Safety: admin cannot delete themselves.
    """
    admin_user, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    target_uid = (data.get("uid") or "").strip()
    if not target_uid:
        return jsonify({"error": "uid required"}), 400
    if admin_user.get("uid") == target_uid:
        return jsonify({"error": "You cannot delete your own account."}), 400

    db = get_db()
    db.users.delete_one({"uid": target_uid})
    db.course_states.delete_many({"uid": target_uid})
    db.course_progress.delete_many({"uid": target_uid})
    db.progress.delete_many({"uid": target_uid})
    db.quizzes.delete_many({"uid": target_uid})
    db.transcripts.delete_many({"uid": target_uid})
    db.summaries.delete_many({"uid": target_uid})
    db.course_holds.delete_many({"uid": target_uid})

    return jsonify({"ok": True, "uid": target_uid})


# ----------------- ADMIN: HOLD / UNHOLD COURSE FOR USER -----------------
@app.route("/admin/course-hold", methods=["POST"])
def admin_course_hold():
    """Hold/unhold a course for a specific user.

    Body: {"uid": "...", "courseTitle": "...", "held": true/false}
    """
    _, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    uid = (data.get("uid") or "").strip()
    courseTitle = (data.get("courseTitle") or "").strip()
    held = bool(data.get("held"))

    if not uid or not courseTitle:
        return jsonify({"error": "uid and courseTitle required"}), 400

    db = get_db()
    now = datetime.now(timezone.utc)
    db.course_holds.update_one(
        {"uid": uid, "courseTitle": courseTitle},
        {"$set": {"uid": uid, "courseTitle": courseTitle, "held": held, "updatedAt": now},
         "$setOnInsert": {"createdAt": now}},
        upsert=True,
    )
    return jsonify({"ok": True, "uid": uid, "courseTitle": courseTitle, "held": held})


# ----------------- ADMIN: ANALYTICS ENDPOINTS -----------------
@app.route("/admin/courses-studying", methods=["GET"])
def admin_courses_studying():
    """Aggregate: how many users are studying each course."""
    _, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    db = get_db()
    # course_states can include multiple formHash docs; group by uid+courseTitle
    pipeline = [
        {"$group": {"_id": {"uid": "$uid", "courseTitle": "$courseTitle"}}},
        {"$group": {"_id": "$_id.courseTitle", "users": {"$sum": 1}}},
        {"$sort": {"users": -1}},
    ]
    rows = list(db.course_states.aggregate(pipeline))

    holds = list(db.course_holds.find({"held": True}, projection={"_id": 0, "uid": 1, "courseTitle": 1}))
    hold_counts = {}
    for h in holds:
        ct = h.get("courseTitle")
        if not ct:
            continue
        hold_counts[ct] = hold_counts.get(ct, 0) + 1

    out = []
    for r in rows:
        ct = r.get("_id")
        out.append({
            "courseTitle": ct,
            "usersStudying": int(r.get("users") or 0),
            "usersOnHold": int(hold_counts.get(ct, 0)),
        })
    return jsonify({"ok": True, "courses": out})


@app.route("/admin/course-progress", methods=["GET"])
def admin_course_progress():
    """Detailed progress per user per course (quiz-passed/total).

    ✅ Requirement: course progress should be calculated from quiz progress.
    """
    _, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    db = get_db()

    # Map course -> total videos (derived from course_states by taking max)
    def count_videos(obj):
        if obj is None:
            return 0
        if isinstance(obj, list):
            return sum(count_videos(it) for it in obj)
        if isinstance(obj, dict):
            if isinstance(obj.get("videos"), list):
                return len(obj.get("videos"))
            if "video" in obj and ("topic" in obj or "title" in obj):
                return 1
            return sum(count_videos(v) for v in obj.values())
        return 0

    totals = {}
    for st in db.course_states.find({}, projection={"_id": 0, "courseTitle": 1, "videos": 1}):
        ct = st.get("courseTitle")
        if not ct:
            continue
        totals[ct] = max(totals.get(ct, 0), count_videos(st.get("videos")))

    def count_true(dct):
        if not isinstance(dct, dict):
            return 0
        return sum(1 for _, v in dct.items() if bool(v))

    users = {u["uid"]: u for u in db.users.find({}, projection={"_id": 0, "uid": 1, "email": 1, "name": 1, "role": 1})}

    # quiz progress is stored in course_progress collection
    rows = []
    for cp in db.course_progress.find({}, projection={"_id": 0, "uid": 1, "courseTitle": 1, "quizPassedMap": 1, "updatedAt": 1}):
        uid = cp.get("uid")
        ct = cp.get("courseTitle")
        u = users.get(uid) or {}
        role = (u.get("role") or "user")

        # ✅ Requirement: do not show progress rows for admins
        if role == "admin":
            continue

        total = int(totals.get(ct, 0))
        passed = count_true(cp.get("quizPassedMap") or {})
        pct = int(round((passed / total) * 100)) if total else 0

        rows.append({
            "uid": uid,
            "name": u.get("name"),
            "email": u.get("email"),
            "role": role,
            "courseTitle": ct,
            "totalQuizzes": total,
            "passedQuizzes": passed,
            "percent": pct,
            "held": is_course_held(uid, ct),
            "updatedAt": cp.get("updatedAt"),
        })

    rows.sort(key=lambda x: (x.get("held") is False, x.get("percent") or 0), reverse=True)
    return jsonify({"ok": True, "rows": rows})


@app.route("/admin/quiz-performance", methods=["GET"])
def admin_quiz_performance():
    """Aggregate quiz pass performance per course."""
    _, err = require_admin()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    db = get_db()

    # Total quizzes per course derived same as /courses/list (total videos)
    def count_videos(obj):
        if obj is None:
            return 0
        if isinstance(obj, list):
            return sum(count_videos(it) for it in obj)
        if isinstance(obj, dict):
            if isinstance(obj.get("videos"), list):
                return len(obj.get("videos"))
            if "video" in obj and ("topic" in obj or "title" in obj):
                return 1
            return sum(count_videos(v) for v in obj.values())
        return 0

    totals = {}
    for st in db.course_states.find({}, projection={"_id": 0, "courseTitle": 1, "videos": 1}):
        ct = st.get("courseTitle")
        if not ct:
            continue
        totals[ct] = max(totals.get(ct, 0), count_videos(st.get("videos")))

    # Sum passed counts across users
    def count_true(dct):
        if not isinstance(dct, dict):
            return 0
        return sum(1 for _, v in dct.items() if bool(v))

    agg = {}
    for cp in db.course_progress.find({}, projection={"_id": 0, "courseTitle": 1, "quizPassedMap": 1}):
        ct = cp.get("courseTitle")
        if not ct:
            continue
        agg[ct] = agg.get(ct, 0) + count_true(cp.get("quizPassedMap") or {})

    courses = []
    for ct, total in totals.items():
        passed_total = int(agg.get(ct, 0))
        # usersStudying: unique uid in course_states
        usersStudying = len(list(db.course_states.aggregate([
            {"$match": {"courseTitle": ct}},
            {"$group": {"_id": "$uid"}},
        ])))
        # Max possible passed = usersStudying * total
        denom = usersStudying * int(total)
        pass_rate = round((passed_total / denom) * 100, 2) if denom else 0
        courses.append({
            "courseTitle": ct,
            "totalQuizzesPerUser": int(total),
            "usersStudying": int(usersStudying),
            "passedQuizzesTotal": passed_total,
            "passRatePercent": pass_rate,
        })
    courses.sort(key=lambda x: x.get("passRatePercent") or 0, reverse=True)
    return jsonify({"ok": True, "courses": courses})

# ----------------- WATCH PROGRESS -----------------
@app.route("/progress/get", methods=["GET"])
def progress_get():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    courseTitle = (request.args.get("courseTitle") or "").strip()
    if not courseTitle:
        return jsonify({"error": "courseTitle required"}), 400

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    db = get_db()
    doc = db.progress.find_one({"uid": user["uid"], "courseTitle": courseTitle}, projection={"_id": 0})
    if not doc:
        return jsonify({"progressByVideo": {}})

    return jsonify({"progressByVideo": doc.get("progressByVideo", {})})


@app.route("/progress/upsert", methods=["POST"])
def progress_upsert():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    courseTitle = (data.get("courseTitle") or "").strip()
    videoUrl = (data.get("videoUrl") or "").strip()
    progress = data.get("progress") or {}

    if not courseTitle or not videoUrl:
        return jsonify({"error": "courseTitle and videoUrl required"}), 400

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    db = get_db()
    now = datetime.now(timezone.utc)

    db.progress.update_one(
        {"uid": user["uid"], "courseTitle": courseTitle},
        {"$set": {f"progressByVideo.{videoUrl}": progress, "updatedAt": now},
         "$setOnInsert": {"createdAt": now, "uid": user["uid"], "courseTitle": courseTitle}},
        upsert=True
    )

    return jsonify({"ok": True})


# ----------------- COURSE RESUME / QUIZ UNLOCK STATE -----------------
# Stores where the learner left off + which videos are unlocked/passed.
# This fixes:
# 1) If user exits and re-opens the course, it should resume.
# 2) Quiz/videos should remain unlocked across sessions/devices.

@app.route("/course/progress/get", methods=["POST"])
def course_progress_get():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    courseTitle = (data.get("courseTitle") or "").strip()
    if not courseTitle:
        return jsonify({"error": "courseTitle required"}), 400

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    db = get_db()
    doc = db.course_progress.find_one({"uid": user["uid"], "courseTitle": courseTitle}, projection={"_id": 0})
    if not doc:
        return jsonify({"found": False, "progress": None}), 200

    # Ensure required keys exist
    progress = {
        "currentGlobalId": int(doc.get("currentGlobalId") or 1),
        "highestUnlockedId": int(doc.get("highestUnlockedId") or 1),
        "quizPassedMap": doc.get("quizPassedMap") or {},
        "quizSubmittedMap": doc.get("quizSubmittedMap") or {},
        "quizCompletedMap": doc.get("quizCompletedMap") or {},
        "updatedAt": doc.get("updatedAt"),
    }
    return jsonify({"found": True, "progress": progress}), 200


@app.route("/course/progress/save", methods=["POST"])
def course_progress_save():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    courseTitle = (data.get("courseTitle") or "").strip()
    progress = data.get("progress") or {}

    if not courseTitle:
        return jsonify({"error": "courseTitle required"}), 400

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    blocked = block_if_held(user.get("uid"), courseTitle)
    if blocked:
        return blocked

    # sanitize
    def _obj(x):
        return x if isinstance(x, dict) else {}

    currentGlobalId = int(progress.get("currentGlobalId") or 1)
    highestUnlockedId = int(progress.get("highestUnlockedId") or 1)
    quizPassedMap = _obj(progress.get("quizPassedMap"))
    quizSubmittedMap = _obj(progress.get("quizSubmittedMap"))
    quizCompletedMap = _obj(progress.get("quizCompletedMap"))

    db = get_db()
    now = datetime.now(timezone.utc)

    db.course_progress.update_one(
        {"uid": user["uid"], "courseTitle": courseTitle},
        {"$set": {
            "uid": user["uid"],
            "courseTitle": courseTitle,
            "currentGlobalId": currentGlobalId,
            "highestUnlockedId": highestUnlockedId,
            "quizPassedMap": quizPassedMap,
            "quizSubmittedMap": quizSubmittedMap,
            "quizCompletedMap": quizCompletedMap,
            "updatedAt": now,
        },
         "$setOnInsert": {"createdAt": now}},
        upsert=True,
    )

    return jsonify({"ok": True})



# ----------------- ENV / CLIENTS -----------------
load_dotenv()
genai.configure(api_key=os.getenv("GOOGLE_API_KEY"))

YOUTUBE_API_KEY = os.getenv("YOUTUBE_API_KEY")
youtube = build("youtube", "v3", developerKey=YOUTUBE_API_KEY)

# ✅ Supadata
supadata = Supadata(api_key=os.getenv("SUPADATA_KEY", ""))
# ----------------- HELPERS -----------------
def is_quota_error(e: Exception) -> bool:
    msg = str(e).lower()
    return ("429" in msg) or ("quota" in msg) or ("rate limit" in msg) or ("resource exhausted" in msg)

def get_gemini_response(input_prompt: str) -> str:
    model = genai.GenerativeModel("gemini-2.5-flash")
    response = model.generate_content(input_prompt)

    if not getattr(response, "candidates", None):
        raise ValueError("Gemini API returned no candidates.")

    try:
        return response.candidates[0].content.parts[0].text.strip()
    except Exception as e:
        raise ValueError(f"Error extracting or parsing response: {e}")


# ---------------- MINDMAP (JSON TREE) ----------------
def _clean_json_text(s: str) -> str:
    """Best-effort cleanup if the model wraps JSON in code fences or adds leading text."""
    if not s:
        return ""
    txt = s.strip()
    # remove markdown fences
    txt = re.sub(r"^```(?:json)?\s*", "", txt, flags=re.IGNORECASE)
    txt = re.sub(r"```\s*$", "", txt)
    # If the model returns extra text before/after JSON, try to extract the first JSON object.
    # This is intentionally simple and safe.
    first = txt.find("{")
    last = txt.rfind("}")
    if first != -1 and last != -1 and last > first:
        txt = txt[first:last+1]
    # Remove trailing commas before } or ] (common LLM mistake)
    txt = re.sub(r",\s*([}\]])", r"\1", txt)
    return txt.strip()

import json, re
from typing import Any

def _strip_code_fences(s: str) -> str:
    if not s:
        return s
    s = re.sub(r"^```(?:json)?\s*", "", s.strip(), flags=re.IGNORECASE)
    s = re.sub(r"\s*```$", "", s.strip())
    return s.strip()

def _remove_trailing_commas(s: str) -> str:
    return re.sub(r",\s*([}\]])", r"\1", s)

def _find_first_json_span(text: str) -> str | None:
    if not text:
        return None

    start = None
    for i, ch in enumerate(text):
        if ch == '{' or ch == '[':
            start = i
            break
    if start is None:
        return None

    stack = []
    in_str = False
    esc = False

    for j in range(start, len(text)):
        ch = text[j]

        if in_str:
            if esc:
                esc = False
            elif ch == '\\':
                esc = True
            elif ch == '"':
                in_str = False
            continue

        if ch == '"':
            in_str = True
            continue

        if ch in '{[':
            stack.append(ch)
        elif ch in '}]':
            if not stack:
                return None
            top = stack.pop()
            if (top == '{' and ch != '}') or (top == '[' and ch != ']'):
                return None
            if not stack:
                return text[start:j+1]

    return None

def safe_json_parse(model_text: str) -> Any:
    """
    Defensive JSON parsing for LLM outputs.
    - Strips code fences
    - Extracts the first JSON object/array by brace/bracket balancing (respects strings/escapes)
    - Repairs trailing commas
    - Parses with json.loads (with light quote repairs fallback)
    """
    if not model_text or not str(model_text).strip():
        raise ValueError("Empty model output")

    raw = _strip_code_fences(str(model_text))

    span = _find_first_json_span(raw)
    if span is None:
        # try removing any leading text before first bracket
        raw2 = re.sub(r"^[^\[{]*", "", raw, flags=re.DOTALL)
        span = _find_first_json_span(raw2)

    if span is None:
        raise ValueError("Could not parse mindmap JSON from model output.")

    span = _remove_trailing_commas(span)

    try:
        return json.loads(span)
    except json.JSONDecodeError:
        repaired = span.replace("“", '"').replace("”", '"').replace("’", "'")
        repaired = _remove_trailing_commas(repaired)
        return json.loads(repaired)

def repair_json_with_gemini(bad_text: str) -> str:
    """Ask Gemini to repair/convert arbitrary output into STRICT valid JSON mindmap only."""
    bad_text = (bad_text or "").strip()
    if not bad_text:
        return ""
    prompt = f"""You are a strict JSON repair tool.

Return ONLY valid JSON. No markdown. No commentary. No code fences.

Target schema (recursive):
{{"name": string, "children": [ ... ]}}

Rules:
- Use double quotes for all keys/strings.
- No trailing commas.
- Ensure all brackets/braces are closed.
- Remove any non-JSON text.
- If input is truncated, COMPLETE the JSON in the most likely way.
- Keep labels short (2–8 words).

Input:
{bad_text}
"""
    try:
        model = genai.GenerativeModel("gemini-2.5-flash")
        resp = model.generate_content(prompt)
        text = (getattr(resp, "text", None) or "").strip()
        return _strip_code_fences(text)
    except Exception:
        return ""


def build_fallback_mindmap(transcript: str, safe_title: str) -> dict:
    # Heuristic fallback (works even without API key):
    # Build a NotebookLM-like structured mindmap by extracting key phrases around common headings.
    sentences = [s.strip() for s in re.split(r"(?<=[.!?])\s+", transcript) if s.strip()]

    def _norm(s: str) -> str:
        s = re.sub(r"\s+", " ", (s or "").strip())
        return s

    def _clean_label(s: str, max_words: int = 8) -> str:
        s = _norm(s)
        s = re.sub(r"^(hello|hi)\b.*?\b(tutorial|video)\b[:,\-\s]*", "", s, flags=re.I)
        s = re.sub(r"\b(please\s+subscribe|thanks\s+for\s+watching|hit\s+the\s+bell)\b.*$", "", s, flags=re.I)
        words = re.findall(r"[A-Za-z0-9\-]+", s)
        if not words:
            return "Item"
        return " ".join(words[:max_words])

    def _pick_points(keywords, max_items=7, max_words=7):
        kws = [k.lower() for k in keywords if k]
        out = []
        seen = set()
        for s in sentences:
            sl = s.lower()
            if any(k in sl for k in kws):
                lab = _clean_label(s, max_words=max_words)
                if lab.lower() in seen:
                    continue
                seen.add(lab.lower())
                out.append(lab)
            if len(out) >= max_items:
                break
        return out

    def _branch(name: str, points):
        return {"name": name, "children": [{"name": p, "children": []} for p in points]}

    # Detect main topic words (simple frequency)
    text_l = transcript.lower()
    has_gd = "gradient descent" in text_l
    has_cost = "cost function" in text_l
    has_lr = "learning rate" in text_l
    has_nn = "neural network" in text_l or "weights" in text_l or "bias" in text_l

    children = []

    # Overview / Purpose
    overview = _pick_points(
        ["in this video", "you will learn", "let's", "we will", "today"],
        max_items=4,
        max_words=8,
    )
    purpose = _pick_points(
        ["used to", "purpose", "optimiz", "train", "minimiz", "improve accuracy"],
        max_items=5,
        max_words=7,
    )
    if overview:
        children.append(_branch("Overview", overview))
    if purpose:
        children.append(_branch("Definition and Purpose", purpose))

    # Core concepts (topic-aware)
    core_points = []
    if has_gd:
        core_points += ["Optimization algorithm", "Move downhill (minimize loss)"]
    if has_cost:
        core_points += ["Cost function (prediction error)"]
    if has_lr:
        core_points += ["Learning rate (step size)"]
    if has_nn:
        core_points += ["Weights and biases", "Training on labeled data"]
    core_points += _pick_points(
        ["cost function", "learning rate", "weights", "biases", "minimize", "reduce the cost"],
        max_items=6,
        max_words=7,
    )
    core_points_dedup = []
    seen = set()
    for p in core_points:
        pl = p.lower()
        if pl in seen:
            continue
        seen.add(pl)
        core_points_dedup.append(p)
    if core_points_dedup:
        children.append(_branch("Key Concepts", core_points_dedup[:10]))

    # How it works / Process
    how_points = _pick_points(
        ["take small steps", "direction", "downhill", "gradient", "update", "adjust", "repeat"],
        max_items=8,
        max_words=8,
    )
    if how_points:
        children.append(_branch("How it works", how_points))

    # Examples / Analogies
    example_points = _pick_points(
        ["example", "let's consider", "house", "sold for", "squiggle", "number", "mountain", "maze"],
        max_items=7,
        max_words=8,
    )
    if example_points:
        children.append(_branch("Examples and Analogies", example_points))

    # Types / Variants
    types_points = []
    if "batch" in text_l:
        types_points.append("Batch Gradient Descent")
    if "stochastic" in text_l:
        types_points.append("Stochastic Gradient Descent")
    if "mini" in text_l and "batch" in text_l:
        types_points.append("Mini-batch Gradient Descent")
    if types_points:
        children.append({"name": "Types of Gradient Descent", "children": [{"name": t, "children": []} for t in types_points]})

    # Challenges / Pitfalls
    chall_points = _pick_points(
        ["non-convex", "global minimum", "saddle", "vanishing", "exploding", "unstable", "struggle"],
        max_items=8,
        max_words=8,
    )
    if chall_points:
        children.append(_branch("Challenges", chall_points))

    # Takeaways
    takeaways = _pick_points(
        ["powerful", "commonly used", "despite", "in summary", "end of this", "used to train"],
        max_items=4,
        max_words=8,
    )
    if takeaways:
        children.append(_branch("Summary / Takeaways", takeaways))

    if not children:
        children = [
            {"name": "Overview", "children": []},
            {"name": "Key Concepts", "children": []},
            {"name": "How it works", "children": []},
        ]

    return {"name": safe_title, "children": children}

    # ---------------- SUMMARY ----------------

# REPLACED

def generate_mindmap_tree(transcript: str, title: str = "Mindmap") -> dict:
    """Generate a detailed, concept-focused JSON tree mindmap from transcript.

    Returns schema: {"name": <root>, "children": [ ... ]}
    """
    safe_title = (title or "Mindmap").strip()[:80]
    transcript = (transcript or "").strip()
    if not transcript:
        return {"name": safe_title, "children": []}

    prompt = f"""
You are an expert instructor. Read the transcript, infer the underlying concepts, and produce a DETAILED mindmap that helps a student study.

Output rules (STRICT):
- Output ONLY valid JSON (no markdown, no commentary, no backticks).
- Schema (recursive): {{"name": string, "children": [schema]}}
- Root MUST be exactly: {{"name": "{safe_title}", "children": [...]}}
- Labels must be short: 2–8 words (no long sentences).
- Remove filler/intro/outro like: "hello everyone", "subscribe", "thanks for watching".
- Prefer concepts, definitions, steps, formulas, comparisons, examples, pitfalls.
- Expand acronyms when possible (e.g., SGD -> Stochastic Gradient Descent).
- Depth target: 4–6 levels.
- Breadth target: 6–10 top-level branches; each branch should have 3–10 children (when possible).
- If transcript is shallow, enrich with standard subtopics (1–2 nodes per concept) WITHOUT hallucinating facts.

Recommended top-level branches (adapt as relevant):
- Definition & Purpose
- Key Components / Concepts
- Workflow / Steps
- Examples / Applications
- Tools / Methods / Variants
- Comparisons (if any)
- Metrics / Evaluation (if any)
- Pitfalls / Challenges
- Summary / Takeaways

Transcript:
{transcript}
""".strip()

    def _strip_fences(s: str) -> str:
        s = (s or "").strip()
        s = re.sub(r"^```(?:json)?\s*", "", s, flags=re.I)
        s = re.sub(r"\s*```$", "", s)
        return s.strip()

    def _clean_labels(node: dict) -> dict:
        if not isinstance(node, dict):
            return {"name": safe_title, "children": []}
        name = str(node.get("name", "")).strip()
        name = re.sub(r"^(hello|hi)\b.*$", "", name, flags=re.I).strip() or name
        name = re.sub(r"\b(thanks for watching|please subscribe|hit the bell)\b.*$", "", name, flags=re.I).strip() or name
        words = re.findall(r"[A-Za-z0-9][A-Za-z0-9\-]*", name)
        name = " ".join(words[:10]) if words else (node.get("name") or "Item")

        kids = node.get("children") or []
        if not isinstance(kids, list):
            kids = []
        cleaned_children = []
        for ch in kids:
            if isinstance(ch, dict):
                cleaned_children.append(_clean_labels(ch))
        cleaned_children = [c for c in cleaned_children if str(c.get("name", "")).strip()]
        return {"name": name, "children": cleaned_children}

    try:
        model_name = os.getenv("GEMINI_MINDMAP_MODEL", "") or "gemini-2.5-flash"
        model = genai.GenerativeModel(model_name)

        resp = model.generate_content(
            prompt,
            generation_config={
                "temperature": 0.1,
                "max_output_tokens": 3200,
                "response_mime_type": "application/json",
            },
        )

        raw = getattr(resp, "text", "") or ""
        if not raw and getattr(resp, "candidates", None):
            try:
                raw = resp.candidates[0].content.parts[0].text or ""
            except Exception:
                raw = ""

        raw = _strip_fences(raw)
        raw = _clean_json_text(raw)

        try:
            data = safe_json_parse(raw)
        except Exception as parse_err:
            # Save raw model output for debugging
            try:
                with open("mindmap_llm_raw.txt", "w", encoding="utf-8") as f:
                    f.write(raw if isinstance(raw, str) else str(raw))
                print("❌ GEMINI RAW SAVED -> mindmap_llm_raw.txt")
            except Exception:
                pass

            # Second-pass: ask Gemini to repair/complete JSON (handles missing commas/truncation)
            repaired = repair_json_with_gemini(raw)
            if repaired:
                try:
                    with open("mindmap_llm_repaired.txt", "w", encoding="utf-8") as f:
                        f.write(repaired)
                except Exception:
                    pass
                try:
                    data = safe_json_parse(repaired)
                except Exception:
                    raise parse_err
            else:
                raise parse_err

        if not isinstance(data, dict) or "name" not in data:
            raise ValueError("Invalid mindmap JSON")

        data["name"] = safe_title
        return _clean_labels(data)

    except Exception as e:
        print("❌ GEMINI MINDMAP FAILED:", repr(e))
        return build_fallback_mindmap(transcript, safe_title)


@app.route("/summarize", methods=["POST"])
def summarize():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        transcript = (data.get("transcript") or "").strip()
        summaryType = (data.get("type") or "").strip()
        video_url = (data.get("video_url") or "").strip()

        if not transcript:
            return jsonify({"error": "Transcript not provided"}), 400
        if not summaryType:
            summaryType = "Paragraph"  # default to avoid client-side empty value

        db = get_db()

        cache_q = {"uid": user["uid"], "summaryType": summaryType}
        if video_url:
            cache_q["video_url"] = video_url
        cached = db.summaries.find_one(cache_q, sort=[("updatedAt", -1)], projection={"_id": 0})
        if cached and cached.get("summary"):
            return jsonify({"summary": cached["summary"], "cached": True})

        prompt = f"""Summarize the following transcript in the user's preferred format: {summaryType}.
Keep it accurate and easy to study.

TRANSCRIPT:
{transcript}
"""

        model = genai.GenerativeModel("gemini-2.5-flash")
        response = model.generate_content(prompt)
        summary = (response.text or "").strip()

        now = datetime.now(timezone.utc)
        doc = {"uid": user["uid"], "video_url": video_url or None, "summaryType": summaryType, "summary": summary, "updatedAt": now, "createdAt": now}
        db.summaries.insert_one(doc)

        return jsonify({"summary": summary, "cached": False})

    except Exception as e:
        if is_quota_error(e):
            return jsonify({"error": "Gemini quota exceeded. Please try later or enable billing."}), 429
        return jsonify({"error": str(e)}), 500

# ---------------- ROADMAP GENERATION ----------------
def generate_roadmap(formData):
    prmpt = f"""You are an expert curriculum designer and YouTube SEO specialist.

Create a personalized learning roadmap for a student with the following details:
- Age: {formData['age']}
- Subject: {formData['subject']}
- Current level: {formData['level']}
- Prior experience: {formData['experience']}
- Learning pace: {formData['pace']}
- Goal: {formData['goal']}
- Duration: {formData['duration']} months

IMPORTANT INSTRUCTIONS (STRICT):
1. Every topic MUST explicitly include the subject name "{formData['subject']}".
2. Topics must be written as precise YouTube search queries.
3. Avoid generic terms like "Introduction", "Basics", "Overview" alone.
4. Use phrases that a learner would type into YouTube.
5. Topics must be beginner-to-goal progressive and practical.
6. Do NOT include explanations, descriptions, or extra text.
7. Do NOT include commas inside a topic — each bullet must be ONE clean search query.
8. Do NOT reference any other programming language.

FORMAT:
Week 1:
- <YouTube search query>
- <YouTube search query>

Week 2:
- <YouTube search query>
- <YouTube search query>

Now generate the roadmap.
"""
    model = genai.GenerativeModel("gemini-2.5-flash")
    response = model.generate_content(prmpt)
    return response.text

def parse_roadmap(roadmap: str):
    weeks = {}
    current_week = None
    for line in roadmap.split("\n"):
        line = line.strip()
        if line.lower().startswith("week"):
            current_week = line.split(":")[0].strip()
            weeks[current_week] = []
        elif line.startswith("-") and current_week:
            topic = line[1:].strip()
            weeks[current_week].append(topic)

    # ✅ print parsed roadmap dictionary (like your old code)
    print("\n================ PARSED ROADMAP ================")
    print(json.dumps(weeks, indent=2, ensure_ascii=False))
    print("================================================\n")

    return weeks

# ---------------- YOUTUBE HELPERS (WITH DETAILED PRINTS) ----------------
def get_video_details(query, max_results=2, retries=3, delay=2):
    """
    Returns list of videos for a query with like_count.
    ✅ Also prints fetching details similar to your old code.
    """
    video_details = []
    results_count = 0
    next_page_token = None
    page_no = 0

    print(f"\n========== YOUTUBE FETCH START ==========")
    print(f"Query: {query} | max_results={max_results}")
    print(f"========================================\n")

    while results_count < max_results:
        page_no += 1
        try:
            print(f"[SEARCH] page={page_no} results_so_far={results_count} token={next_page_token}")
            search_response = youtube.search().list(
                q=query,
                part="snippet",
                maxResults=min(50, max_results - results_count),
                type="video",
                pageToken=next_page_token
            ).execute()

            items = search_response.get("items", [])
            print(f"[SEARCH] page={page_no} returned_items={len(items)}")

            for item in items:
                video_id = item.get("id", {}).get("videoId")
                if not video_id:
                    print("[SKIP] Missing videoId in item")
                    continue

                title = item.get("snippet", {}).get("title", "")
                channel = item.get("snippet", {}).get("channelTitle", "")
                published = item.get("snippet", {}).get("publishedAt", "")
                video_url = f"https://www.youtube.com/watch?v={video_id}"

                # Fetch video statistics with retry
                stats = {}
                last_err = None
                for attempt in range(1, retries + 1):
                    try:
                        print(f"  [STATS] attempt={attempt}/{retries} id={video_id}")
                        video_data = youtube.videos().list(
                            part="statistics,contentDetails",
                            id=video_id
                        ).execute()
                        if video_data.get("items"):
                            stats = video_data["items"][0].get("statistics", {}) or {}
                        break
                    except HttpError as e:
                        last_err = e
                        if e.resp.status in [500, 503]:
                            sleep_s = delay * attempt
                            print(f"  [STATS-RETRY] status={e.resp.status} sleeping={sleep_s}s")
                            time.sleep(sleep_s)
                        else:
                            raise

                if last_err and not stats:
                    print(f"  [STATS-FAIL] id={video_id} err={str(last_err)}")
                    continue

                like_count = int(stats.get("likeCount", 0) or 0)
                view_count = int(stats.get("viewCount", 0) or 0)
                comment_count = int(stats.get("commentCount", 0) or 0)

                video_details.append({
                    "url": video_url,
                    "video_id": video_id,
                    "title": title,
                    "channel": channel,
                    "publishedAt": published,
                    "like_count": like_count,
                    "view_count": view_count,
                    "comment_count": comment_count
                })

                # ✅ This print line matches your older style
                print(query, " [", results_count, "] : ", video_details[-1])

                results_count += 1
                if results_count >= max_results:
                    break

            next_page_token = search_response.get("nextPageToken")
            if not next_page_token:
                print("[SEARCH] No nextPageToken, ending.")
                break

        except HttpError as e:
            if e.resp.status in [500, 503]:
                print(f"[SEARCH-RETRY] status={e.resp.status} sleeping={delay}s")
                time.sleep(delay)
                continue
            raise

    print(f"\n========== YOUTUBE FETCH END ==========")
    print(f"Query: {query} | fetched={len(video_details)}")
    print(f"======================================\n")

    return video_details

def get_best_video(topic):
    # ✅ consistent with your old logic: take first result
    video_list = get_video_details(topic, max_results=2)
    print("here")  # same marker you used earlier
    if not video_list:
        return None
    return video_list[0]["url"]

def build_weekly_json(roadmap):
    weeks = parse_roadmap(roadmap)
    result = []

    print("\n=========== BUILD WEEKLY JSON START ===========")
    for week, topics in weeks.items():
        print(f"\n[WEEK] {week} topics_count={len(topics)}")
        week_data = []
        for idx, topic in enumerate(topics, start=1):
            q = topic + " in english"
            print(f"  -> ({idx}) Topic: {topic}")
            print(f"     Query: {q}")
            video = get_best_video(q)
            week_data.append({"topic": topic, "video": video if video else "No video found"})
        result.append({week: week_data})
    print("\n=========== BUILD WEEKLY JSON END ===========\n")

    return result

@app.route("/generate-roadmap", methods=["POST"])
def generate():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        formData = request.get_json() or {}
        roadmap = generate_roadmap(formData)

        print("\n================ ROADMAP RAW TEXT ================")
        print(roadmap)
        print("==================================================\n")

        final_output = build_weekly_json(roadmap)

        with open("videos.json", "w", encoding="utf-8") as f:
            json.dump(final_output, f, indent=2, ensure_ascii=False)

        return jsonify({"roadmap": roadmap, "videos": final_output})

    except Exception as e:
        if is_quota_error(e):
            return jsonify({"error": "Gemini quota exceeded. Please try later or enable billing."}), 429
        return jsonify({"error": str(e)}), 500

# ---------------- TRANSCRIPT ----------------
@app.route("/get-transcript", methods=["POST"])
def get_transcript():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        url = (data.get("url") or "").strip()

        if not url:
            return jsonify({"error": "URL is required"}), 400

        db = get_db()

        cached = db.transcripts.find_one({"uid": user["uid"], "url": url}, projection={"_id": 0})
        if cached and cached.get("transcript"):
            return jsonify({"url": url, "transcript": cached["transcript"], "language": cached.get("language", "en"), "cached": True})

        transcript = supadata.transcript(
            url=url,
            lang="en",
            text=True,
            mode="auto"
        )

        # Supadata returns either a finished transcript with .content or a job_id
        if hasattr(transcript, "content"):
            db.transcripts.update_one(
                {"uid": user["uid"], "url": url},
                {"$set": {"uid": user["uid"], "url": url, "transcript": transcript.content, "language": getattr(transcript, "lang", "en"), "updatedAt": datetime.now(timezone.utc)},
                 "$setOnInsert": {"createdAt": datetime.now(timezone.utc)}},
                upsert=True,
            )
            return jsonify({"url": url, "transcript": transcript.content, "language": transcript.lang, "cached": False})
        else:
            return jsonify({"message": "Transcript is being processed", "job_id": transcript.job_id})

    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ---------------- QUIZ ----------------
def generate_mcq(transcript: str):
    prmpt = f"""You are an expert educational consultant.
A student has given a video transcript and wants to create a multiple-choice quiz based on it.

Transcript:
{transcript}

Create a multiple-choice quiz with 10 questions. Each question should have 4 options.

If a question requires a code snippet (because the transcript includes code), include a **short** snippet inline in the question using single backticks, like: `for i in range(n): ...`.
Keep the snippet on the SAME LINE as the question (do not use multi-line code blocks).
Format:
Question 1: Question
a) Option 1 
b) Option 2
c) Option 3
d) Option 4
Correct Answer: Answer

Only the quiz is required.
"""
    model = genai.GenerativeModel("gemini-2.5-flash")
    response = model.generate_content(prmpt)
    return response.text

def _normalize_text(s: str) -> str:
    if s is None:
        return ""
    s = str(s).strip().lower()
    s = re.sub(r"\s+", " ", s)
    return s

def parse_to_json(quiz_text: str):
    """
    Robust MCQ parser.

    Handles:
    - Correct Answer: b
    - Correct Answer: b) Option text
    - Correct Answer: Option text
    """
    quiz_data = []
    blocks = re.split(r"Question\s*\d+\s*:", quiz_text, flags=re.IGNORECASE)

    for block in blocks:
        block = block.strip()
        if not block:
            continue

        lines = [l.strip() for l in block.splitlines() if l.strip()]
        if len(lines) < 3:
            continue

        question = lines[0]

        # collect options a-d
        options = []
        for line in lines[1:]:
            m = re.match(r"^([a-dA-D])[\)\.]\s*(.+)$", line)
            if m:
                options.append(m.group(2).strip())
            if len(options) == 4:
                break

        if len(options) < 2:
            continue

        answer_line = next((l for l in lines if l.lower().startswith("correct answer")), "")
        raw = answer_line.split(":", 1)[1].strip() if ":" in answer_line else ""
        raw_norm = _normalize_text(raw)

        correct_option = ""

        # Case 1: raw starts with a/b/c/d (like "b")
        m = re.match(r"^([a-d])\b", raw_norm)
        if m and len(options) >= 4:
            idx = ord(m.group(1)) - ord("a")
            if 0 <= idx < len(options):
                correct_option = options[idx]

        # Case 2: raw like "b) option text" or "b. option text"
        if not correct_option:
            m2 = re.match(r"^([a-d])[\)\.]\s*(.+)$", raw_norm)
            if m2 and len(options) >= 4:
                idx = ord(m2.group(1)) - ord("a")
                if 0 <= idx < len(options):
                    correct_option = options[idx]

        # Case 3: raw is option text -> fuzzy match
        if not correct_option:
            def canon(x):
                x = _normalize_text(x)
                x = re.sub(r"[^a-z0-9 ]+", "", x)
                return x.strip()

            raw_c = canon(raw)
            for opt in options:
                oc = canon(opt)
                if not oc:
                    continue
                if oc == raw_c or oc in raw_c or raw_c in oc:
                    correct_option = opt
                    break

        if correct_option:
            quiz_data.append({"question": question, "options": options, "answer": correct_option})

    return quiz_data

@app.route("/generate-mcq", methods=["POST"])
def generate_mcq_api():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        transcript = (data.get("transcript") or "").strip()
        video_url = (data.get("video_url") or "").strip()
        courseTitle = (data.get("courseTitle") or "").strip()

        if not video_url:
            return jsonify({"error": "video_url is required"}), 400

        # ✅ Hold enforcement
        if not courseTitle:
            courseTitle = derive_course_title_from_video(user.get("uid"), video_url) or ""
        if courseTitle:
            blocked = block_if_held(user.get("uid"), courseTitle)
            if blocked:
                return blocked

        db = get_db()

        # ✅ 1) If quiz already exists for this user+video, return it (no transcript needed)
        cached = db.quizzes.find_one(
            {"uid": user["uid"], "video_url": video_url},
            sort=[("updatedAt", -1)],
            projection={"_id": 0}
        )
        if cached and cached.get("quiz_id") and cached.get("questions_only"):
            return jsonify({
                "quiz_id": cached["quiz_id"],
                "questions": cached["questions_only"],
                "cached": True
            })

        # ✅ 2) If transcript not sent (common after logout/login), fetch it from DB cache
        if not transcript:
            tdoc = db.transcripts.find_one(
                {"uid": user["uid"], "url": video_url},
                sort=[("updatedAt", -1)],
                projection={"_id": 0, "transcript": 1}
            )
            if tdoc and tdoc.get("transcript"):
                transcript = tdoc["transcript"].strip()

        # ✅ 3) If still no transcript, tell frontend to fetch transcript first
        if not transcript:
            return jsonify({
                "error": "Transcript not available. Please fetch transcript first.",
                "needs_transcript": True
            }), 400

        # ✅ 4) Generate new quiz now
        quiz_text = generate_mcq(transcript)
        quiz_data = parse_to_json(quiz_text)
        quiz_data = quiz_data[:10]

        if not quiz_data:
            return jsonify({"error": "Failed to parse quiz. Try again."}), 500

        quiz_id = str(uuid.uuid4())
        questions_only = [{"question": q["question"], "options": q["options"]} for q in quiz_data]

        now = datetime.now(timezone.utc)
        db.quizzes.insert_one({
            "uid": user["uid"],
            "video_url": video_url,
            "quiz_id": quiz_id,
            "full_quiz": quiz_data,
            "questions_only": questions_only,
            "attempts_used": 0,
            "createdAt": now,
            "updatedAt": now,
        })

        return jsonify({"quiz_id": quiz_id, "questions": questions_only, "cached": False})

    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/generate-mindmap", methods=["POST"])
def generate_mindmap_api():
    """Generate (or fetch cached) mindmap JSON tree for a given video.

    Body: { video_url: str, transcript?: str, title?: str, courseTitle?: str, force?: bool }
    Returns: { tree: {...}, cached: bool }
    """
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        video_url = (data.get("video_url") or "").strip()
        transcript = (data.get("transcript") or "").strip()
        title = (data.get("title") or "Mindmap").strip() or "Mindmap"
        courseTitle = (data.get("courseTitle") or "").strip()
        force = bool(data.get("force"))

        if not video_url:
            return jsonify({"error": "video_url is required"}), 400

        # ✅ Hold enforcement
        if not courseTitle:
            courseTitle = derive_course_title_from_video(user.get("uid"), video_url) or ""
        if courseTitle:
            blocked = block_if_held(user.get("uid"), courseTitle)
            if blocked:
                return blocked

        db = get_db()

        if not force:
            cached = db.mindmaps.find_one(
                {"uid": user["uid"], "video_url": video_url},
                sort=[("updatedAt", -1)],
                projection={"_id": 0, "tree": 1}
            )
            if cached and cached.get("tree"):
                return jsonify({"tree": cached["tree"], "cached": True})

        # If transcript not sent, try DB transcript cache
        if not transcript:
            tdoc = db.transcripts.find_one(
                {"uid": user["uid"], "url": video_url},
                sort=[("updatedAt", -1)],
                projection={"_id": 0, "transcript": 1}
            )
            if tdoc and tdoc.get("transcript"):
                transcript = tdoc["transcript"].strip()

        if not transcript:
            return jsonify({
                "error": "Transcript not available. Please fetch transcript first.",
                "needs_transcript": True
            }), 400

        tree = generate_mindmap_tree(transcript, title=title)
        now = datetime.now(timezone.utc)
        db.mindmaps.update_one(
            {"uid": user["uid"], "video_url": video_url},
            {"$set": {"uid": user["uid"], "video_url": video_url, "title": title, "tree": tree, "updatedAt": now},
             "$setOnInsert": {"createdAt": now}},
            upsert=True
        )

        return jsonify({"tree": tree, "cached": False})

    except Exception as e:
        return jsonify({"error": str(e)}), 500


# ---------------- NOTES (Mindmap) ----------------
@app.route("/notes/list", methods=["GET"])
def list_notes():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        db = get_db()
        notes = list(
            db.notes.find(
                {"uid": user["uid"]},
                projection={"_id": 0}
            ).sort("updatedAt", -1).limit(200)
        )
        return jsonify({"notes": notes})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/notes/save-mindmap", methods=["POST"])
def save_mindmap_note():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        note_type = "mindmap"
        title = (data.get("title") or "Mindmap").strip()[:120]
        courseTitle = (data.get("courseTitle") or "").strip()[:200]
        video_url = (data.get("video_url") or "").strip()
        tree = data.get("tree") or {}

        if not video_url:
            return jsonify({"error": "video_url is required"}), 400
        if not isinstance(tree, dict) or "name" not in tree:
            return jsonify({"error": "tree is required"}), 400

        db = get_db()
        now = datetime.now(timezone.utc)
        note_id = (data.get("note_id") or "").strip() or str(uuid.uuid4())

        db.notes.update_one(
            {"uid": user["uid"], "note_id": note_id},
            {
                "$set": {
                    "uid": user["uid"],
                    "note_id": note_id,
                    "type": note_type,
                    "title": title,
                    "courseTitle": courseTitle,
                    "video_url": video_url,
                    "tree": tree,
                    "updatedAt": now,
                },
                "$setOnInsert": {"createdAt": now},
            },
            upsert=True,
        )

        return jsonify({"ok": True, "note_id": note_id})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/notes/delete", methods=["POST"])
def delete_note():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        note_id = (data.get("note_id") or "").strip()
        if not note_id:
            return jsonify({"error": "note_id is required"}), 400
        db = get_db()
        db.notes.delete_one({"uid": user["uid"], "note_id": note_id})
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"error": str(e)}), 500

def _norm(s: str) -> str:
    if not s:
        return ""
    return re.sub(r"^[a-dA-D][\)\.]\s*", "", str(s)).strip().lower()

@app.route("/submit-quiz", methods=["POST"])
def submit_quiz():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    try:
        data = request.get_json() or {}
        quiz_id = data.get("quiz_id")
        courseTitle = (data.get("courseTitle") or "").strip()
        answers = data.get("answers")

        if not quiz_id:
            return jsonify({"error": "quiz_id required"}), 400
        if not isinstance(answers, list):
            return jsonify({"error": "answers must be a list"}), 400

        db = get_db()
        quiz_doc = db.quizzes.find_one({"uid": user["uid"], "quiz_id": quiz_id})
        if not quiz_doc:
            return jsonify({"error": "Invalid quiz_id"}), 400

        # ✅ Hold enforcement (derive course by stored video_url if needed)
        if not courseTitle:
            courseTitle = derive_course_title_from_video(user.get("uid"), quiz_doc.get("video_url") or "") or ""
        if courseTitle:
            blocked = block_if_held(user.get("uid"), courseTitle)
            if blocked:
                return blocked
        used = int(quiz_doc.get("attempts_used", 0))

        full_quiz = quiz_doc.get("full_quiz", [])
        if not full_quiz:
            return jsonify({"error": "Quiz data not found"}), 500

        # Evaluate
        score = 0
        results = []
        for i, q in enumerate(full_quiz):
            user_ans = answers[i] if i < len(answers) else ""
            correct = q.get("answer", "")
            ok = (_normalize_text(user_ans) == _normalize_text(correct))
            if ok:
                score += 1
            results.append({
                "question": q.get("question"),
                "selected": user_ans,
                "correct": correct,
                "isCorrect": ok
            })

        used += 1
        db.quizzes.update_one(
            {"uid": user["uid"], "quiz_id": quiz_id},
            {"$set": {"attempts_used": used, "updatedAt": datetime.now(timezone.utc)}}
        )

        required = max(1, math.ceil(len(full_quiz) * PASS_PERCENT))
        passed = score >= required
        return jsonify({
            "score": score,
            "total": len(full_quiz),
            "required": required,
            "pass_percent": PASS_PERCENT,
            "passed": passed,
            "attempts_used": used,
            "results": results
        })

    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ---------------- CHAT (CONTINUOUS) ----------------
CHAT_SESSIONS = {}   # conversation_id -> list of messages
MAX_TURNS = 20       # keep last N messages to control token usage

# ---------------- PDF CHAT (Upload + Q&A) ----------------
# In-memory storage (per server instance). For production, store in DB or object storage.
PDF_STORE = {}  # pdf_id -> {uid, filename, text, chunks, created_at}
MAX_PDF_CHARS = 250_000  # safety cap for extracted text


def _chunk_text(s: str, chunk_size: int = 1200, overlap: int = 200):
    s = (s or '').strip()
    if not s:
        return []
    out=[]
    i=0
    n=len(s)
    while i < n:
        j=min(n, i+chunk_size)
        out.append(s[i:j])
        if j==n:
            break
        i=max(0, j-overlap)
    return out


def _simple_retrieve(chunks, query: str, k: int = 6):
    q = (query or '').lower()
    toks = [t for t in re.findall(r"[a-z0-9]{3,}", q)][:30]
    if not toks:
        return chunks[:k]
    scored=[]
    for c in chunks:
        cl=c.lower()
        score=sum(cl.count(t) for t in toks)
        if score>0:
            scored.append((score, c))
    scored.sort(key=lambda x: x[0], reverse=True)
    best=[c for _,c in scored[:k]]
    if len(best)<k:
        # backfill with early chunks to keep some context
        for c in chunks:
            if c not in best:
                best.append(c)
            if len(best)>=k:
                break
    return best

def _trim_history(history, max_turns=MAX_TURNS):
    # Each turn is usually user+assistant. Keep last ~max_turns*2 messages.
    if len(history) > max_turns * 2:
        return history[-max_turns * 2:]
    return history

@app.route("/chat", methods=["POST"])
def chat_bot():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    subject = (data.get("subject") or "").strip()
    user_input = (data.get("message") or "").strip()
    conversation_id = (data.get("conversation_id") or "").strip()

    if not subject or not user_input:
        return jsonify({"error": "Both 'subject' and 'message' are required"}), 400

    if not conversation_id:
        return jsonify({"error": "conversation_id is required"}), 400

    # Load history for this conversation
    history = CHAT_SESSIONS.get(conversation_id, [])

    # Add user message
    history.append({"role": "user", "content": user_input})
    history = _trim_history(history)

    system_prompt = f"""
You are a helpful tutor specializing in {subject}.
Rules:
1) If the question is NOT related to {subject}, reply exactly: Out of scope
2) Keep response clear like ChatGPT.
3) Use numbered points for explanations.
4) If code is needed, put it in a separate fenced code block using triple backticks with language.
5) Do NOT use stars (*) or dash bullets (-). Use only numbers (1., 2., 3.)
6) Be concise but helpful.
"""

    convo_text = ""
    for msg in history:
        role = msg["role"]
        content = msg["content"]
        if role == "user":
            convo_text += f"User: {content}\n"
        else:
            convo_text += f"Assistant: {content}\n"

    prompt = f"""{system_prompt}

Conversation so far:
{convo_text}

Now respond to the latest user message only.
"""

    try:
        model = genai.GenerativeModel("gemini-2.5-flash")
        response = model.generate_content(prompt)
        reply_text = (getattr(response, 'text', None) or '').strip()

        history.append({"role": "assistant", "content": reply_text})
        history = _trim_history(history)
        CHAT_SESSIONS[conversation_id] = history

        return jsonify({
            "conversation_id": conversation_id,
            "reply": reply_text,
            "history_size": len(history)
        })
    except Exception as e:
        if is_quota_error(e):
            return jsonify({"error": "Gemini quota exceeded. Please try later or enable billing."}), 429
        return jsonify({"error": str(e)}), 500


@app.route("/pdf/upload", methods=["POST"])
def pdf_upload():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    if "file" not in request.files:
        return jsonify({"error": "No file provided (field name: file)"}), 400

    f = request.files["file"]
    filename = (getattr(f, 'filename', '') or '').strip() or 'document.pdf'
    if not filename.lower().endswith('.pdf'):
        return jsonify({"error": "Only PDF files are supported"}), 400

    try:
        reader = PdfReader(f)
        parts = []
        for page in reader.pages:
            try:
                t = page.extract_text() or ''
            except Exception:
                t = ''
            if t:
                parts.append(t)

        text = "\n".join(parts).strip()
        if not text:
            return jsonify({"error": "Could not extract text from this PDF (it may be scanned). Try a text-based PDF."}), 400

        if len(text) > MAX_PDF_CHARS:
            text = text[:MAX_PDF_CHARS]

        chunks = _chunk_text(text)
        pdf_id = str(uuid.uuid4())
        PDF_STORE[pdf_id] = {
            "uid": user["uid"],
            "filename": filename,
            "text": text,
            "chunks": chunks,
            "created_at": datetime.now(timezone.utc).isoformat(),
        }

        return jsonify({"pdf_id": pdf_id, "filename": filename, "chunks": len(chunks)})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/pdf/chat", methods=["POST"])
def pdf_chat():
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    data = request.get_json() or {}
    pdf_id = (data.get("pdf_id") or '').strip()
    question = (data.get("question") or '').strip()

    if not pdf_id or not question:
        return jsonify({"error": "pdf_id and question are required"}), 400

    obj = PDF_STORE.get(pdf_id)
    if not obj or obj.get("uid") != user["uid"]:
        return jsonify({"error": "PDF not found (upload again)"}), 404

    chunks = obj.get("chunks") or []
    best = _simple_retrieve(chunks, question, k=6)
    context = "\n\n---\n\n".join(best)

    system_prompt = """
You are a helpful assistant.
You must answer ONLY using the provided PDF excerpts.
If the answer is not in the excerpts, reply exactly: Not found in the document
Rules:
1) Keep response clear like ChatGPT.
2) Use numbered points only (1., 2., 3.).
3) If code is needed, put it in a separate fenced code block using triple backticks with language.
4) Do NOT use stars (*) or dash bullets (-).
"""

    prompt = f"""{system_prompt}

PDF filename: {obj.get('filename')}

PDF excerpts:
{context}

User question:
{question}
"""

    try:
        model = genai.GenerativeModel("gemini-2.5-flash")
        response = model.generate_content(prompt)
        reply_text = (getattr(response, 'text', None) or '').strip()
        return jsonify({"reply": reply_text})
    except Exception as e:
        if is_quota_error(e):
            return jsonify({"error": "Gemini quota exceeded. Please try later or enable billing."}), 429
        return jsonify({"error": str(e)}), 500


if __name__ == "__main__":
    app.run(debug=True)
