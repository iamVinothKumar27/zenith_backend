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
from datetime import datetime, timezone, timedelta

# ---- datetime helpers (avoid naive vs aware issues) ----
def _to_utc_aware(dt):
    """Ensure a datetime is timezone-aware in UTC (Mongo may return naive UTC)."""
    if not dt or not isinstance(dt, datetime):
        return dt
    if dt.tzinfo is None:
        return dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


from werkzeug.utils import secure_filename

from flask import g
from pymongo import MongoClient
import gridfs
from bson.objectid import ObjectId
import firebase_admin
from firebase_admin import credentials as fb_credentials
from firebase_admin import auth as fb_auth
load_dotenv()  

# ----------------- EMAIL (SMTP: Titan/GoDaddy etc.) -----------------
import smtplib
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
import re
# ----------------- PASSWORD REUSE PREVENTION -----------------
PASSWORD_PEPPER = os.getenv("PASSWORD_PEPPER", "").strip()  # set this in .env (random long string)

def _pw_hash(uid: str, password: str) -> str:
    """
    Hash password so we can detect reuse.
    Uses SHA-256 with uid + server-side pepper.
    NOTE: This is NOT used for authentication; only reuse detection.
    """
    uid = (uid or "").strip()
    password = (password or "").strip()
    raw = f"{uid}|{PASSWORD_PEPPER}|{password}".encode("utf-8")
    return hashlib.sha256(raw).hexdigest()

def _yt_id(url: str) -> str:
    """Extract YouTube ID from watch?v= or youtu.be links."""
    if not url:
        return ""
    m = re.search(r"(?:v=|youtu\.be/)([A-Za-z0-9_-]{6,})", url)
    return m.group(1) if m else ""


def derive_video_number_from_course(db, uid: str, course_title: str, video_url: str):
    """
    Returns (video_no, total_videos) like (4, 32) by searching course_states.videos
    Supports shapes:
      1) [{"Week 1": [{"topic":..., "video": URL}, ...]}, {"Week 2": [...]}]   ✅ your current build_weekly_json
      2) [{"week":"Week 1","videos":[{"videoUrl":...}, ...]}]
      3) flat list of urls or dicts
    """
    if not uid or not course_title or not video_url:
        return (None, None)

    target_id = _yt_id(video_url) or video_url.strip()

    state = db.course_states.find_one(
        {"uid": uid, "courseTitle": course_title},
        {"videos": 1, "weeks": 1, "course": 1}
    )
    if not state:
        return (None, None)

    def _get_url(obj):
        if obj is None:
            return ""
        if isinstance(obj, str):
            return obj.strip()
        if isinstance(obj, dict):
            return (obj.get("videoUrl")
                    or obj.get("video_url")
                    or obj.get("url")
                    or obj.get("video")
                    or "").strip()
        return str(obj).strip()

    def _flatten_video_urls(node):
        out = []

        if node is None:
            return out

        # string url
        if isinstance(node, str):
            u = node.strip()
            if u:
                out.append(u)
            return out

        # list -> recurse each
        if isinstance(node, list):
            for it in node:
                out.extend(_flatten_video_urls(it))
            return out

        # dict -> handle multiple schema
        if isinstance(node, dict):
            # A) {"videos": [ ... ]}
            if isinstance(node.get("videos"), list):
                for v in node.get("videos"):
                    u = _get_url(v)
                    if u:
                        out.append(u)
                    else:
                        out.extend(_flatten_video_urls(v))
                return out

            # B) build_weekly_json: {"Week 1": [ {topic, video}, ... ]}
            for k, v in node.items():
                if isinstance(v, list):
                    # likely week list
                    for item in v:
                        u = _get_url(item)  # ✅ reads "video" key
                        if u:
                            out.append(u)
                        else:
                            out.extend(_flatten_video_urls(item))
                else:
                    out.extend(_flatten_video_urls(v))
            return out

        return out

    # ✅ pull weeks/videos from all possible places
    videos_root = state.get("videos")
    if not videos_root and isinstance(state.get("course"), dict):
        videos_root = state["course"].get("videos") or state["course"].get("weeks")
    if not videos_root:
        videos_root = state.get("weeks")

    flattened = _flatten_video_urls(videos_root)
    if not flattened:
        return (None, None)

    total = len(flattened)

    # match by youtube id (preferred) else full url
    for idx, vurl in enumerate(flattened, start=1):
        vid = _yt_id(vurl) or vurl.strip()
        if vid and target_id and vid == target_id:
            return (idx, total)

    return (None, total)

SMTP_HOST = os.getenv("SMTP_HOST", "").strip()
SMTP_PORT = int(os.getenv("SMTP_PORT", "587"))
SMTP_USER = os.getenv("SMTP_USER", "").strip()
SMTP_PASS = os.getenv("SMTP_PASS", "").strip()

# ✅ Sender aliases (Google Workspace / Gmail "Send mail as")
# These should be configured as aliases for your primary mailbox (SMTP_USER).
MAIL_FROM_DEFAULT = (os.getenv("MAIL_FROM_DEFAULT") or os.getenv("MAIL_FROM") or os.getenv("SMTP_FROM") or SMTP_USER).strip()
MAIL_FROM_AUTH = (os.getenv("MAIL_FROM_AUTH") or "authentication@zenithlearning.site").strip()
MAIL_FROM_COURSES = (os.getenv("MAIL_FROM_COURSES") or "courses@zenithlearning.site").strip()
MAIL_FROM_PROFILE = (os.getenv("MAIL_FROM_PROFILE") or "profile@zenithlearning.site").strip()
MAIL_FROM_ADMIN = (os.getenv("MAIL_FROM_ADMIN") or "admin@zenithlearning.site").strip()
MAIL_FROM_CONTACT = (os.getenv("MAIL_FROM_CONTACT") or "contact@zenithlearning.site").strip()

# Optional: use SendGrid API instead of SMTP (kept for safety, but Mailgun removed)
SENDGRID_API_KEY = os.getenv("SENDGRID_API_KEY", "").strip()
SENDGRID_FROM = os.getenv("SENDGRID_FROM", "").strip()

FRONTEND_BASE_URL = os.getenv("FRONTEND_BASE_URL", os.getenv("FRONTEND_URL", "")).strip().rstrip("/")
ADMIN_EMAIL = os.getenv("ADMIN_EMAIL", "admin@zenithlearning.site").strip()
CONTACT_INBOX = os.getenv("CONTACT_INBOX", "contact@zenithlearning.site").strip()


def _smtp_ready() -> bool:
    return bool(SMTP_HOST and SMTP_PORT and SMTP_USER and SMTP_PASS)

def _pick_from(kind: str = "") -> str:
    k = (kind or "").strip().lower()
    if k in ("auth", "authentication", "login"):
        return MAIL_FROM_AUTH or MAIL_FROM_DEFAULT
    if k in ("courses", "course", "quiz"):
        return MAIL_FROM_COURSES or MAIL_FROM_DEFAULT
    if k in ("profile",):
        return MAIL_FROM_PROFILE or MAIL_FROM_DEFAULT
    if k in ("admin",):
        return MAIL_FROM_ADMIN or MAIL_FROM_DEFAULT
    if k in ("contact",):
        return MAIL_FROM_CONTACT or MAIL_FROM_DEFAULT
    return MAIL_FROM_DEFAULT or SMTP_USER

def _send_email_sync_smtp(
    to_email: str,
    subject: str,
    html_body: str,
    text_body: str = "",
    *,
    from_email: str = None,
    reply_to: str = None,
) -> bool:
    """Send email via SMTP. Returns True if sent, False otherwise.

    Notes:
    - When using Google Workspace SMTP, authenticate with SMTP_USER (primary mailbox),
      and set From to one of its verified aliases (courses@, profile@, etc.).
    - For contact form, prefer setting Reply-To to the user's email.
    """
    if not to_email:
        return False
    if not _smtp_ready():
        print("[MAIL] SMTP not configured. Skipping send to:", to_email, "subject:", subject)
        return False

    sender = (from_email or MAIL_FROM_DEFAULT or SMTP_USER).strip()

    msg = MIMEMultipart("alternative")
    msg["From"] = f"Zenith Learning <{sender}>"
    msg["To"] = to_email
    msg["Subject"] = subject
    if reply_to:
        msg["Reply-To"] = reply_to

    if text_body:
        msg.attach(MIMEText(text_body, "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))

    # Keep timeouts low to avoid Gunicorn worker timeouts on hosted deployments.
    connect_timeout = int(os.getenv("SMTP_TIMEOUT", "8"))

    server = None
    try:
        if int(SMTP_PORT) == 465:
            server = smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=connect_timeout)
            server.ehlo()
        else:
            server = smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=connect_timeout)
            server.ehlo()
            try:
                server.starttls()
                server.ehlo()
            except Exception:
                pass

        server.login(SMTP_USER, SMTP_PASS)
        server.sendmail(sender, [to_email], msg.as_string())
        server.quit()
        print("[MAIL] SMTP Sent:", subject, "->", to_email, "| from:", sender)
        return True
    except Exception as e:
        print("[MAIL] SMTP Send failed:", e)
        try:
            if server:
                server.quit()
        except Exception:
            pass
        return False

def _send_email_sync_sendgrid(to_email: str, subject: str, html_body: str, text_body: str = "") -> bool:
    """Send email via SendGrid Web API. Returns True if accepted by SendGrid."""
    api_key = os.getenv("SENDGRID_API_KEY", "").strip()
    if not api_key:
        return False

    from_email = os.getenv("SENDGRID_FROM", "").strip() or MAIL_FROM
    if not from_email:
        return False

    try:
        import requests  # type: ignore
    except Exception:
        requests = None

    payload = {
        "personalizations": [{
            "to": [{"email": to_email}],
            "subject": subject,
        }],
        "from": {"email": from_email, "name": "Zenith Learning"},
        "content": [
            {"type": "text/plain", "value": text_body or " "},
            {"type": "text/html", "value": html_body},
        ],
    }

    try:
        if requests:
            r = requests.post(
                "https://api.sendgrid.com/v3/mail/send",
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                json=payload,
                timeout=10,
            )
            if 200 <= r.status_code < 300:
                print("[MAIL] SendGrid accepted:", subject, "->", to_email)
                return True
            print("[MAIL] SendGrid failed:", r.status_code, getattr(r, "text", ""))
            return False
        else:
            # Minimal fallback without requests
            import urllib.request
            import urllib.error

            req = urllib.request.Request(
                "https://api.sendgrid.com/v3/mail/send",
                data=json.dumps(payload).encode("utf-8"),
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=10) as resp:
                ok = 200 <= resp.status < 300
                print("[MAIL] SendGrid accepted:", ok, subject, "->", to_email)
                return ok
    except Exception as e:
        print("[MAIL] SendGrid send failed:", e)
        return False


def _send_email_sync_mailgun(to_email: str, subject: str, html_body: str, text_body: str = "") -> bool:
    """Send email via Mailgun HTTP API. Returns True if Mailgun accepted the message."""
    api_key = os.getenv("MAILGUN_API_KEY", "").strip()
    domain = os.getenv("MAILGUN_DOMAIN", "").strip()
    if not api_key or not domain:
        return False

    # API base: US (default) or EU (set MAILGUN_BASE_URL=https://api.eu.mailgun.net)
    base_url = (os.getenv("MAILGUN_BASE_URL", "https://api.mailgun.net").strip().rstrip("/"))
    endpoint = f"{base_url}/v3/{domain}/messages"

    from_email = (os.getenv("MAILGUN_FROM", "").strip() or os.getenv("MAIL_FROM", "").strip() or os.getenv("SMTP_FROM", "").strip() or SMTP_USER).strip()
    if not from_email:
        return False

    data = {
        "from": f"Zenith Learning <{from_email}>",
        "to": [to_email],
        "subject": subject,
        "text": text_body or " ",
        "html": html_body,
    }

    try:
        import requests  # type: ignore
    except Exception:
        requests = None

    try:
        if requests:
            r = requests.post(
                endpoint,
                auth=("api", api_key),
                data=data,
                timeout=10,
            )
            if 200 <= r.status_code < 300:
                print("[MAIL] Mailgun accepted:", subject, "->", to_email)
                return True
            print("[MAIL] Mailgun failed:", r.status_code, getattr(r, "text", ""))
            return False
        else:
            # Minimal fallback without requests
            import urllib.request
            import urllib.parse
            import base64

            encoded = urllib.parse.urlencode({k: (v[0] if isinstance(v, list) else v) for k, v in data.items()}).encode("utf-8")
            auth_header = base64.b64encode(f"api:{api_key}".encode("utf-8")).decode("ascii")
            req = urllib.request.Request(
                endpoint,
                data=encoded,
                headers={"Authorization": f"Basic {auth_header}", "Content-Type": "application/x-www-form-urlencoded"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=10) as resp:
                code = getattr(resp, "status", 200)
                if 200 <= code < 300:
                    print("[MAIL] Mailgun accepted:", subject, "->", to_email)
                    return True
                print("[MAIL] Mailgun failed:", code)
                return False
    except Exception as e:
        print("[MAIL] Mailgun send failed:", e)
        return False



def _is_render_env() -> bool:
    """Detect Render hosted environment."""
    return bool(
        os.getenv("RENDER")  # sometimes "true"
        or os.getenv("RENDER_SERVICE_ID")
        or os.getenv("RENDER_EXTERNAL_URL")
        or os.getenv("RENDER_INSTANCE_ID")
    )

def _preferred_mail_provider() -> str:
    """Always use SMTP (Google Workspace)."""
    return "smtp"

def _send_email(
    to_email: str,
    subject: str,
    html_body: str,
    text_body: str = "",
    *,
    kind: str = "",
    reply_to: str = None,
):
    """Send email on a background thread (SMTP only)."""
    if not to_email:
        return

    from_email = _pick_from(kind)

    def _job():
        # Optional fallback: SendGrid if configured (useful if SMTP is blocked by host)
        if os.getenv("SENDGRID_API_KEY", "").strip():
            if _send_email_sync_sendgrid(to_email, subject, html_body, text_body):
                return
        _send_email_sync_smtp(to_email, subject, html_body, text_body, from_email=from_email, reply_to=reply_to)

    try:
        import threading
        t = threading.Thread(target=_job, daemon=True)
        t.start()
    except Exception as e:
        print("[MAIL] Could not spawn mail thread:", e)
        _job()

def _brand_email(title: str, preheader: str = "", body_html: str = "", primary_cta: dict = None, secondary_cta: dict = None):
    """Return a professional, branded email HTML."""
    logo_text = "Zenith Learning"
    year = datetime.now().year
    primary_btn = ""
    if primary_cta and primary_cta.get("url") and primary_cta.get("label"):
        primary_btn = f"""
        <a href="{primary_cta.get('url')}" style="display:inline-block;background:#2563eb;color:#ffffff;text-decoration:none;padding:12px 18px;border-radius:12px;font-weight:700;font-size:14px;">
          {primary_cta.get('label')}
        </a>"""
    secondary_btn = ""
    if secondary_cta and secondary_cta.get("url") and secondary_cta.get("label"):
        secondary_btn = f"""
        <a href="{secondary_cta.get('url')}" style="display:inline-block;background:#111827;color:#ffffff;text-decoration:none;padding:12px 18px;border-radius:12px;font-weight:700;font-size:14px;">
          {secondary_cta.get('label')}
        </a>"""

    cta_row = ""
    if primary_btn or secondary_btn:
        cta_row = f"<tr><td style='padding:12px 24px 22px 24px;'>{primary_btn} &nbsp; {secondary_btn}</td></tr>"

    primary_url = (primary_cta.get('url') if primary_cta else "") or ""

    html = f"""<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>{title}</title>
  </head>
  <body style="margin:0;padding:0;background:#f6f7fb;font-family:Inter,system-ui,-apple-system,Segoe UI,Roboto,Arial,sans-serif;color:#111827;">
    <div style="display:none;max-height:0;overflow:hidden;opacity:0;color:transparent;">{preheader}</div>

    <table width="100%" cellspacing="0" cellpadding="0" style="background:#f6f7fb;padding:28px 10px;">
      <tr>
        <td align="center">
          <table width="640" cellspacing="0" cellpadding="0" style="background:#ffffff;border-radius:18px;overflow:hidden;box-shadow:0 10px 30px rgba(17,24,39,0.08);">
            <tr>
              <td style="background:linear-gradient(135deg,#0ea5e9,#2563eb);padding:22px 24px;">
                <div style="font-size:16px;font-weight:800;color:#ffffff;letter-spacing:0.2px;">{logo_text}</div>
                <div style="font-size:12px;color:rgba(255,255,255,0.9);margin-top:4px;">Smart learning • Roadmaps • Quizzes • Progress</div>
              </td>
            </tr>

            <tr>
              <td style="padding:26px 24px 6px 24px;">
                <div style="font-size:20px;font-weight:800;line-height:1.25;">{title}</div>
                <div style="font-size:13px;color:#6b7280;margin-top:8px;">{preheader}</div>
              </td>
            </tr>

            <tr>
              <td style="padding:10px 24px 6px 24px;font-size:14px;line-height:1.65;color:#111827;">
                {body_html}
              </td>
            </tr>

            {cta_row}

            <tr>
              <td style="padding:0 24px 22px 24px;">
                <div style="border-top:1px solid #e5e7eb;padding-top:14px;font-size:12px;color:#6b7280;line-height:1.6;">
                  Need help? Reply to this email or contact our team from the <b>Contact</b> page in the app.<br/>
                  <span style="color:#9ca3af;">© {year} Zenith Learning. All rights reserved.</span>
                </div>
              </td>
            </tr>
          </table>

          <div style="width:640px;font-size:12px;color:#9ca3af;line-height:1.5;margin-top:10px;text-align:center;">
            If the button doesn't work, copy and paste this link in your browser:<br/>
            <span style="word-break:break-all;">{primary_url}</span>
          </div>
        </td>
      </tr>
    </table>
  </body>
</html>"""
    return html

def _safe_public_url(path: str) -> str:
    """
    Always return an ABSOLUTE URL for emails.
    Priority:
    1) FRONTEND_BASE_URL env (recommended)
    2) FRONTEND_URL env
    3) Fallback to request Origin (if available)
    4) Last resort: return path (will not work in email clients)
    """
    base = (os.getenv("FRONTEND_BASE_URL") or os.getenv("FRONTEND_URL") or "").strip().rstrip("/")

    # best-effort fallback (sometimes request has Origin)
    if not base:
        try:
            origin = (request.headers.get("Origin") or "").strip().rstrip("/")
            if origin:
                base = origin
        except Exception:
            pass

    if not path.startswith("/"):
        path = "/" + path

    return (base + path) if base else path

IST = timezone(timedelta(hours=5, minutes=30))

def _now_ist_str():
    # Example: 2026-02-06 01:10 AM IST
    return datetime.now(IST).strftime("%Y-%m-%d %I:%M %p IST")



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
    """Verify token + allow only the fixed admin mailbox (ADMIN_EMAIL)."""
    user, err = require_user()
    if err:
        return None, err

    try:
        email = (user.get("email") or "").strip().lower()
        if email != (ADMIN_EMAIL or "").strip().lower():
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

    # ✅ Canonicalize by email to avoid duplicate Mongo users when the same person logs in via password + SSO.
    email_norm = (email or "").strip().lower()
    if email_norm:
        # Upsert by email (unique), then attach latest Firebase uid/provider/name/photo
        res = db.users.update_one(
            {"email": email_norm},
            {"$set": {
                "uid": uid,
                "email": email_norm,
                "name": name,
                "photoURL": photoURL,
                "providerId": providerId,
                "updatedAt": now,
            },
             # role ONLY on first insert
             "$setOnInsert": {"createdAt": now}},
            upsert=True
        )
    else:
        # Fallback (rare): no email available -> upsert by uid
        res = db.users.update_one(
        {"email": (email or "").strip().lower()} if (email or "").strip() else {"uid": uid},
            {"$set": {
                "uid": uid,
                "email": email_norm,
                "name": name,
                "photoURL": photoURL,
                "providerId": providerId,
                "updatedAt": now,
            },
             "$setOnInsert": {"createdAt": now}},
            upsert=True
        )

    # ✅ Send welcome email for SSO (Google) only for first-time sign-in
    try:
        is_new = bool(getattr(res, "upserted_id", None))
        if is_new and (providerId or "").lower().startswith("google"):
            # Avoid duplicates if user doc already has the flag
            udoc = db.users.find_one({"email": (email or "").strip().lower()} if (email or "").strip() else {"uid": uid}, projection={"_id": 0, "welcomeSsoSent": 1, "name": 1}) or {}
            if not udoc.get("welcomeSsoSent"):
                home_url = _safe_public_url("/")
                body = f"""
                <p style="margin:0 0 10px 0;">Hi <b>{(name or 'there')}</b>,</p>
                <p style="margin:0 0 10px 0;">
                  Welcome to <b>Zenith Learning</b>! Your Google sign-in is set up and you're ready to start learning.
                </p>
                <p style="margin:0 0 10px 0;">Here are a few quick tips to get the best experience:</p>
                <ul style="margin:10px 0 10px 20px;">
                  <li>Create a roadmap to structure your learning in weeks</li>
                  <li>Complete quizzes after each video to unlock the next content</li>
                  <li>Track progress in <b>My Courses</b> and continue anytime</li>
                </ul>
                """
                html = _brand_email(
                    "Welcome to Zenith Learning 🎉",
                    "Your Google sign-in is ready — begin your roadmap today.",
                    body,
                    primary_cta={"label": "Start learning", "url": home_url},
                    secondary_cta={"label": "Contact support", "url": _safe_public_url("/contact")}
                )
                _send_email(email, "Welcome to Zenith Learning", html, kind="auth")
                db.users.update_one({"email": (email or "").strip().lower()} if (email or "").strip() else {"uid": uid}, {"$set": {"welcomeSsoSent": True, "updatedAt": now}})
    except Exception as _e:
        pass


    user_doc = db.users.find_one({"email": (email or "").strip().lower()} if (email or "").strip() else {"uid": uid}, {"_id": 0})
    return jsonify({
        "ok": True,
        "user": user_doc
    })

    
# ----------------- AUTH EMAIL FLOWS (Verification + Password reset) -----------------

def _new_token() -> str:
    return uuid.uuid4().hex + uuid.uuid4().hex  # 64 chars

@app.route("/auth/send-verification", methods=["POST"])
def auth_send_verification():
    """
    Send a custom verification email (SMTP) for password-based signups.
    Requires Firebase ID token. We DO NOT create accounts here; we simply verify/activate.
    """
    user, err = require_user()
    if err:
        msg, code = err
        return jsonify({"error": msg}), code

    email = user.get("email") or ""
    uid = user.get("uid") or ""
    if not email or not uid:
        return jsonify({"error": "email/uid missing"}), 400

    db = get_db()
    now = datetime.now(timezone.utc)

    # ✅ Ensure Mongo user doc exists (canonical by email to prevent duplicates)
    try:
        email_norm = (email or "").strip().lower()
        filt = {"email": email_norm} if email_norm else {"uid": uid}
        db.users.update_one(
            filt,
            {"$set": {
                "uid": uid,
                "email": email_norm,
                "name": (user.get("name") or ""),
                "photoURL": (user.get("picture") or user.get("photoURL") or ""),
                "providerId": "password",
                "updatedAt": now,
            }, "$setOnInsert": {"createdAt": now}},
            upsert=True
        )
    except Exception as e:
        print(f"[WARN] Mongo upsert during send-verification failed: {e}")

    # If already verified, avoid re-sending
    try:
        _init_firebase_admin()
        u = fb_auth.get_user(uid)
        if getattr(u, "email_verified", False):
            return jsonify({"ok": True, "alreadyVerified": True})
    except Exception:
        pass

    token = _new_token()
    # Store token
    db.email_verifications.insert_one({
        "token": token,
        "uid": uid,
        "email": email,
        "used": False,
        "createdAt": now,
        "expiresAt": now + timedelta(hours=24),
    })

    verify_url = _safe_public_url(f"/verify-email?token={token}")
    body = f"""
    <p style="margin:0 0 10px 0;">Hi <b>{(user.get('name') or 'there')}</b>,</p>
    <p style="margin:0 0 10px 0;">
      Thanks for signing up for <b>Zenith Learning</b>. To activate your account and start saving courses and progress,
      please verify your email address.
    </p>
    <ul style="margin:10px 0 10px 20px;">
      <li>This verification link is valid for <b>24 hours</b>.</li>
      <li>If you didn’t create this account, you can safely ignore this email.</li>
    </ul>
    <p style="margin:10px 0 0 0;">Click the button below to continue.</p>
    """
    html = _brand_email(
        "Verify your email to activate your Zenith account",
        "One quick step to activate your account and start learning.",
        body,
        primary_cta={"label": "Open verification page", "url": verify_url},
    )
    _send_email(email, "Verify your Zenith Learning email", html, kind="auth")
    return jsonify({"ok": True})

@app.route("/auth/verify-email", methods=["POST"])
def auth_verify_email():
    """
    Verify token, then mark Firebase user as emailVerified.
    Also sends a welcome email (manual signup) exactly once.
    """
    data = request.get_json() or {}
    token = (data.get("token") or "").strip()
    if not token:
        return jsonify({"error": "token required"}), 400

    db = get_db()
    now = datetime.now(timezone.utc)


    rec = db.email_verifications.find_one({"token": token})
    if not rec:
        return jsonify({"error": "Invalid or expired token"}), 400
    if rec.get("used"):
        return jsonify({"ok": True, "alreadyUsed": True})
    exp = _to_utc_aware(rec.get("expiresAt"))
    if exp and isinstance(exp, datetime) and exp < now:
        return jsonify({"error": "Token expired"}), 400

    uid = rec.get("uid")
    email = rec.get("email")

    # ✅ Ensure user exists in MongoDB even if the user verified before first login
    db.users.update_one(
        {"uid": uid},
        {"$set": {"uid": uid, "email": email, "updatedAt": now},
         "$setOnInsert": {"createdAt": now, "providerId": "password"}},
        upsert=True
    )

    try:
        _init_firebase_admin()
        fb_auth.update_user(uid, email_verified=True)
    except Exception as e:
        return jsonify({"error": f"Firebase update failed: {e}"}), 500

    db.email_verifications.update_one({"token": token}, {"$set": {"used": True, "usedAt": now}})

    # Welcome email for manual signup (send only once)
    user_doc = db.users.find_one({"email": (email or "").strip().lower()} if (email or "").strip() else {"uid": uid}, projection={"_id": 0}) or {}
    if not user_doc.get("welcomeManualSent"):
        home_url = _safe_public_url("/")
        body = f"""
        <p style="margin:0 0 10px 0;">Hi <b>{(user_doc.get('name') or 'there')}</b>,</p>
        <p style="margin:0 0 10px 0;">
          Your email is verified ✅. Welcome to <b>Zenith Learning</b>!
        </p>
        <p style="margin:0 0 10px 0;">
          Here’s what you can do next:
        </p>
        <ul style="margin:10px 0 10px 20px;">
          <li>Create a personalized learning roadmap</li>
          <li>Track video progress and quiz performance</li>
          <li>Resume anytime from <b>My Courses</b></li>
          <li>Use Notes to save important points</li>
        </ul>
        <p style="margin:10px 0 0 0;">Ready to continue?</p>
        """
        html = _brand_email(
            "Welcome to Zenith Learning 🎉",
            "Your account is active. Let’s start learning.",
            body,
            primary_cta={"label": "Go to Zenith", "url": home_url},
            secondary_cta={"label": "Contact support", "url": _safe_public_url("/contact")}
        )
        _send_email(email, "Welcome to Zenith Learning", html, kind="auth")
        db.users.update_one({"email": (email or "").strip().lower()} if (email or "").strip() else {"uid": uid}, {"$set": {"welcomeManualSent": True, "updatedAt": now}}, upsert=True)

    return jsonify({"ok": True})

@app.route("/auth/password-reset/request", methods=["POST"])
def auth_password_reset_request():
    """
    Send a password reset email using SMTP.
    Always returns ok to avoid account enumeration.
    """
    data = request.get_json() or {}
    email = (data.get("email") or "").strip().lower()
    if not email:
        return jsonify({"error": "email required"}), 400

    db = get_db()
    now = datetime.now(timezone.utc)


    token = _new_token()

    try:
        _init_firebase_admin()
        u = fb_auth.get_user_by_email(email)
        uid = u.uid
    except Exception:
        # Return ok even if not found
        return jsonify({"ok": True})

    db.password_resets.insert_one({
        "token": token,
        "uid": uid,
        "email": email,
        "used": False,
        "createdAt": now,
        "expiresAt": now + timedelta(hours=1),
    })

    reset_url = _safe_public_url(f"/reset-password?token={token}")
    body = f"""
    <p style="margin:0 0 10px 0;">Hi,</p>
    <p style="margin:0 0 10px 0;">
      We received a request to reset the password for your Zenith Learning account (<b>{email}</b>).
    </p>
    <p style="margin:0 0 10px 0;">
      If you initiated this request, click the button below to set a new password.
      This link is valid for <b>1 hour</b>.
    </p>
    <ul style="margin:10px 0 10px 20px;">
      <li>If you did not request a reset, you can ignore this email.</li>
      <li>For security, never share your password with anyone.</li>
    </ul>
    """
    html = _brand_email(
        "Reset your Zenith Learning password",
        "Use the button below to set a new password (valid for 1 hour).",
        body,
        primary_cta={"label": "Reset password", "url": reset_url},
    )
    _send_email(email, "Reset your Zenith Learning password", html, kind="auth")
    return jsonify({"ok": True})

@app.route("/auth/password-reset/confirm", methods=["POST"])
def auth_password_reset_confirm():
    data = request.get_json() or {}
    token = (data.get("token") or "").strip()
    new_password = (data.get("newPassword") or "").strip()
    if not token or not new_password:
        return jsonify({"error": "token and newPassword required"}), 400
    if len(new_password) < 6:
        return jsonify({"error": "Password must be at least 6 characters"}), 400

    db = get_db()
    now = datetime.now(timezone.utc)

    rec = db.password_resets.find_one({"token": token})
    if not rec:
        return jsonify({"error": "Invalid or expired token"}), 400
    if rec.get("used"):
        return jsonify({"error": "Token already used"}), 400
    exp = _to_utc_aware(rec.get("expiresAt"))
    if exp and isinstance(exp, datetime) and exp < now:
        return jsonify({"error": "Token expired"}), 400

    uid = (rec.get("uid") or "").strip()
    email = (rec.get("email") or "").strip().lower()

    if not uid:
        return jsonify({"error": "Invalid reset record (uid missing)"}), 400

    # ✅ Ensure user exists in MongoDB
    db.users.update_one(
        {"uid": uid},
        {"$set": {"uid": uid, "email": email, "updatedAt": now},
         "$setOnInsert": {"createdAt": now, "providerId": "password"}},
        upsert=True
    )

    # ✅ Prevent using the same password again (compare with stored hash)
    try:
        user_doc = db.users.find_one({"uid": uid}, projection={"_id": 0, "passwordHash": 1}) or {}
        old_hash = (user_doc.get("passwordHash") or "").strip()
        new_hash = _pw_hash(uid, new_password)

        # If we have old hash and it's same => block
        if old_hash and old_hash == new_hash:
            return jsonify({
                "error": "New password cannot be the same as your old password. Please choose a different password."
            }), 400
    except Exception:
        # don't fail reset if hash check fails unexpectedly
        pass

    # ✅ Update Firebase password
    try:
        _init_firebase_admin()
        fb_auth.update_user(uid, password=new_password)
    except Exception as e:
        return jsonify({"error": f"Password update failed: {e}"}), 500

    # ✅ Mark token used
    db.password_resets.update_one({"token": token}, {"$set": {"used": True, "usedAt": now}})

    # ✅ Save latest password hash (for next-time reuse detection)
    try:
        db.users.update_one(
            {"uid": uid},
            {"$set": {"passwordHash": _pw_hash(uid, new_password), "updatedAt": now}},
            upsert=True
        )
    except Exception:
        pass

    # ✅ Confirmation email
    body = f"""
    <p style="margin:0 0 10px 0;">Hi,</p>
    <p style="margin:0 0 10px 0;">
      Your Zenith Learning password has been successfully updated for <b>{email}</b>.
    </p>
    <p style="margin:0 0 10px 0;">
      If you didn’t make this change, please reset your password again immediately and contact support.
    </p>
    """
    html = _brand_email(
        "Your password was updated",
        "Your password reset is complete.",
        body,
        primary_cta={"label": "Login to Zenith", "url": _safe_public_url("/login")},
        secondary_cta={"label": "Contact support", "url": _safe_public_url("/contact")}
    )
    _send_email(email, "Zenith Learning — Password updated", html, kind="auth")
    return jsonify({"ok": True})

@app.route("/contact", methods=["POST"])
def contact_send():
    data = request.get_json() or {}
    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip()
    subject = (data.get("subject") or "Contact request").strip()
    message = (data.get("message") or "").strip()

    if not name or not email or not message:
        return jsonify({"error": "name, email and message are required"}), 400

    # Admin mail
    admin_subject = f"[Zenith Contact] {subject}"
    body_admin = f"""
    <p style="margin:0 0 10px 0;">You received a new message from the Zenith Contact form.</p>
    <table style="border-collapse:collapse;font-size:14px;">
      <tr><td style="padding:6px 10px;border:1px solid #e5e7eb;"><b>Name</b></td><td style="padding:6px 10px;border:1px solid #e5e7eb;">{name}</td></tr>
      <tr><td style="padding:6px 10px;border:1px solid #e5e7eb;"><b>Email</b></td><td style="padding:6px 10px;border:1px solid #e5e7eb;">{email}</td></tr>
      <tr><td style="padding:6px 10px;border:1px solid #e5e7eb;"><b>Subject</b></td><td style="padding:6px 10px;border:1px solid #e5e7eb;">{subject}</td></tr>
    </table>
    <p style="margin:12px 0 6px 0;"><b>Message:</b></p>
    <div style="white-space:pre-wrap;background:#f9fafb;border:1px solid #e5e7eb;border-radius:12px;padding:12px;">{message}</div>
    """
    html_admin = _brand_email(
        "New Contact Form Message",
        "A user submitted a message via the Contact page.",
        body_admin,
        primary_cta={"label": "Open Zenith", "url": _safe_public_url("/")},
    )
    _send_email(CONTACT_INBOX, admin_subject, html_admin, kind="contact", reply_to=email)

    # User acknowledgement
    body_user = f"""
    <p style="margin:0 0 10px 0;">Hi <b>{name}</b>,</p>
    <p style="margin:0 0 10px 0;">
      Thanks for reaching out to <b>Zenith Learning</b>. We’ve received your message and our team will respond as soon as possible.
    </p>
    """
    html_user = _brand_email(
        "We received your message",
        "Thanks for contacting Zenith Learning — we’ll reply soon.",
        body_user,
        primary_cta={"label": "Back to Zenith", "url": _safe_public_url("/")},
    )
    _send_email(email, "Zenith Learning — We received your message", html_user, kind="contact")

    return jsonify({"ok": True})


# ----------------- PROFILE (EXTRA FIELDS + LOCAL PHOTO) -----------------
# --- Profile update email helpers ---
_PROFILE_FIELD_LABELS = {
    "name": "Name",
    "dob": "Date of Birth",
    "education": "Education",
    "college": "College",
    "degree": "Degree",
    "department": "Department",
    "yearBatch": "Batch / Year",
    "year": "Year",
    "phone": "Phone",
    "location": "Location",
    "bio": "Bio",
    "photoURL": "Profile Photo (URL)",
    "photoLocalURL": "Profile Photo",
}

def _norm_profile_val(v):
    if v is None:
        return ""
    if isinstance(v, str):
        return v.strip()
    # keep numbers/bools as-is but stringify for comparisons
    return str(v).strip()

def _profile_change_rows(before: dict, after_partial: dict):
    """
    Compute change rows ONLY for fields present in `after_partial` (i.e., what client attempted to write).
    Returns list of dicts: {field,label,change,old,new}
    """
    rows = []
    before = before or {}
    for k, new_v in (after_partial or {}).items():
        if k in ("updatedAt",):
            continue
        old_v = _norm_profile_val(before.get(k, ""))
        new_vn = _norm_profile_val(new_v)
        if old_v == new_vn:
            continue

        if old_v and not new_vn:
            change = "Deleted"
        elif (not old_v) and new_vn:
            change = "Added"
        else:
            change = "Updated"

        rows.append({
            "field": k,
            "label": _PROFILE_FIELD_LABELS.get(k, k),
            "change": change,
            "old": old_v,
            "new": new_vn,
        })
    return rows

def _send_profile_update_email(to_email: str, name: str, rows: list, when_ist: str, cta_url: str = ""):
    """Send a profile update email listing only changed fields."""
    if not to_email or not rows:
        return

    # Build rows table
    tr_html = ""
    for r in rows:
        new_disp = r["new"] if r["change"] != "Deleted" else "—"
        # Avoid super-long bio blobs in email tables
        if r["field"] == "bio" and len(new_disp) > 140:
            new_disp = new_disp[:140].rstrip() + "…"
        if r["field"] in ("photoLocalURL", "photoURL"):
            # don't dump long urls; indicate status
            if r["change"] == "Deleted":
                new_disp = "Removed"
            else:
                new_disp = "Updated"

        tr_html += f"""
        <tr>
          <td style="padding:8px 10px;border:1px solid #e5e7eb;"><b>{r['label']}</b></td>
          <td style="padding:8px 10px;border:1px solid #e5e7eb;">{r['change']}</td>
          <td style="padding:8px 10px;border:1px solid #e5e7eb;word-break:break-word;">{new_disp}</td>
        </tr>
        """

    body = f"""
    <p style="margin:0 0 10px 0;">Hi <b>{(name or 'there').strip()}</b>,</p>
    <p style="margin:0 0 12px 0;">Your Zenith profile was updated on <b>{when_ist}</b>. Here’s what changed:</p>

    <table style="border-collapse:collapse;font-size:14px;width:100%;max-width:560px;">
      <tr>
        <td style="padding:8px 10px;border:1px solid #e5e7eb;background:#f9fafb;"><b>Field</b></td>
        <td style="padding:8px 10px;border:1px solid #e5e7eb;background:#f9fafb;"><b>Change</b></td>
        <td style="padding:8px 10px;border:1px solid #e5e7eb;background:#f9fafb;"><b>New value</b></td>
      </tr>
      {tr_html}
    </table>

    <p style="margin:14px 0 0 0;color:#6b7280;font-size:13px;">
      If you didn’t make this change, please reset your password and contact support.
    </p>
    """

    html = _brand_email(
        "Profile updated",
        "Your Zenith profile details were updated.",
        body,
        primary_cta={"label": "Open Profile", "url": (cta_url or _safe_public_url("/profile"))},
    )
    _send_email(to_email, "Zenith Learning — Profile updated", html, kind="profile")


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

    db = get_db()
    uid = user["uid"]

    # Read previous state so we can email ONLY what changed
    before = db.users.find_one({"uid": uid}, {"_id": 0}) or {}

    # Compute change rows BEFORE we add updatedAt
    rows = _profile_change_rows(before, update)

    now = datetime.now(timezone.utc)
    update["updatedAt"] = now

    db.users.update_one({"uid": uid}, {"$set": update}, upsert=True)
    doc = db.users.find_one({"uid": uid}, {"_id": 0})

    # Send profile update email (only if there were changes)
    try:
        to_email = (user.get("email") or (doc or {}).get("email") or before.get("email") or "").strip()
        display_name = (doc or {}).get("name") or update.get("name") or before.get("name") or ""
        if to_email and rows:
            _send_profile_update_email(
                to_email=to_email,
                name=display_name,
                rows=rows,
                when_ist=_now_ist_str(),
                cta_url=_safe_public_url("/profile"),
            )
    except Exception as e:
        print("[MAIL] profile update email failed:", e)

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
        mt = (f.mimetype or "").lower()
        if "jpeg" in mt or "jpg" in mt:
            ext = ".jpg"
        elif "png" in mt:
            ext = ".png"
        elif "webp" in mt:
            ext = ".webp"

    if ext not in ALLOWED_IMAGE_EXTS:
        return jsonify({"error": "Only JPG / PNG / WEBP allowed"}), 400

    # Read current avatar state (for delete + email diff)
    current = db.users.find_one(
        {"uid": uid},
        {"_id": 0, "avatarFileId": 1, "photoLocalURL": 1, "email": 1, "name": 1}
    ) or {}

    # Replace existing avatar (GridFS) if present
    old_fid = current.get("avatarFileId")
    if old_fid:
        try:
            fs.delete(ObjectId(old_fid))
        except Exception:
            pass

    # Store in GridFS
    content_type = (f.mimetype or "").strip() or "application/octet-stream"
    file_id = fs.put(f.stream.read(), filename=f"avatar_{uid}{ext}", contentType=content_type)
    public_url = _profile_avatar_url(uid)

    # Clean any old local file leftovers
    _remove_existing_avatar_files(uid)

    now = datetime.now(timezone.utc)
    db.users.update_one(
        {"uid": uid},
        {"$set": {
            "avatarFileId": str(file_id),
            "photoLocalURL": public_url,
            "photoURL": "",
            "updatedAt": now
        }},
        upsert=True,
    )

    doc = db.users.find_one({"uid": uid}, {"_id": 0}) or {}

    # ✅ Send email: profile photo updated (only mention photo)
    try:
        before = current or {}
        rows = _profile_change_rows(before, {"photoLocalURL": public_url})

        to_email = (user.get("email") or doc.get("email") or before.get("email") or "").strip()
        display_name = (doc.get("name") or before.get("name") or user.get("name") or "").strip()

        if to_email and rows:
            _send_profile_update_email(
                to_email=to_email,
                name=display_name,
                rows=rows,
                when_ist=_now_ist_str(),
                cta_url=_safe_public_url("/profile"),
            )
    except Exception as e:
        print("[MAIL] profile photo upload email failed:", e)

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

    # Read current avatar state (for email diff)
    current = db.users.find_one(
        {"uid": uid},
        {"_id": 0, "avatarFileId": 1, "photoLocalURL": 1, "email": 1, "name": 1}
    ) or {}

    # Delete from GridFS if present
    old_fid = current.get("avatarFileId")
    if old_fid:
        try:
            fs.delete(ObjectId(old_fid))
        except Exception:
            pass

    # Also remove any local leftovers
    _remove_existing_avatar_files(uid)

    now = datetime.now(timezone.utc)
    db.users.update_one(
        {"uid": uid},
        {"$set": {"photoLocalURL": "", "photoURL": "", "avatarFileId": "", "updatedAt": now}},
        upsert=True,
    )

    doc = db.users.find_one({"uid": uid}, {"_id": 0}) or {}

    # ✅ Send email: profile photo deleted (only mention photo)
    try:
        before = current or {}
        rows = _profile_change_rows(before, {"photoLocalURL": ""})

        to_email = (user.get("email") or doc.get("email") or before.get("email") or "").strip()
        display_name = (doc.get("name") or before.get("name") or user.get("name") or "").strip()

        if to_email and rows:
            _send_profile_update_email(
                to_email=to_email,
                name=display_name,
                rows=rows,
                when_ist=_now_ist_str(),
                cta_url=_safe_public_url("/profile"),
            )
    except Exception as e:
        print("[MAIL] profile photo delete email failed:", e)

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

    # ✅ Detect first-time course creation (for enrolled email)
    existing_course = db.course_states.find_one(
        {"uid": user["uid"], "courseTitle": courseTitle, "formHash": h},
        projection={"_id": 1}
    )


    db.course_states.update_one(
        {"uid": user["uid"], "courseTitle": courseTitle, "formHash": h},
        {"$set": {"uid": user["uid"], "courseTitle": courseTitle, "formHash": h, "formData": formData, "roadmap": roadmap, "videos": videos, "updatedAt": now},
         "$setOnInsert": {"createdAt": now}},
        upsert=True
    )


    # ✅ Course enrolled email (send only on first insert)
    if not existing_course:
        try:
            to_email = user.get("email") or ""
            course_id = hashlib.sha1(f"{user['uid']}|{courseTitle}|{h}".encode("utf-8")).hexdigest()[:12]
            body = f"""
            <p style="margin:0 0 10px 0;">Hi <b>{(user.get('name') or 'there')}</b>,</p>
            <p style="margin:0 0 10px 0;">
              You’re enrolled in a new course on <b>Zenith Learning</b>.
              Your roadmap and videos are ready.
            </p>
            <ul style="margin:10px 0 10px 20px;">
              <li><b>Course:</b> {courseTitle}</li>
              <li><b>Course ID:</b> {course_id}</li>
              <li><b>Quiz Result Time (IST):</b> {_now_ist_str()}</li>
            </ul>
            <p style="margin:10px 0 0 0;">Open the course to continue:</p>
            """
            open_url = _safe_public_url(f"/course/{courseTitle}/form")
            html = _brand_email(
                "Course enrolled — your roadmap is ready",
                f"You enrolled in {courseTitle}. Open your roadmap and start learning.",
                body,
                primary_cta={"label": "Open course", "url": open_url},
                secondary_cta={"label": "View My Courses", "url": _safe_public_url("/my-courses")}
            )
            _send_email(to_email, f"Zenith Learning — Enrolled: {courseTitle}", html, kind="courses")
        except Exception:
            pass


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

    # ✅ send unenrolled mail (before deleting data)
    try:
        to_email = (user.get("email") or "").strip()
        uname = user.get("name") or "there"
        when_ist = _now_ist_str()

        body = f"""
        <p style="margin:0 0 10px 0;">Hi <b>{uname}</b>,</p>
        <p style="margin:0 0 10px 0;">
          You have discontinued (unenrolled) from the course below on <b>Zenith Learning</b>.
        </p>
        <ul style="margin:10px 0 10px 20px;">
          <li><b>Course:</b> {course_title}</li>
          <li><b>Unenrolled at:</b> {when_ist}</li>
        </ul>
        <p style="margin:10px 0 0 0;">
          You can enroll again anytime from <b>My Courses</b>.
        </p>
        """

        html = _brand_email(
            "Course discontinued (Unenrolled)",
            "You have been unenrolled from a course on Zenith Learning.",
            body,
            primary_cta={"label": "View My Courses", "url": _safe_public_url("/my-courses")},
            secondary_cta={"label": "Contact support", "url": _safe_public_url("/contact")}
        )
        _send_email(to_email, f"Zenith Learning — Unenrolled: {course_title}", html, kind="courses")
    except Exception:
        pass

    db = get_db()

    db.course_states.delete_many({"uid": uid, "courseTitle": course_title})
    db.progress.delete_many({"uid": uid, "courseTitle": course_title})
    db.quiz_progress.delete_many({"uid": uid, "courseTitle": course_title})
    db.quizzes.delete_many({"uid": uid, "courseTitle": course_title})
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

    admin_email_lc = (ADMIN_EMAIL or "").strip().lower()

    users_out = []
    for u in db.users.find({}, projection={"_id": 0, "uid": 1, "email": 1, "name": 1}):
        uid = u.get("uid")
        email = (u.get("email") or "").strip()
        is_admin = email.lower() == admin_email_lc

        # ✅ Do not show learning progress for the admin mailbox
        if is_admin:
            users_out.append({
                "uid": uid,
                "email": email,
                "name": u.get("name"),
                "isAdmin": True,
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
            "email": email,
            "name": u.get("name"),
            "isAdmin": False,
            "courses": courses,
            "overallPercent": overall,
            "heldCourses": sorted(list(held_set)),
        })

    users_out.sort(key=lambda x: (not x.get("isAdmin"), x.get("email") or ""))
    return jsonify({"ok": True, "adminEmail": ADMIN_EMAIL, "users": users_out})


# ----------------- ADMIN: ROLE MANAGEMENT -----------------
@app.route("/admin/promote", methods=["POST"])
def admin_promote():
    return jsonify({"error": "Role management removed. Admin is fixed to ADMIN_EMAIL."}), 410


@app.route("/admin/demote", methods=["POST"])
def admin_demote():
    return jsonify({"error": "Role management removed. Admin is fixed to ADMIN_EMAIL."}), 410


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

    # ✅ fetch user's email + name before deletion
    target_doc = db.users.find_one(
        {"uid": target_uid},
        projection={"_id": 0, "email": 1, "name": 1}
    ) or {}

    target_email = (target_doc.get("email") or "").strip()
    target_name = (target_doc.get("name") or "there")

    # ✅ delete user data
    # remove user doc (uid is stored on the canonical email doc)
    db.users.delete_one({"uid": target_uid})
    if target_email:
        db.users.delete_one({"email": target_email.strip().lower()})
    db.course_states.delete_many({"uid": target_uid})
    db.course_progress.delete_many({"uid": target_uid})
    db.progress.delete_many({"uid": target_uid})
    db.quizzes.delete_many({"uid": target_uid})
    db.transcripts.delete_many({"uid": target_uid})
    db.summaries.delete_many({"uid": target_uid})
    db.course_holds.delete_many({"uid": target_uid})


    # ✅ delete from Firebase Auth too
    try:
        _init_firebase_admin()
        try:
            fb_auth.delete_user(target_uid)
        except Exception:
            # fallback: if uid not found but email exists, try delete by email
            if target_email:
                u = fb_auth.get_user_by_email(target_email)
                fb_auth.delete_user(u.uid)
    except Exception as e:
        print(f"[WARN] Firebase delete failed for {target_uid}: {e}")

    # ✅ send account removed email (after deletion is ok, but use saved email)
    try:
        when_ist = _now_ist_str()
        body = f"""
        <p style="margin:0 0 10px 0;">Hi <b>{target_name}</b>,</p>
        <p style="margin:0 0 10px 0;">
          Your <b>Zenith Learning</b> account has been removed by the administrator.
        </p>
        <ul style="margin:10px 0 10px 20px;">
          <li><b>Removed at:</b> {when_ist}</li>
        </ul>
        <p style="margin:10px 0 0 0;">
          If you believe this was a mistake, please contact support.
        </p>
        """
        html = _brand_email(
            "Your Zenith account has been removed",
            "Your account was removed by the administrator.",
            body,
            primary_cta={"label": "Contact support", "url": _safe_public_url("/contact")},
            secondary_cta={"label": "Open Zenith", "url": _safe_public_url("/")}
        )
        _send_email(target_email, "Zenith Learning — Account removed", html, kind="admin")
    except Exception:
        pass

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

    # ✅ Notify user (admin action)
    try:
        udoc = db.users.find_one({"uid": uid}, projection={"_id": 0, "email": 1, "name": 1}) or {}
        to_email = (udoc.get("email") or "").strip()
        if to_email:
            uname = udoc.get("name") or "there"
            status = "ON HOLD" if held else "ACTIVE"
            body = f"""
            <p style="margin:0 0 10px 0;">Hi <b>{uname}</b>,</p>
            <p style="margin:0 0 10px 0;">
              Your course access has been updated by the admin on <b>Zenith Learning</b>.
            </p>
            <ul style="margin:10px 0 10px 20px;">
              <li><b>Course:</b> {courseTitle}</li>
              <li><b>Status:</b> <b>{status}</b></li>
              <li><b>Updated at (IST):</b> {_now_ist_str()}</li>
            </ul>
            <p style="margin:10px 0 0 0;">If you think this is a mistake, contact support.</p>
            """
            html = _brand_email(
                f"Course status updated — {status}",
                f"Course: {courseTitle} • Status: {status}",
                body,
                primary_cta={"label": "Open My Courses", "url": _safe_public_url("/my-courses")},
                secondary_cta={"label": "Contact support", "url": _safe_public_url("/contact")},
            )
            _send_email(to_email, f"Zenith Learning — Course {status}: {courseTitle}", html, kind="admin")
    except Exception:
        pass

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

    users = {u["uid"]: u for u in db.users.find({}, projection={"_id": 0, "uid": 1, "email": 1, "name": 1})}

    # quiz progress is stored in course_progress collection
    rows = []
    for cp in db.course_progress.find({}, projection={"_id": 0, "uid": 1, "courseTitle": 1, "quizPassedMap": 1, "updatedAt": 1}):
        uid = cp.get("uid")
        ct = cp.get("courseTitle")
        u = users.get(uid) or {}
        email_lc = (u.get("email") or "").strip().lower()
        if email_lc == (ADMIN_EMAIL or "").strip().lower():
            continue

        total = int(totals.get(ct, 0))
        passed = count_true(cp.get("quizPassedMap") or {})
        pct = int(round((passed / total) * 100)) if total else 0

        rows.append({
            "uid": uid,
            "name": u.get("name"),
            "email": u.get("email"),
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


    # ✅ Course completion email (send once when all quizzes/videos are completed)
    try:
        # determine total videos from course_states
        cs = db.course_states.find_one({"uid": user["uid"], "courseTitle": courseTitle}, projection={"_id": 0, "videos": 1}) or {}
        def _count_videos(obj):
            if obj is None:
                return 0
            if isinstance(obj, list):
                return sum(_count_videos(it) for it in obj)
            if isinstance(obj, dict):
                if isinstance(obj.get("videos"), list):
                    return len(obj.get("videos"))
                if "video" in obj and ("topic" in obj or "title" in obj):
                    return 1
                return sum(_count_videos(v) for v in obj.values())
            return 0
        total_videos = _count_videos(cs.get("videos"))
        passed_count = sum(1 for k,v in (quizPassedMap or {}).items() if v)
        completed_count = sum(1 for k,v in (quizCompletedMap or {}).items() if v)

        is_complete = (total_videos > 0) and (passed_count >= total_videos or completed_count >= total_videos)
        if is_complete:
            # Avoid duplicates
            course_key = hashlib.sha1(f"{user['uid']}|{courseTitle}".encode("utf-8")).hexdigest()
            already = db.course_completion_mails.find_one({"courseKey": course_key}, projection={"_id": 1})
            if not already:
                db.course_completion_mails.insert_one({"courseKey": course_key, "uid": user["uid"], "courseTitle": courseTitle, "createdAt": now})
                to_email = user.get("email") or ""
                body = f"""
                <p style="margin:0 0 10px 0;">Hi <b>{(user.get('name') or 'there')}</b>,</p>
                <p style="margin:0 0 10px 0;">
                  Congratulations — you have completed the course <b>{courseTitle}</b> on Zenith Learning 🎉
                </p>
                <ul style="margin:10px 0 10px 20px;">
                  <li><b>Total videos:</b> {total_videos}</li>
                  <li><b>Quizzes passed:</b> {passed_count}</li>
                  <li><b>Completed items:</b> {completed_count}</li>
                </ul>
                <p style="margin:10px 0 10px 0;">
                  Next steps:
                </p>
                <ul style="margin:10px 0 10px 20px;">
                  <li>Review your notes and revise weak areas</li>
                  <li>Try a new roadmap with a higher difficulty or faster pace</li>
                  <li>Share feedback through the Contact page</li>
                </ul>
                """
                html = _brand_email(
                    "Course completed ✅",
                    f"You completed {courseTitle}. Keep the momentum going.",
                    body,
                    primary_cta={"label": "View My Courses", "url": _safe_public_url("/my-courses")},
                    secondary_cta={"label": "Start a new course", "url": _safe_public_url("/")}
                )
                _send_email(to_email, f"Zenith Learning — Course Completed: {courseTitle}", html, kind="courses")
    except Exception:
        pass


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

        # derive course title if not provided
        if not courseTitle:
            courseTitle = derive_course_title_from_video(
                user.get("uid"), (quiz_doc.get("video_url") or "")
            ) or ""

        # block if course is held
        if courseTitle:
            blocked = block_if_held(user.get("uid"), courseTitle)
            if blocked:
                return blocked

        used = int(quiz_doc.get("attempts_used", 0))
        full_quiz = quiz_doc.get("full_quiz", [])

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

        # ✅ SEND QUIZ RESULT EMAIL (VIDEO = COURSE VIDEO NUMBER like 4/32, not YouTube id)
        try:
            to_email = (user.get("email") or "").strip()
            if to_email:
                status_line = "PASSED ✅" if passed else "NEEDS REATTEMPT ⚠️"
                video_url = (quiz_doc.get("video_url") or "").strip()

                # ✅ prefer frontend-provided video number (avoids off-by-one / ordering mismatches)
                req_video_no = data.get("video_no") or data.get("videoNo")
                req_total_videos = data.get("total_videos") or data.get("totalVideos")
                try:
                    req_video_no = int(req_video_no) if req_video_no is not None else None
                except Exception:
                    req_video_no = None
                try:
                    req_total_videos = int(req_total_videos) if req_total_videos is not None else None
                except Exception:
                    req_total_videos = None

                # ✅ derive video number (e.g., 4) and total (e.g., 32)
                video_no, total_videos = derive_video_number_from_course(
                    db=db,
                    uid=user.get("uid"),
                    course_title=courseTitle,
                    video_url=video_url
                )

                # If frontend provided a video number/total, trust it
                if req_video_no:
                    video_no = req_video_no
                if req_total_videos:
                    total_videos = req_total_videos

                # fallback
                youtube_id = _yt_id(video_url)

                video_label = f"#{video_no}" if video_no else (youtube_id or "N/A")
                video_label_full = (
                    f"{video_no}/{total_videos}"
                    if (video_no and total_videos)
                    else (str(video_no) if video_no else "N/A")
                )

                body = f"""
                <p style="margin:0 0 10px 0;">Hi <b>{user.get('name') or 'there'}</b>,</p>
                <p style="margin:0 0 10px 0;">Your quiz has been evaluated and your result is ready.</p>

                <ul style="margin:10px 0 10px 20px;">
                  <li><b>Course:</b> {courseTitle or 'N/A'}</li>
                  <li><b>Status:</b> <b>{status_line}</b></li>
                  <li><b>Score:</b> {score}/{len(full_quiz)} (Pass mark: {required})</li>
                  <li><b>Quiz Result Time (IST):</b> {_now_ist_str()}</li>
                  <li><b>Attempts used:</b> {used}</li>
                  <li><b>Video No:</b> {video_label_full}</li>
                  <li><b>Video:</b> {video_label}</li>
                  <li><b>Video Link:</b> {video_url or 'N/A'}</li>
                </ul>
                """

                html = _brand_email(
                    f"Quiz completed — {status_line}",
                    f"Course: {courseTitle or 'N/A'} • Score: {score}/{len(full_quiz)} • Video: {video_label}",
                    body,
                    primary_cta={"label": "View My Courses", "url": _safe_public_url("/my-courses")},
                    secondary_cta={"label": "Open Contact", "url": _safe_public_url("/contact")}
                )

                _send_email(
                    to_email,
                    f"Zenith Learning — Quiz Result ({status_line})",
                    html,
                    kind="courses"
                )
        except Exception:
            pass

        return jsonify({
            "score": score,
            "total": len(full_quiz),
            "required": required,
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
