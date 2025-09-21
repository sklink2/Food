#!/usr/bin/env python3
import requests
import pdfplumber
import re
import json
import os
from bs4 import BeautifulSoup
from datetime import datetime
from urllib.parse import urljoin, urlparse
from pathlib import Path

PAGE_URL = "https://www.lfchd.org/wp-content/uploads/2025/01/"
HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
}

from pathlib import Path
REPO_DIR = Path("/home/pi/inspections")           # your repo root
SAVE_DIR = REPO_DIR / "inspections"               # one folder for all JSONs

# Example row:
# 67372 #1 CHINA BUFFET 125 E. REYNOLDS ROAD, STE. 120 21-Feb-2025 REGULAR FOOD 93 15 39 41 48 56

DATE_TOKEN_RE = r"\d{2}-[A-Za-z]{3}-\d{4}"  # e.g., 21-Feb-2025
ROW_RE = re.compile(
    rf"^\s*(\d{{5,6}})\s+(.*?)\s+({DATE_TOKEN_RE})\s+([A-Za-z/ -]+?)\s+(FOOD|RETAIL)\s+(\d{{1,3}})(?:\s+(.*))?$"
)

STREET_TYPES = {
    "RD","RD.","ROAD","DR","DR.","DRIVE","ST","ST.","STREET","AVE","AVENUE","LN","LN.","LANE",
    "CIR","CIRCLE","BLVD","PKWY","PIKE","WAY","PL","PLAZA","CT","COURT","HWY","HIGHWAY","ROW"
}

def find_pdf_url():
    print("🌐 Fetching main page...")
    r = requests.get(PAGE_URL, headers=HEADERS, timeout=30)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "html.parser")

    candidates = []
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if "Food-Retail_Inspections" in href and href.lower().endswith(".pdf"):
            candidates.append(urljoin(PAGE_URL, href))

    if not candidates:
        raise RuntimeError("❌ PDF link not found!")

    def yyyymm(u):
        m = re.search(r"/wp-content/uploads/(\d{4})/(\d{2})/", u)
        return int(m.group(1))*100 + int(m.group(2)) if m else -1

    candidates.sort(key=yyyymm, reverse=True)
    pdf_url = candidates[0]
    print(f"📎 Found PDF: {pdf_url}")
    return pdf_url

def download_pdf(url) -> Path:
    print(f"📥 Downloading PDF from: {url}")
    resp = requests.get(url, headers=HEADERS, timeout=60, stream=True)
    resp.raise_for_status()
    tail = Path(urlparse(url).path).name or "latest.pdf"
    pdf_path = Path.cwd() / tail
    with open(pdf_path, "wb") as f:
        for chunk in resp.iter_content(1024 * 64):
            if chunk:
                f.write(chunk)
    print(f"✅ PDF downloaded → {pdf_path.name}")
    return pdf_path

def _split_name_address(prefix: str) -> tuple[str, str]:
    tokens = prefix.split()
    if not tokens:
        return prefix.strip(), ""
    numeric_positions = []
    addr_idx = None
    for i, tok in enumerate(tokens):
        if re.match(r'^[#]?\d', tok):
            numeric_positions.append(i)
            window = [w.upper().strip(",") for w in tokens[i+1:i+6]]
            if any(w in STREET_TYPES for w in window):
                addr_idx = i
                break
    if addr_idx is None and numeric_positions:
        addr_idx = numeric_positions[-1]
    if addr_idx is None:
        return prefix.strip(), ""
    name = " ".join(tokens[:addr_idx]).strip()
    address = " ".join(tokens[addr_idx:]).strip()
    return name, address

def parse_pdf(pdf_path: Path):
    print("🔎 Parsing PDF...")
    by_permit = {}

    with pdfplumber.open(str(pdf_path)) as pdf:
        for page in pdf.pages:
            text = page.extract_text() or ""
            for raw in text.splitlines():
                line = raw.strip()
                if not line or "Permit #" in line or "Report Executed On" in line:
                    continue

                m = ROW_RE.match(line)
                if not m:
                    continue

                permit = m.group(1)   # <-- this was accidentally glued to 'continue' before
                prefix = m.group(2)
                date_str = m.group(3)
                insp_type = m.group(4).strip().upper()
                category = m.group(5).upper()
                score = int(m.group(6))
                viol_str = (m.group(7) or "").strip()

                name, address = _split_name_address(prefix)
                date_iso = datetime.strptime(date_str, "%d-%b-%Y").date().isoformat()
                violations = [int(n) for n in re.findall(r"\d+", viol_str)]

                rec = by_permit.setdefault(permit, {
                    "permit": permit,
                    "name": name,
                    "address": address,
                    "inspections": []
                })
                if name and len(name) > len(rec["name"]):
                    rec["name"] = name
                if address and len(address) > len(rec["address"]):
                    rec["address"] = address

                rec["inspections"].append({
                    "date": date_iso,
                    "inspection_type": insp_type,
                    "category": category,
                    "score": score,
                    "violations": violations
                })

    entries = list(by_permit.values())
    print(f"✅ Parsed {len(entries)} establishments.")
    return entries

from datetime import datetime, date

def _latest_inspection_date(data):
    """Return the latest inspection date (as a date object) from parsed data."""
    latest = None
    for est in data:
        for ins in est.get("inspections", []):
            try:
                d = datetime.fromisoformat(ins["date"]).date()  # "YYYY-MM-DD"
                if latest is None or d > latest:
                    latest = d
            except Exception:
                pass
    return latest

def save_json(data, pdf_path: Path) -> str:
    SAVE_DIR.mkdir(parents=True, exist_ok=True)
    # Prefer latest inspection date in data; fallback to PDF filename
    def _latest_inspection_date(rows):
        latest = None
        for est in rows:
            for ins in est.get("inspections", []):
                try:
                    d = datetime.fromisoformat(ins["date"]).date()
                    if latest is None or d > latest:
                        latest = d
                except Exception:
                    pass
        return latest
    latest = _latest_inspection_date(data)
    if latest:
        date_part = latest.strftime("%m-%d-%Y")
    else:
        date_part = _date_part_from_pdf_filename(pdf_path.name)

    filename = f"inspection_data-{date_part}.json"
    out_path = SAVE_DIR / filename
    with open(out_path, "w") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    print(f"📁 JSON saved to {out_path}")
    return str(out_path)

def update_index() -> str:
    SAVE_DIR.mkdir(parents=True, exist_ok=True)
    files = sorted(
        SAVE_DIR.glob("inspection_data-*.json"),
        key=lambda p: p.stat().st_mtime,
        reverse=True
    )
    listing = [
        {
            "file": p.name,
            "size_bytes": p.stat().st_size,
            "modified": datetime.fromtimestamp(p.stat().st_mtime).isoformat()
        }
        for p in files
    ]
    index_path = SAVE_DIR / "index.json"
    with open(index_path, "w") as f:
        json.dump(listing, f, indent=2, ensure_ascii=False)
    print(f"🗂️  Index updated → {index_path}")
    return str(index_path)


def commit_to_git(*paths):
    # assumes the process runs in /home/pi/inspections (your webhook sets cwd)
    if os.system("git rev-parse --is-inside-work-tree >/dev/null 2>&1") != 0:
        print("ℹ️ Not a git repo; skipping commit.")
        return
    for p in paths:
        os.system(f'git add "{p}"')
    ts = datetime.now().isoformat(timespec="seconds")
    msg = f"Add/update inspections ({ts})"
    os.system(f'git commit -m "{msg}" >/dev/null 2>&1 || true')
    os.system('git push origin HEAD:main >/dev/null 2>&1')
    print("☁️ Changes pushed to GitHub (main).")
if __name__ == "__main__":
    try:
        pdf_url = find_pdf_url()
        pdf_path = download_pdf(pdf_url)
        data = parse_pdf(pdf_path)
        json_file = save_json(data, pdf_path)
        index_file = update_index()
        commit_to_git(json_file, index_file)
    except Exception as e:
        print("🚨 Error:", e)
