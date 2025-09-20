#!/usr/bin/env python3
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

PAGE_URL = "https://www.lfchd.org/food-protection/"
HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
}

# Column formats in this PDF (example line on p.1):
# 67372 #1 CHINA BUFFET 125 E. REYNOLDS ROAD, STE. 120 21-Feb-2025 REGULAR FOOD 93 15 39 41 48 56
# Date is dd-Mon-YYYY; "Food or Retail" is FOOD/RETAIL; Score is 0..100; trailing violations are numbers. :contentReference[oaicite:1]{index=1}

DATE_TOKEN_RE = r"\d{2}-[A-Za-z]{3}-\d{4}"  # e.g., 21-Feb-2025
ROW_RE = re.compile(
    rf"^\s*(\d{{5,6}})\s+(.*?)\s+({DATE_TOKEN_RE})\s+([A-Za-z/ -]+?)\s+(FOOD|RETAIL)\s+(\d{{1,3}})(?:\s+(.*))?$"
)

STREET_TYPES = {
    "RD","RD.","ROAD","DR","DR.","DRIVE","ST","ST.","STREET","AVE","AVENUE","LN","LN.","LANE",
    "CIR","CIRCLE","BLVD","PKWY","PIKE","WAY","PL","PLAZA","CT","COURT","HWY","HIGHWAY",
    "PI","PI.","PK","PLACE","ROW","PKWY","PKWY."
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
        raise Exception("❌ PDF link not found!")

    # Pick the most recent /YYYY/MM/ path if present
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
    """
    prefix = "<name and address tokens>" (everything between permit and date)
    Heuristic:
      - Find the *address start* at a numeric token (#?\d...) that is likely a street number.
      - Prefer a numeric token that has a street-type keyword within the next few tokens.
      - If none, fall back to the *last* numeric token (handles names like '33 STAVES').
    """
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
                # skip headers/blank lines
                if not line or "Permit #" in line or "Report Executed On" in line:
                    continue

                m = ROW_RE.match(line)
                if not m:
                    continue

                permit = m.group(1)
                prefix = m.group(2)
                date_str = m.group(3)
                insp_type = m.group(4).strip().upper()
                category = m.group(5).upper()
                score = int(m.group(6))
                viol_str = (m.group(7) or "").strip()

                name, address = _split_name_address(prefix)

                # normalize date to ISO
                date_iso = datetime.strptime(date_str, "%d-%b-%Y").date().isoformat()

                violations = [int(n) for n in re.findall(r"\d+", viol_str)]

                # group by permit
                rec = by_permit.setdefault(permit, {
                    "permit": permit,
                    "name": name,
                    "address": address,
                    "inspections": []
                })
                # If we later see a better name/address (rare), keep the longer non-empty value
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

def _date_part_from_pdf_filename(pdf_filename: str) -> str:
    """
    From 'Food-Retail_Inspections-06.2024-06.2025.pdf' -> '06-2024-06-2025'
    From 'Food-Retail_Inspections-1-20-2025.pdf'     -> '1-20-2025'
    Fallback: today's date.
    """
    base = os.path.basename(pdf_filename)
    name_no_ext, _ = os.path.splitext(base)

    # Single m-d-yyyy
    m = re.search(r"(\d{1,2}-\d{1,2}-\d{4})", name_no_ext)
    if m:
        return m.group(1)

    # Range mm.yyyy-mm.yyyy
    m = re.search(r"(\d{2}\.\d{4}-\d{2}\.\d{4})", name_no_ext)
    if m:
        return m.group(1).replace(".", "-")

    # Single mm.yyyy
    m = re.search(r"(\d{2}\.\d{4})", name_no_ext)
    if m:
        return m.group(1).replace(".", "-")

    return datetime.now().strftime("%Y-%m-%d")

def save_json(data, pdf_path: Path) -> str:
    date_part = _date_part_from_pdf_filename(pdf_path.name)
    filename = f"inspection_data-{date_part}.json"
    with open(filename, "w") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    print(f"📁 JSON saved to {filename}")
    return filename

def commit_to_git(json_file):
    if os.system("git rev-parse --is-inside-work-tree >/dev/null 2>&1") != 0:
        print("ℹ️ Not a git repo; skipping commit.")
        return
    os.system(f"git add {json_file}")
    ts = datetime.now().isoformat(timespec="seconds")
    os.system(f"git commit -m 'Add {json_file} ({ts})' >/dev/null 2>&1 || true")
    os.system("git push origin HEAD:main >/dev/null 2>&1 || git push origin HEAD:master >/dev/null 2>&1")
    print("☁️ Changes pushed to GitHub.")

if __name__ == "__main__":
    try:
        pdf_url = find_pdf_url()
        pdf_path = download_pdf(pdf_url)
        data = parse_pdf(pdf_path)
        json_file = save_json(data, pdf_path)
        commit_to_git(json_file)
    except Exception as e:
        print("🚨 Error:", e)
