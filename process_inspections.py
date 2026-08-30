#!/usr/bin/env python3
"""
Daily Fayette County inspection updater for sklink2/Food.

Primary source:
  Kentucky Environmental Public Business Listing (COUNTY=34 / Fayette)

What it does:
  * Downloads every Fayette County establishment from the state site.
  * Prefers the site's CSV export for the master list, then enriches current
    inspections from the live ASP.NET HTML so violation codes/text are retained.
  * Falls back to ASP.NET pagination if CSV export is unavailable.
  * Unions historical inspection records from every legacy JSON snapshot in the repo.
  * Never drops a distinct historical inspection; richer violation/details fields are preserved.
  * Marks establishments first discovered after the initial baseline as "new"
    for 30 days.
  * Marks inspections as "new" for 30 days from inspection date.
  * Uses the most recent inspection as current; on the same date FOLLOWUP wins.
  * Creates category JSON files using simple name-based heuristics.
  * Adds stable establishment/inspection IDs for SwiftData upserts.
  * Preserves establishments that disappear from the live feed as inactive history.
  * Publishes metadata.json + changes.json for full or incremental device sync.
  * Updates one stable current JSON file only when the published data changes.
  * Updates inspections/index.json in the legacy array format.
  * Commits and pushes changed JSON to GitHub.

Designed for Raspberry Pi / Python 3.11+.
Dependencies: requests, beautifulsoup4
"""

from __future__ import annotations

import csv
import hashlib
import html as html_lib
import io
import json
import os
import re
import subprocess
import sys
import time
from copy import deepcopy
from datetime import date, datetime, timedelta
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup

# ----------------------------- Configuration -----------------------------

COUNTY = 34
COUNTY_NAME = "Fayette"
STATE_URL = (
    "https://public.cdpehs.com/KYEnvPBL/"
    "VW_PUBLIC_EST_INSP/ShowVW_PUBLIC_EST_INSPTable.aspx?COUNTY=34"
)
SOURCE_NAME = "KYEnvPBL"

REPO_DIR = Path("/home/pi/inspections")
OUT_DIR = REPO_DIR / "inspections"
CATEGORY_DIR = OUT_DIR / "categories"
MASTER_PATH = OUT_DIR / "inspection_data-current.json"
MANIFEST_PATH = OUT_DIR / "manifest.json"
METADATA_PATH = OUT_DIR / "metadata.json"
CHANGES_PATH = OUT_DIR / "changes.json"
INDEX_PATH = OUT_DIR / "index.json"

SWIFTDATA_SCHEMA_VERSION = 2
DATASET_NAME = "EatLex Fayette County Inspections"

NEW_DAYS = 30
REQUEST_TIMEOUT = 60
FALLBACK_PAGE_SIZE = 10
FALLBACK_DELAY_SECONDS = 0.15
# The violation details only exist in the rendered HTML score cells. We ask the
# ASP.NET pager for a larger page size; if the server refuses it, the crawler
# safely continues at the default 10 rows/page.
VIOLATION_PAGE_SIZE = 100
VIOLATION_DELAY_SECONDS = 0.10
MAX_FALLBACK_PAGES = 400
REQUIRE_VIOLATION_ENRICHMENT = True

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (X11; Linux armv7l) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 EatLexInspectionBot/2.0"
    ),
    "Accept-Language": "en-US,en;q=0.9",
}

# If your git remote/branch are different, change these.
GIT_REMOTE = "origin"
GIT_BRANCH = "main"

# ----------------------------- Utility helpers ----------------------------


def log(message: str) -> None:
    print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {message}", flush=True)


def normalize_space(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


def normalize_key_text(value: Any) -> str:
    value = html_lib.unescape(normalize_space(value)).upper()
    value = value.replace("&", " AND ")
    value = re.sub(r"[^A-Z0-9]+", " ", value)
    return normalize_space(value)


def normalize_address_key(value: Any) -> str:
    text = normalize_key_text(value)
    # Normalize common street suffix differences between the legacy LFCHD PDFs
    # and the current KYEnvPBL export. This is only used for matching; the
    # displayed address is never modified.
    replacements = {
        " STREET ": " ST ",
        " ROAD ": " RD ",
        " DRIVE ": " DR ",
        " AVENUE ": " AVE ",
        " BOULEVARD ": " BLVD ",
        " LANE ": " LN ",
        " COURT ": " CT ",
        " CIRCLE ": " CIR ",
        " PARKWAY ": " PKWY ",
        " HIGHWAY ": " HWY ",
        " PLACE ": " PL ",
    }
    padded = f" {text} "
    for source, target in replacements.items():
        padded = padded.replace(source, target)
    return normalize_space(padded)




def address_house_number(value: Any) -> str:
    """Return the leading street number used only for conservative state-row dedupe."""
    text = normalize_address_key(value)
    match = re.match(r"^(\d+[A-Z]?)\b", text)
    return match.group(1) if match else ""


def same_physical_address_for_same_name(address_a: Any, address_b: Any) -> bool:
    """
    Conservative fuzzy address comparison used only when the establishment name
    is already identical. It collapses obvious formatting/typo aliases such as
    "3337 SQUIRE OAK DRIVE" vs "3337 SQUIRES OAK DR", while refusing to merge
    different street numbers (for example 723 vs 725 NATIONAL AVE).

    Suite/unit differences at the same base address are allowed to group because
    all source rows and all distinct inspection scores are still retained in the
    merged public establishment history.
    """
    a = normalize_address_key(address_a)
    b = normalize_address_key(address_b)
    if not a or not b:
        return False
    if a == b:
        return True

    num_a = address_house_number(a)
    num_b = address_house_number(b)
    if not num_a or num_a != num_b:
        return False

    # Very high threshold: this is meant only for obvious spelling/pluralization
    # or suffix-format differences, not general fuzzy business matching.
    return SequenceMatcher(None, a, b).ratio() >= 0.93


GENERIC_NAME_WORDS = {
    "THE", "LLC", "INC", "INCORPORATED", "CORP", "CORPORATION", "CO", "COMPANY",
    "SCHOOL", "SCHOOLS", "CENTER", "CENTRE"
}


def same_establishment_name_variant(name_a: Any, name_b: Any) -> bool:
    """Conservative name-alias test used only when addresses are the same/near-same.

    This intentionally catches aliases such as "ASHLAND ELEMENTARY" vs
    "ASHLAND ELEMENTARY SCHOOL" while refusing to collapse unrelated businesses
    that merely share a building.
    """
    a = normalize_key_text(name_a)
    b = normalize_key_text(name_b)
    if not a or not b:
        return False
    if a == b:
        return True

    ta = a.split()
    tb = b.split()
    ca = [t for t in ta if t not in GENERIC_NAME_WORDS]
    cb = [t for t in tb if t not in GENERIC_NAME_WORDS]
    if ca and cb and ca == cb:
        return True

    # One name may simply add a generic suffix such as SCHOOL/LLC/INC.
    if a in b or b in a:
        longer = tb if len(tb) >= len(ta) else ta
        shorter = ta if len(tb) >= len(ta) else tb
        extras = longer[len(shorter):]
        if extras and all(x in GENERIC_NAME_WORDS for x in extras):
            return True

    return SequenceMatcher(None, a, b).ratio() >= 0.92


def group_state_rows(state_rows: List[dict]) -> List[Tuple[str, List[dict]]]:
    """Group rows into establishments without discarding inspection events.

    Rows with identical names and near-identical addresses are grouped. Rows
    with conservative name aliases may also group when they share the same
    physical address. Every source row remains in the group and is later merged
    into the inspection history, so Ashland Elementary can retain both 98 and
    100 inspections from the same date if both are present in the state feed.
    """
    groups: List[Tuple[str, List[dict]]] = []
    by_name_city: Dict[Tuple[str, str], List[int]] = {}
    by_house_city: Dict[Tuple[str, str], List[int]] = {}

    for row in state_rows:
        name = normalize_space(row.get("name"))
        address = normalize_space(row.get("address"))
        city = normalize_space(row.get("city")) or "LEXINGTON"
        if not name or not address:
            continue

        name_key = normalize_key_text(name)
        city_key = normalize_key_text(city)
        name_bucket = (name_key, city_key)
        house_bucket = (address_house_number(address), city_key)
        matched_index: Optional[int] = None

        # First prefer same-name aliases.
        for idx in by_name_city.get(name_bucket, []):
            representative = groups[idx][1][0]
            if same_physical_address_for_same_name(address, representative.get("address")):
                matched_index = idx
                break

        # Then allow a conservative name variant at the same physical address.
        if matched_index is None and house_bucket[0]:
            for idx in by_house_city.get(house_bucket, []):
                representative = groups[idx][1][0]
                if (
                    same_physical_address_for_same_name(address, representative.get("address"))
                    and same_establishment_name_variant(name, representative.get("name"))
                ):
                    matched_index = idx
                    break

        if matched_index is None:
            key = establishment_key(name, address, city)
            groups.append((key, [row]))
            idx = len(groups) - 1
            by_name_city.setdefault(name_bucket, []).append(idx)
            if house_bucket[0]:
                by_house_city.setdefault(house_bucket, []).append(idx)
        else:
            groups[matched_index][1].append(row)
            # Register aliases so later rows can reach this same group quickly.
            by_name_city.setdefault(name_bucket, []).append(matched_index)
            if house_bucket[0]:
                by_house_city.setdefault(house_bucket, []).append(matched_index)

    return groups

def establishment_key(name: str, address: str, city: str = "LEXINGTON") -> str:
    return "|".join(
        [normalize_key_text(name), normalize_address_key(address), normalize_key_text(city)]
    )


def address_lookup_key(address: str, city: str = "LEXINGTON") -> str:
    return "ADDR|" + "|".join([normalize_address_key(address), normalize_key_text(city)])


def name_lookup_key(name: str, city: str = "LEXINGTON") -> str:
    return "NAME|" + "|".join([normalize_key_text(name), normalize_key_text(city)])


def stable_state_id(key: str) -> str:
    return "state-" + hashlib.sha1(key.encode("utf-8")).hexdigest()[:16]


def _stable_hash(prefix: str, seed: str, length: int = 24) -> str:
    digest = hashlib.sha256(seed.encode("utf-8")).hexdigest()[:length]
    return f"{prefix}_{digest}"


def ensure_establishment_id(record: dict, fallback_key: str) -> str:
    """Return/persist a stable public ID suitable for SwiftData @unique.

    Once an ID has been published it is never recomputed, even if the display
    name/address later changes. On the first migration, a real legacy permit is
    preferred when available; otherwise the normalized establishment key seeds
    a deterministic ID.
    """
    existing = normalize_space(record.get("id"))
    if existing.startswith("est_"):
        return existing

    permit = normalize_space(record.get("permit"))
    if permit and not permit.lower().startswith("state-"):
        seed = f"permit|{permit}|{fallback_key}"
    else:
        seed = f"location|{fallback_key}"

    record_id = _stable_hash("est", seed)
    record["id"] = record_id
    return record_id


def ensure_inspection_ids(record: dict) -> None:
    """Assign stable IDs to every historical inspection without dropping any."""
    establishment_id = normalize_space(record.get("id"))
    if not establishment_id:
        raise ValueError("Establishment ID must be assigned before inspection IDs")

    history = record.get("inspections") or []
    if not isinstance(history, list):
        return

    used = set()
    for position, inspection in enumerate(history):
        if not isinstance(inspection, dict):
            continue

        existing = normalize_space(inspection.get("id"))
        if existing.startswith("insp_") and existing not in used:
            used.add(existing)
            continue

        # The same date/type/score/category is treated as one inspection event by
        # merge_inspection(). Position is only a collision fallback for malformed
        # legacy data that somehow contains two otherwise identical events.
        base_seed = "|".join([
            establishment_id,
            str(inspection.get("date") or ""),
            normalize_key_text(inspection.get("inspection_type")),
            str(inspection.get("score") if inspection.get("score") is not None else ""),
            normalize_key_text(inspection.get("category")),
        ])
        candidate = _stable_hash("insp", base_seed)
        if candidate in used:
            candidate = _stable_hash("insp", f"{base_seed}|{position}")
        inspection["id"] = candidate
        used.add(candidate)


def validate_swiftdata_ids(records: List[dict]) -> None:
    establishment_ids = set()
    inspection_ids = set()

    for record in records:
        record_id = normalize_space(record.get("id"))
        if not record_id:
            raise RuntimeError(f"Missing establishment ID for {record.get('name')}")
        if record_id in establishment_ids:
            raise RuntimeError(f"Duplicate establishment ID detected: {record_id}")
        establishment_ids.add(record_id)

        for inspection in record.get("inspections", []) or []:
            if not isinstance(inspection, dict):
                continue
            inspection_id = normalize_space(inspection.get("id"))
            if not inspection_id:
                raise RuntimeError(f"Missing inspection ID under {record_id}")
            if inspection_id in inspection_ids:
                raise RuntimeError(f"Duplicate inspection ID detected: {inspection_id}")
            inspection_ids.add(inspection_id)


def dataset_version(records: List[dict]) -> str:
    """Content-addressed version used by the iOS sync layer."""
    payload = canonical_json(records).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_date(value: Any) -> Optional[date]:
    text = normalize_space(value)
    if not text or text.lower() in {"none", "null", "n/a", "&nbsp;"}:
        return None
    for fmt in ("%m/%d/%Y", "%m/%d/%y", "%Y-%m-%d", "%m-%d-%Y"):
        try:
            return datetime.strptime(text, fmt).date()
        except ValueError:
            pass
    return None


def iso_date(value: Any) -> Optional[str]:
    d = parse_date(value)
    return d.isoformat() if d else None


def parse_score(value: Any) -> Optional[int]:
    text = normalize_space(value)
    if not text or text.lower() in {"none", "null", "n/a", "&nbsp;"}:
        return None
    match = re.search(r"\b(100|[1-9]?\d)\b", text)
    if not match:
        return None
    score = int(match.group(1))
    return score if 0 <= score <= 100 else None


def within_new_window(date_text: Optional[str], today: date) -> bool:
    d = parse_date(date_text)
    if not d:
        return False
    age = (today - d).days
    return 0 <= age < NEW_DAYS


def atomic_write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    with temp.open("w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.write("\n")
    os.replace(temp, path)


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def canonical_json(data: Any) -> str:
    return json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


# ----------------------------- Categorization -----------------------------

FAST_FOOD_TERMS = [
    "MCDONALD", "WENDY", "TACO BELL", "BURGER KING", "CHICK FIL A", "CHICK-FIL-A",
    "ARBY", "KFC", "KENTUCKY FRIED CHICKEN", "SUBWAY", "JIMMY JOHN", "JERSEY MIKE",
    "FIREHOUSE SUBS", "PENN STATION", "DOMINO", "PIZZA HUT", "LITTLE CAESAR",
    "PAPA JOHN", "SONIC", "DAIRY QUEEN", "FIVE GUYS", "CHIPOTLE", "QDOBA",
    "PANERA", "RAISING CANE", "CANES", "WHITE CASTLE", "CULVER", "ZAXBY",
    "STEAK N SHAKE", "HARDEE", "CAPTAIN D", "LONG JOHN SILVER", "WINGSTOP",
    "POPEYES", "MOES", "TROPICAL SMOOTHIE", "SHAKE SHACK"
]

CATEGORY_RULES: List[Tuple[str, List[str]]] = [
    ("Childcare & Early Learning", [
        "DAYCARE", "DAY CARE", "CHILD CARE", "CHILDCARE", "PRESCHOOL", "PRE-SCHOOL",
        "EARLY LEARNING", "EARLY CHILD", "HEAD START", "MONTESSORI"
    ]),
    ("Schools & Universities", [
        "ELEMENTARY", "MIDDLE SCHOOL", "HIGH SCHOOL", "SCHOOL", "ACADEMY",
        "UNIVERSITY", "COLLEGE", "CAMPUS", "FAYETTE COUNTY PUBLIC", "FCPS",
        "UNIVERSITY OF KENTUCKY", "TRANSYLVANIA"
    ]),
    ("Healthcare & Senior Living", [
        "HOSPITAL", "MEDICAL", "HEALTH CARE", "HEALTHCARE", "NURSING", "ASSISTED LIVING",
        "SENIOR", "REHAB", "REHABILITATION", "ADULT DAY", "CARE CENTER", "CARE CENTRE",
        "HOSPICE"
    ]),
    ("Pools & Recreation", [
        "POOL", "AQUATIC", "SWIM", "SPLASH", "WATER PARK", "COUNTRY CLUB", "YMCA",
        "FITNESS", "ATHLETIC CLUB", "RECREATION", "REC CENTER"
    ]),
    ("Fast Food & Fast Casual", FAST_FOOD_TERMS),
    ("Coffee, Bakery & Desserts", [
        "STARBUCKS", "COFFEE", "CAFE", "CAFÉ", "BAKERY", "DONUT", "DOUGHNUT",
        "ICE CREAM", "CREAMERY", "DESSERT", "COOKIE", "BOBA", "TEA HOUSE", "TEAHOUSE"
    ]),
    ("Grocery & Markets", [
        "KROGER", "PUBLIX", "ALDI", "WHOLE FOODS", "TRADER JOE", "WALMART", "WAL-MART",
        "MEIJER", "COSTCO", "SAMS CLUB", "SAM'S CLUB", "GROCERY", "SUPERMARKET",
        "FOOD MARKET", "MEAT MARKET", "SEAFOOD MARKET", "FARMERS MARKET", "FARMER'S MARKET"
    ]),
    ("Convenience & Gas", [
        "SPEEDWAY", "CIRCLE K", "THORNTONS", "MARATHON", "SHELL", "BP ", "EXXON",
        "MOBIL", "GAS STATION", "CONVENIENCE", "FUEL", "TRAVEL CENTER"
    ]),
    ("Bars, Breweries & Distilleries", [
        "BREWERY", "BREWING", "DISTILLERY", "TAVERN", "PUB", "BAR ", " BAR", "LOUNGE",
        "TAPROOM", "TAP ROOM", "WINE BAR"
    ]),
    ("Hotels & Lodging", [
        "HOTEL", "MOTEL", "INN ", " INN", "SUITES", "RESORT", "LODGE"
    ]),
    ("Mobile, Vendors & Concessions", [
        "MOBILE", "FOOD TRUCK", "VENDOR", "CONCESSION", "TEMPORARY", "CATERING", "CATERER"
    ]),
    ("Restaurants & Dining", [
        "RESTAURANT", "GRILL", "KITCHEN", "PIZZA", "SUSHI", "STEAKHOUSE", "STEAK HOUSE",
        "BISTRO", "DINER", "BBQ", "BARBECUE", "TAQUERIA", "TACOS", "WINGS", "CHICKEN",
        "BURGER", "SEAFOOD", "RAMEN", "THAI", "INDIAN", "MEXICAN", "CHINESE", "BUFFET"
    ]),
]


def classify_establishment(name: str, address: str, previous: Optional[dict] = None) -> str:
    text = f" {normalize_key_text(name)} {normalize_key_text(address)} "
    for category, terms in CATEGORY_RULES:
        for term in terms:
            if normalize_key_text(term) in text:
                return category

    # If it existed in the legacy food inspection data, it is almost certainly a food establishment.
    if previous and previous.get("inspections"):
        legacy_categories = {
            normalize_key_text(i.get("category"))
            for i in previous.get("inspections", [])
            if isinstance(i, dict)
        }
        if "FOOD" in legacy_categories or "RETAIL" in legacy_categories:
            return "Restaurants & Food Establishments"

    return "Other / Uncategorized"


def category_slug(category: str) -> str:
    slug = normalize_key_text(category).lower().replace(" ", "-")
    return slug or "uncategorized"



# --------------------------- Violation mapping ----------------------------

# KYEnvPBL exposes violated inspection-item *titles* inside the score cell's
# detailRolloverPopup() HTML. The CSV export does not contain them. These
# aliases map the state's wording to the 1-58 violation codes used by EatLex.
# Raw state text is ALSO retained in JSON so wording is never lost even if a
# future state-site wording change cannot be mapped immediately.
VIOLATION_ALIASES: Dict[int, List[str]] = {
    1: ["PERSON IN CHARGE PRESENT DEMONSTRATES KNOWLEDGE AND PERFORMS DUTIES"],
    2: ["CERTIFIED FOOD PROTECTION MANAGER"],
    3: ["MANAGEMENT FOOD EMPLOYEE AND CONDITIONAL EMPLOYEE KNOWLEDGE RESPONSIBILITIES AND REPORTING"],
    4: ["PROPER USE OF RESTRICTION AND EXCLUSION"],
    5: ["PROCEDURES FOR RESPONDING TO VOMITING AND DIARRHEAL EVENTS", "PROCEDURES FOR VOMITING AND DIARRHEAL EVENTS"],
    6: ["PROPER EATING TASTING DRINKING OR TOBACCO USE"],
    7: ["NO DISCHARGE FROM EYES NOSE AND MOUTH", "DISCHARGE FROM EYES NOSE OR THROAT"],
    8: ["HANDS CLEAN AND PROPERLY WASHED"],
    9: ["NO BARE HAND CONTACT WITH READY TO EAT FOODS", "NO BARE HAND CONTACT WITH RTE FOOD OR APPROVED ALTERNATE METHOD PROPERLY FOLLOWED"],
    10: ["ADEQUATE HANDWASHING FACILITIES SUPPLIED AND ACCESSIBLE", "ADEQUATE HAND WASHING FACILITIES SUPPLIED AND ACCESSIBLE"],
    11: ["FOOD OBTAINED FROM APPROVED SOURCE"],
    12: ["FOOD RECEIVED AT PROPER TEMPERATURE"],
    13: ["FOOD IN GOOD CONDITION SAFE AND UNADULTERATED"],
    14: ["REQUIRED RECORDS AVAILABLE SHELLSTOCK TAGS PARASITE DESTRUCTION", "REQUIRED RECORDS AVAILABLE SHELLSTOCK TAGS PARASITE DESTRUCTION DOCUMENTATION"],
    15: ["FOOD SEPARATED AND PROTECTED"],
    16: ["PROPER DISPOSITION OF RETURNED PREVIOUSLY SERVED RECONDITIONED AND UNSAFE FOOD", "PROPER DISPOSITION OF RETURNED REJECTED OR UNUSED FOOD"],
    17: ["FOOD STORED COVERED"],
    18: ["FOOD CONTACT SURFACES CLEANED AND SANITIZED", "FOOD CONTACT SURFACES CLEANED"],
    19: ["PROPER COOKING TIME AND TEMPERATURES", "PROPER COOKING TIME AND TEMPERATURE"],
    20: ["PROPER REHEATING PROCEDURES FOR HOT HOLDING", "PROPER REHEATING PROCEDURES"],
    21: ["PROPER COLD HOLDING TEMPERATURES", "PROPER COLD HOLDING"],
    22: ["PROPER HOT HOLDING TEMPERATURES", "PROPER HOT HOLDING"],
    23: ["PROPER COOLING TIME AND TEMPERATURES", "PROPER COOLING"],
    24: ["TIME AS A PUBLIC HEALTH CONTROL PROCEDURES AND RECORDS"],
    25: ["PROPER DATE MARKING AND DISPOSITION"],
    26: ["CONSUMER ADVISORY"],
    27: ["HIGHLY SUSCEPTIBLE POPULATION", "HIGHLY SUSCEPTIBLE POPULATIONS"],
    28: ["FOOD ADDITIVES APPROVED AND PROPERLY USED", "APPROVED FOOD ADDITIVES"],
    29: ["TOXIC SUBSTANCES PROPERLY IDENTIFIED STORED AND USED"],
    30: ["COMPLIANCE WITH VARIANCE SPECIALIZED PROCESS AND HACCP PLAN", "COMPLIANCE WITH VARIANCE SPECIALIZED PROCESS HACCP PLAN"],
    31: ["PASTEURIZED FOODS USED PROHIBITED FOODS NOT OFFERED", "PASTEURIZED FOODS USED PROHIBITED FOODS"],
    32: ["WATER AND ICE FROM APPROVED SOURCE"],
    33: ["SPECIALIZED PROCESSING METHODS", "SPECIALIZED PROCESSING METHODS APPROVED"],
    34: ["PROPER COOLING METHODS USED ADEQUATE EQUIPMENT FOR TEMPERATURE CONTROL", "PROPER COOLING METHODS USED ADEQUATE EQUIPMENT FOR TEMP CONTROL"],
    35: ["PLANT FOOD PROPERLY COOKED FOR HOT HOLDING"],
    36: ["APPROVED THAWING METHODS USED"],
    37: ["THERMOMETERS PROVIDED AND ACCURATE"],
    38: ["FOOD PROPERLY LABELED ORIGINAL CONTAINER", "FOOD PROPERLY LABELED ORIGINAL CONTAINERS"],
    39: ["CONTAMINATION PREVENTED DURING FOOD PREPARATION STORAGE AND DISPLAY"],
    40: ["PERSONAL CLEANLINESS HAIR RESTRAINTS"],
    41: ["WIPING CLOTHS PROPERLY USED AND STORED"],
    42: ["WASHING FRUITS AND VEGETABLES", "FRUITS AND VEGETABLES PROPERLY WASHED"],
    43: ["REQUIRED POSTINGS PERMIT INSPECTION AND HAND WASHING SIGNS", "REQUIRED POSTINGS PERMIT INSPECTION AND HANDWASHING SIGNS", "POSTINGS AND COMPLIANCE"],
    44: ["IN USE UTENSILS PROPERLY STORED"],
    45: ["UTENSILS EQUIPMENT AND LINENS PROPERLY STORED DRIED AND HANDLED"],
    46: ["SINGLE USE SINGLE SERVICE ARTICLES PROPERLY STORED AND USED", "SINGLE USE AND SINGLE SERVICE ARTICLES PROPERLY STORED AND USED"],
    47: ["GLOVES USED PROPERLY", "PROPER USE OF GLOVES"],
    48: ["FOOD AND NONFOOD CONTACT SURFACES CLEANABLE PROPERLY DESIGNED CONSTRUCTED AND USED", "FOOD AND NONFOOD CONTACT SURFACES CLEANABLE PROPERLY DESIGNED CONSTRUCTED USED"],
    49: ["WAREWASHING FACILITIES INSTALLED MAINTAINED AND USED TEST STRIPS"],
    50: ["NONFOOD CONTACT SURFACES CLEAN", "NON FOOD CONTACT SURFACES CLEAN"],
    51: ["HOT AND COLD WATER AVAILABLE ADEQUATE PRESSURE PLUMBING MAINTAINED", "HOT AND COLD WATER AVAILABLE ADEQUATE PRESSURE"],
    52: ["PLUMBING INSTALLED PROPER BACKFLOW DEVICES"],
    53: ["SEWAGE AND WASTE WATER PROPERLY DISPOSED", "SEWAGE AND WASTEWATER PROPERLY DISPOSED"],
    54: ["TOILET FACILITIES PROPERLY CONSTRUCTED SUPPLIED AND CLEAN"],
    55: ["GARBAGE REFUSE PROPERLY DISPOSED FACILITIES MAINTAINED", "GARBAGE AND REFUSE PROPERLY DISPOSED FACILITIES MAINTAINED"],
    56: ["PHYSICAL FACILITIES INSTALLED MAINTAINED AND CLEAN"],
    57: ["ADEQUATE VENTILATION AND LIGHTING DESIGNATED AREAS USED"],
    58: ["INSECTS RODENTS AND ANIMALS NOT PRESENT", "INSECTS RODENTS AND ANIMALS"],
}


def normalize_violation_text(value: Any) -> str:
    return normalize_key_text(value)


VIOLATION_EXACT_MAP: Dict[str, int] = {
    normalize_violation_text(alias): code
    for code, aliases in VIOLATION_ALIASES.items()
    for alias in aliases
}


def violation_code_for_text(text: str) -> Optional[int]:
    """Map live KYEnvPBL item-title text to EatLex's 1-58 code set.

    Exact normalized aliases are preferred. A conservative fuzzy fallback is
    used only for small punctuation/wording changes. Raw text is always kept,
    so an unmapped future phrase never disappears from the dataset.
    """
    norm = normalize_violation_text(text)
    if not norm:
        return None
    exact = VIOLATION_EXACT_MAP.get(norm)
    if exact is not None:
        return exact

    # Strong semantic shortcuts for the most common state wording changes.
    phrase_rules = [
        (25, ("DATE MARKING", "DISPOSITION")),
        (56, ("PHYSICAL FACILITIES", "MAINTAINED", "CLEAN")),
        (55, ("GARBAGE", "REFUSE", "FACILITIES", "MAINTAINED")),
        (51, ("HOT AND COLD WATER", "ADEQUATE PRESSURE")),
        (40, ("PERSONAL CLEANLINESS", "HAIR RESTRAINTS")),
        (50, ("NONFOOD CONTACT SURFACES", "CLEAN")),
        (49, ("WAREWASHING", "FACILITIES")),
        (52, ("PLUMBING", "BACKFLOW")),
        (58, ("INSECTS", "RODENTS", "ANIMALS")),
        (18, ("FOOD CONTACT SURFACES", "CLEANED", "SANITIZED")),
        (8, ("HANDS", "CLEAN", "WASHED")),
        (1, ("PERSON IN CHARGE", "DEMONSTRATES KNOWLEDGE")),
    ]
    for code, required in phrase_rules:
        if all(token in norm for token in required):
            return code

    # Conservative fuzzy fallback across canonical aliases.
    best_code: Optional[int] = None
    best_ratio = 0.0
    for alias, code in VIOLATION_EXACT_MAP.items():
        ratio = SequenceMatcher(None, norm, alias).ratio()
        if ratio > best_ratio:
            best_ratio = ratio
            best_code = code
    return best_code if best_ratio >= 0.78 else None


def violation_details_from_score_cell(cell) -> Tuple[List[int], List[str], List[str]]:
    """Extract violation item titles from a score-cell rollover popup.

    Returns (mapped_codes, raw_texts, unmapped_texts).
    """
    link = cell.find("a", onclick=True)
    if not link:
        return [], [], []
    onclick = html_lib.unescape(link.get("onclick") or "")
    match = re.search(r"(<ul>.*?</ul>)", onclick, re.I | re.S)
    if not match:
        return [], [], []

    fragment = BeautifulSoup(match.group(1), "html.parser")
    raw_texts: List[str] = []
    codes: List[int] = []
    unmapped: List[str] = []
    for li in fragment.find_all("li"):
        text = normalize_space(html_lib.unescape(li.get_text(" ", strip=True)))
        if not text:
            continue
        if text not in raw_texts:
            raw_texts.append(text)
        code = violation_code_for_text(text)
        if code is None:
            if text not in unmapped:
                unmapped.append(text)
        elif code not in codes:
            codes.append(code)
    codes.sort()
    return codes, raw_texts, unmapped


def state_row_detail_key(row: dict) -> str:
    """Stable match key between CSV rows and their rendered HTML rows."""
    return "|".join([
        normalize_key_text(row.get("name")),
        normalize_address_key(row.get("address")),
        normalize_key_text(row.get("city") or "LEXINGTON"),
        str(row.get("last_inspection_date") or ""),
        str(row.get("last_inspection_score") if row.get("last_inspection_score") is not None else ""),
        str(row.get("followup_date") or ""),
        str(row.get("followup_score") if row.get("followup_score") is not None else ""),
    ])


def merge_violation_enrichment(csv_rows: List[dict], html_rows: List[dict]) -> Tuple[int, List[str]]:
    """Copy live violation details from rendered rows into the CSV master rows."""
    buckets: Dict[str, List[dict]] = {}
    for row in html_rows:
        buckets.setdefault(state_row_detail_key(row), []).append(row)

    matched = 0
    unmapped: List[str] = []
    for row in csv_rows:
        bucket = buckets.get(state_row_detail_key(row)) or []
        detail = bucket.pop(0) if bucket else None
        if not detail:
            continue
        matched += 1
        for key in (
            "last_violations", "last_violation_texts", "last_unmapped_violation_texts",
            "followup_violations", "followup_violation_texts", "followup_unmapped_violation_texts",
        ):
            row[key] = deepcopy(detail.get(key) or [])
        for text in (detail.get("last_unmapped_violation_texts") or []) + (detail.get("followup_unmapped_violation_texts") or []):
            if text not in unmapped:
                unmapped.append(text)
    return matched, unmapped

# ------------------------- ASP.NET state-site scraper ----------------------

EXPECTED_HEADERS = {
    # Current KY CDP CSV export labels (Aug. 2026) plus the labels used by
    # the HTML table / older exports. Keeping aliases makes the importer
    # tolerant of small wording changes on the state site.
    "name": ["PREMISE NAME", "NAME"],
    "address": ["PREMISE ADDRESS 1", "PREMISE ADDRESS", "ADDRESS"],
    "city": ["PREMISE CITY", "CITY"],
    "last_date": ["LAST INSP DATE", "LAST INSPECTION DATE", "INSPECTION DATE"],
    "last_score": [
        "LAST INSP SCORE",
        "LAST INSPECTION SCORE/GRADE",
        "LAST INSPECTION SCORE",
        "INSPECTION SCORE/GRADE",
    ],
    "follow_date": [
        "FOLLOW INSP DATE",
        "FOLLOW-UP DATE",
        "FOLLOW UP DATE",
        "FOLLOWUP DATE",
    ],
    "follow_score": [
        "FOLLOW INSP SCORE",
        "FOLLOW-UP SCORE/GRADE",
        "FOLLOW UP SCORE/GRADE",
        "FOLLOWUP SCORE/GRADE",
    ],
}


def canonical_header(value: Any) -> str:
    return normalize_space(value).upper().replace("\ufeff", "")


def map_csv_headers(fieldnames: Iterable[str]) -> Dict[str, str]:
    available = {canonical_header(x): x for x in fieldnames if x is not None}
    mapping: Dict[str, str] = {}
    for logical, candidates in EXPECTED_HEADERS.items():
        for candidate in candidates:
            if candidate in available:
                mapping[logical] = available[candidate]
                break
    return mapping


def rows_from_csv_bytes(content: bytes) -> List[dict]:
    """Parse the CDP export.

    The KY CDP site currently returns its CSV export as text/plain and may use
    UTF-16 (with NUL bytes), even though the control is labelled "Export CSV".
    Detect the encoding and delimiter rather than assuming UTF-8/comma.
    """
    if content.startswith((b"\xff\xfe", b"\xfe\xff")):
        encodings = ("utf-16", "utf-8-sig", "cp1252")
    elif b"\x00" in content[:512]:
        encodings = ("utf-16", "utf-8-sig", "cp1252")
    else:
        encodings = ("utf-8-sig", "utf-16", "cp1252")

    text = None
    used_encoding = None
    for encoding in encodings:
        try:
            candidate = content.decode(encoding)
        except UnicodeDecodeError:
            continue
        # Reject a decode that still contains lots of NULs; that usually means
        # UTF-16 bytes were decoded as a single-byte encoding.
        if candidate[:2000].count("\x00") > 5:
            continue
        text = candidate
        used_encoding = encoding
        break

    if text is None:
        text = content.decode("utf-8", errors="replace")
        used_encoding = "utf-8-replace"

    lines = text.splitlines()
    header_index = None
    for idx, line in enumerate(lines[:100]):
        upper = canonical_header(line)
        # Current CSV uses abbreviated labels such as "Last Insp Date" while
        # the web table says "Last Inspection Date". Detect either form.
        if (
            "NAME" in upper
            and "ADDRESS" in upper
            and ("INSP" in upper or "INSPECTION" in upper)
            and "SCORE" in upper
        ):
            header_index = idx
            break
    if header_index is None:
        preview = repr(text[:240])
        raise ValueError(
            f"CSV export did not contain the expected header row "
            f"(encoding={used_encoding}, preview={preview})"
        )

    body = "\n".join(lines[header_index:])
    sample = body[:8192]
    try:
        dialect = csv.Sniffer().sniff(sample, delimiters=",\t;|")
    except csv.Error:
        dialect = csv.excel

    reader = csv.DictReader(io.StringIO(body), dialect=dialect)
    if not reader.fieldnames:
        raise ValueError("CSV export has no field names")

    # Strip BOM/whitespace from exported column names while retaining the exact
    # strings needed to retrieve DictReader values.
    mapping = map_csv_headers(reader.fieldnames)
    required = {"name", "address", "city", "last_date", "last_score"}
    missing = required - set(mapping)
    if missing:
        raise ValueError(
            f"CSV export missing expected columns: {sorted(missing)}; "
            f"encoding={used_encoding}; delimiter={repr(getattr(dialect, 'delimiter', ','))}; "
            f"got {reader.fieldnames}"
        )

    results = []
    for raw in reader:
        name = normalize_space(raw.get(mapping["name"]))
        address = normalize_space(raw.get(mapping["address"]))
        city = normalize_space(raw.get(mapping["city"]))
        if not name or not address:
            continue
        results.append({
            "name": html_lib.unescape(name),
            "address": html_lib.unescape(address),
            "city": html_lib.unescape(city) or "LEXINGTON",
            "last_inspection_date": iso_date(raw.get(mapping["last_date"])),
            "last_inspection_score": parse_score(raw.get(mapping["last_score"])),
            "followup_date": iso_date(raw.get(mapping.get("follow_date", ""))) if mapping.get("follow_date") else None,
            "followup_score": parse_score(raw.get(mapping.get("follow_score", ""))) if mapping.get("follow_score") else None,
        })

    log(
        f"Parsed CSV export using {used_encoding}, "
        f"delimiter={repr(getattr(dialect, 'delimiter', ','))}: {len(results):,} rows"
    )
    return results


def hidden_form_fields(soup: BeautifulSoup) -> Dict[str, str]:
    data: Dict[str, str] = {}
    for inp in soup.find_all("input", attrs={"type": "hidden"}):
        name = inp.get("name")
        if name:
            data[name] = inp.get("value") or ""
    return data


def form_action_url(current_url: str, soup: BeautifulSoup) -> str:
    form = soup.find("form")
    action = form.get("action") if form else None
    return urljoin(current_url, action) if action else current_url


def get_landing(session: requests.Session) -> Tuple[requests.Response, BeautifulSoup]:
    response = session.get(STATE_URL, headers=HEADERS, timeout=REQUEST_TIMEOUT)
    response.raise_for_status()
    soup = BeautifulSoup(response.text, "html.parser")
    return response, soup


def try_csv_export(session: requests.Session, response: requests.Response, soup: BeautifulSoup) -> List[dict]:
    button_name = "ctl00$PageContent$VW_PUBLIC_EST_INSPExportCSVButton"
    data = hidden_form_fields(soup)
    data[button_name + ".x"] = "1"
    data[button_name + ".y"] = "1"

    export = session.post(
        form_action_url(response.url, soup),
        data=data,
        headers={**HEADERS, "Referer": response.url},
        timeout=REQUEST_TIMEOUT,
    )
    export.raise_for_status()

    content_type = export.headers.get("Content-Type", "").lower()
    disposition = export.headers.get("Content-Disposition", "").lower()
    log(
        f"CSV export response: {len(export.content):,} bytes, "
        f"content-type={content_type or 'unknown'}"
    )

    # Sometimes servers return the HTML page on a failed postback.
    if "text/html" in content_type and "attachment" not in disposition:
        head = export.text[:500].lower()
        if "<html" in head or "__viewstate" in export.text.lower():
            raise ValueError("CSV export button returned HTML instead of CSV")

    rows = rows_from_csv_bytes(export.content)
    if len(rows) < 100:
        raise ValueError(f"CSV export returned only {len(rows)} data rows; expected the full Fayette listing")
    return rows


def find_data_table(soup: BeautifulSoup):
    """Return the innermost 7-column establishment results table.

    The CDP page contains many nested layout tables. Searching recursively for
    NAME/ADDRESS can accidentally select a large outer wrapper, so identify the
    table by one of its *direct* rows instead.
    """
    for table in soup.find_all("table"):
        for tr in table.find_all("tr", recursive=False):
            cells = tr.find_all(["th", "td"], recursive=False)
            if len(cells) != 7:
                continue
            texts = [canonical_header(c.get_text(" ", strip=True)) for c in cells]
            if (
                texts[0] == "NAME"
                and texts[1] == "ADDRESS"
                and texts[2] == "CITY"
                and "INSPECTION DATE" in texts[3]
                and "INSPECTION SCORE" in texts[4]
            ):
                return table
    return None


def rows_from_html(soup: BeautifulSoup) -> List[dict]:
    table = find_data_table(soup)
    if table is None:
        raise ValueError("Could not locate the inspection results table")

    results: List[dict] = []
    # ASP.NET wraps the results table in several other tables. Only inspect
    # direct rows/cells here; recursive find_all() can count nested UI cells as
    # establishments and produce 100+ bogus rows from a 10-row page.
    for tr in table.find_all("tr", recursive=False):
        cells = tr.find_all("td", recursive=False)
        if len(cells) != 7:
            continue
        values = [normalize_space(c.get_text(" ", strip=True)) for c in cells]
        name, address, city, last_date, last_score, follow_date, follow_score = values
        if canonical_header(name) == "NAME" or not name or not address:
            continue
        # A real establishment row has a parseable inspection date or a blank
        # date; reject obvious UI rows accidentally encountered in the table.
        if last_date and not parse_date(last_date):
            continue
        last_codes, last_texts, last_unmapped = violation_details_from_score_cell(cells[4])
        follow_codes, follow_texts, follow_unmapped = violation_details_from_score_cell(cells[6])
        results.append({
            "name": html_lib.unescape(name),
            "address": html_lib.unescape(address),
            "city": html_lib.unescape(city) or "LEXINGTON",
            "last_inspection_date": iso_date(last_date),
            "last_inspection_score": parse_score(last_score),
            "last_violations": last_codes,
            "last_violation_texts": last_texts,
            "last_unmapped_violation_texts": last_unmapped,
            "followup_date": iso_date(follow_date),
            "followup_score": parse_score(follow_score),
            "followup_violations": follow_codes,
            "followup_violation_texts": follow_texts,
            "followup_unmapped_violation_texts": follow_unmapped,
        })
    return results


def pagination_page_count(soup: BeautifulSoup) -> int:
    current = soup.find(id="ctl00_PageContent_VW_PUBLIC_EST_INSPPagination__CurrentPage")
    if current:
        parent_text = normalize_space(current.parent.parent.get_text(" ", strip=True)) if current.parent else ""
        match = re.search(r"\bof\s+(\d+)\b", parent_text, re.I)
        if match:
            return int(match.group(1))
    text = normalize_space(soup.get_text(" ", strip=True))
    match = re.search(r"\bof\s+(\d+)\s+\d+\s+Items\b", text, re.I)
    if match:
        return int(match.group(1))
    return 1


def submit_postback(
    session: requests.Session,
    current_response: requests.Response,
    soup: BeautifulSoup,
    event_target: Optional[str] = None,
    image_button: Optional[str] = None,
    extra: Optional[Dict[str, str]] = None,
) -> Tuple[requests.Response, BeautifulSoup]:
    data = hidden_form_fields(soup)
    if extra:
        data.update(extra)
    if event_target:
        data["__EVENTTARGET"] = event_target
        data["__EVENTARGUMENT"] = ""
    if image_button:
        data[image_button + ".x"] = "1"
        data[image_button + ".y"] = "1"

    response = session.post(
        form_action_url(current_response.url, soup),
        data=data,
        headers={**HEADERS, "Referer": current_response.url},
        timeout=REQUEST_TIMEOUT,
    )
    response.raise_for_status()
    return response, BeautifulSoup(response.text, "html.parser")


def scrape_with_pagination(
    session: requests.Session,
    requested_page_size: int = FALLBACK_PAGE_SIZE,
    delay_seconds: float = FALLBACK_DELAY_SECONDS,
    log_prefix: str = "Fallback",
) -> List[dict]:
    response, soup = get_landing(session)

    # Ask the server for more rows per page. If rejected, the loop still works
    # at the server's current/default page size.
    try:
        response, soup = submit_postback(
            session,
            response,
            soup,
            event_target="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_PageSizeButton",
            extra={"ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_PageSize": str(requested_page_size)},
        )
    except Exception as exc:
        log(f"Could not increase page size ({exc}); continuing with server default")

    pages = pagination_page_count(soup)
    if pages > MAX_FALLBACK_PAGES:
        raise RuntimeError(f"Refusing to scrape {pages} pages; safety limit is {MAX_FALLBACK_PAGES}")

    all_rows: List[dict] = []
    for page_num in range(1, pages + 1):
        page_rows = rows_from_html(soup)
        all_rows.extend(page_rows)
        log(f"{log_prefix} page {page_num}/{pages}: +{len(page_rows)} rows ({len(all_rows):,} total)")
        if page_num >= pages:
            break
        response, soup = submit_postback(
            session,
            response,
            soup,
            image_button="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_NextPage",
        )
        time.sleep(delay_seconds)
    return all_rows


def fetch_state_rows() -> List[dict]:
    with requests.Session() as session:
        session.headers.update(HEADERS)
        response, soup = get_landing(session)
        try:
            rows = try_csv_export(session, response, soup)
            log(f"Downloaded {len(rows):,} Fayette County records via CSV export")

            # CSV has the master rows/scores but NOT violation detail. The live
            # HTML score cells contain violation item titles in rollover markup,
            # so crawl the rendered listing and enrich the CSV rows before merge.
            log("Fetching live violation details from KYEnvPBL HTML...")
            html_rows = scrape_with_pagination(
                session,
                requested_page_size=VIOLATION_PAGE_SIZE,
                delay_seconds=VIOLATION_DELAY_SECONDS,
                log_prefix="Violation detail",
            )
            matched, unmapped = merge_violation_enrichment(rows, html_rows)
            coverage = matched / len(rows) if rows else 0.0
            log(
                f"Violation enrichment matched {matched:,}/{len(rows):,} CSV rows "
                f"({coverage:.1%})"
            )
            if unmapped:
                preview = "; ".join(unmapped[:12])
                log(f"Warning: {len(unmapped)} unique violation title(s) were not mapped to codes: {preview}")
            if REQUIRE_VIOLATION_ENRICHMENT and coverage < 0.95:
                raise RuntimeError(
                    f"Violation enrichment coverage was only {coverage:.1%}; refusing to publish incomplete data"
                )
            return rows
        except Exception as exc:
            # If the CSV itself failed, the HTML fallback remains a complete
            # source for names/scores AND violations. If CSV succeeded but the
            # required violation enrichment failed, do not silently publish a
            # stripped dataset; re-raise instead.
            if 'rows' in locals() and isinstance(locals().get('rows'), list) and len(locals().get('rows')) >= 100:
                raise
            log(f"CSV export unavailable: {exc}")
            log("Falling back to ASP.NET pagination...")
            rows = scrape_with_pagination(session)
            log(f"Downloaded {len(rows):,} Fayette County records via pagination")
            return rows


# -------------------------- Historical-data merge -------------------------


def legacy_snapshot_paths() -> List[Path]:
    """Return every legacy inspection-data JSON available in the repo.

    Both the repo root and inspections/ historically contained snapshots. We
    union all of them so an inspection that existed only in an older snapshot
    (for example a 2023 score with violation details) cannot disappear merely
    because a newer snapshot omitted it.
    """
    paths: List[Path] = []
    seen = set()
    for folder in (REPO_DIR, OUT_DIR):
        for path in folder.glob("inspection_data-*.json"):
            if not path.is_file() or path.name.endswith(".tmp"):
                continue
            resolved = str(path.resolve())
            if resolved not in seen:
                seen.add(resolved)
                paths.append(path)

    # Process stable current master last so its metadata wins when useful.
    paths.sort(key=lambda p: (p.resolve() == MASTER_PATH.resolve(), p.name))
    return paths


def merge_record_metadata(target: dict, incoming: dict) -> None:
    """Fill missing metadata without deleting richer fields already retained."""
    for key, value in incoming.items():
        if key == "inspections":
            continue
        if key not in target or target.get(key) in (None, "", [], {}):
            if value not in (None, "", [], {}):
                target[key] = deepcopy(value)


def union_legacy_snapshots(paths: List[Path]) -> List[dict]:
    merged: List[dict] = []

    for path in paths:
        try:
            data = load_json(path)
        except Exception as exc:
            log(f"Warning: could not read legacy snapshot {path}: {exc}")
            continue
        if not isinstance(data, list):
            log(f"Warning: skipping non-list legacy snapshot {path}")
            continue

        # Build aliases once per snapshot. Newly introduced establishments are
        # also tracked by exact key within this file.
        lookup = previous_lookup(merged) if merged else {}
        added_this_file: Dict[str, dict] = {}
        before_inspections = sum(
            len(r.get("inspections", [])) for r in merged if isinstance(r, dict)
        )

        for incoming in data:
            if not isinstance(incoming, dict):
                continue
            name = normalize_space(incoming.get("name"))
            address = normalize_space(incoming.get("address"))
            city = normalize_space(incoming.get("city")) or "LEXINGTON"
            if not name or not address:
                continue

            exact_key = establishment_key(name, address, city)
            target = (
                find_previous_record(lookup, name, address, city)
                or added_this_file.get(exact_key)
            )

            if target is None:
                target = deepcopy(incoming)
                if not isinstance(target.get("inspections"), list):
                    target["inspections"] = []
                merged.append(target)
                added_this_file[exact_key] = target
            else:
                merge_record_metadata(target, incoming)
                history = target.setdefault("inspections", [])
                if not isinstance(history, list):
                    history = []
                    target["inspections"] = history
                for inspection in incoming.get("inspections", []) or []:
                    if isinstance(inspection, dict):
                        merge_inspection(history, deepcopy(inspection))

        after_inspections = sum(
            len(r.get("inspections", [])) for r in merged if isinstance(r, dict)
        )
        log(
            f"Merged legacy snapshot {path.name}: {len(data):,} establishments; "
            f"history now {after_inspections:,} inspections "
            f"(+{after_inspections - before_inspections:,})"
        )

    return merged


def load_previous_records() -> Tuple[List[dict], bool, Optional[Path]]:
    paths = legacy_snapshot_paths()
    if not paths:
        return [], True, None

    data = union_legacy_snapshots(paths)
    first_new_system_run = not MASTER_PATH.exists()
    source = MASTER_PATH if MASTER_PATH.exists() else paths[-1]
    log(
        f"Historical union: {len(paths)} snapshot(s), {len(data):,} establishments, "
        f"{sum(len(r.get('inspections', [])) for r in data if isinstance(r, dict)):,} inspections"
    )
    return data, first_new_system_run, source


def previous_lookup(records: List[dict]) -> Dict[str, dict]:
    lookup: Dict[str, dict] = {}
    address_candidates: Dict[str, List[dict]] = {}
    name_candidates: Dict[str, List[dict]] = {}

    for record in records:
        if not isinstance(record, dict):
            continue
        name = normalize_space(record.get("name"))
        address = normalize_space(record.get("address"))
        city = normalize_space(record.get("city")) or "LEXINGTON"
        if not name or not address:
            continue

        lookup[establishment_key(name, address, city)] = record
        # Legacy data usually had no city. Keep a Lexington equivalent.
        lookup.setdefault(establishment_key(name, address, "LEXINGTON"), record)

        for candidate_city in {city, "LEXINGTON"}:
            address_candidates.setdefault(address_lookup_key(address, candidate_city), []).append(record)
            name_candidates.setdefault(name_lookup_key(name, candidate_city), []).append(record)

    # Address-only/name-only aliases are safe only when they identify exactly one
    # legacy establishment. This catches harmless renames like
    # "ASHLAND ELEMENTARY" -> "ASHLAND ELEMENTARY SCHOOL" without merging
    # multiple businesses that share an address or chain name.
    for key, candidates in address_candidates.items():
        unique = {id(x): x for x in candidates}
        if len(unique) == 1:
            lookup[key] = next(iter(unique.values()))

    for key, candidates in name_candidates.items():
        unique = {id(x): x for x in candidates}
        if len(unique) == 1:
            lookup[key] = next(iter(unique.values()))

    return lookup


def find_previous_record(lookup: Dict[str, dict], name: str, address: str, city: str) -> Optional[dict]:
    return (
        lookup.get(establishment_key(name, address, city))
        or lookup.get(establishment_key(name, address, "LEXINGTON"))
        or lookup.get(address_lookup_key(address, city))
        or lookup.get(address_lookup_key(address, "LEXINGTON"))
        or lookup.get(name_lookup_key(name, city))
        or lookup.get(name_lookup_key(name, "LEXINGTON"))
    )


def inspection_identity(item: dict) -> Tuple[Any, ...]:
    return (
        item.get("date"),
        normalize_key_text(item.get("inspection_type")),
        item.get("score"),
        normalize_key_text(item.get("category")),
    )


def _merge_unique_list(existing_value: Any, incoming_value: Any) -> Any:
    if not isinstance(existing_value, list) or not isinstance(incoming_value, list):
        return existing_value
    result = deepcopy(existing_value)
    fingerprints = {canonical_json(x) for x in result}
    for item in incoming_value:
        fp = canonical_json(item)
        if fp not in fingerprints:
            result.append(deepcopy(item))
            fingerprints.add(fp)
    return result


def merge_inspection_fields(existing: dict, incoming: dict) -> None:
    """Preserve the richest version of an inspection seen in any snapshot."""
    for key, value in incoming.items():
        if key == "is_new":
            existing[key] = value
            continue
        if isinstance(existing.get(key), list) and isinstance(value, list):
            existing[key] = _merge_unique_list(existing.get(key), value)
            continue
        if key not in existing or existing.get(key) in (None, "", [], {}):
            if value not in (None, "", [], {}):
                existing[key] = deepcopy(value)


def merge_inspection(history: List[dict], inspection: dict) -> bool:
    identity = inspection_identity(inspection)
    incoming_category = normalize_key_text(inspection.get("category"))

    for existing in history:
        if not isinstance(existing, dict):
            continue

        exact_match = inspection_identity(existing) == identity

        # The current KY state export does not expose FOOD/RETAIL category, so
        # incoming records use UNKNOWN. If richer legacy history already has the
        # same event, update that row rather than adding a meaningless UNKNOWN
        # duplicate. Distinct scores, types, categories, or dates are NEVER
        # discarded and remain separate inspection-history entries.
        state_matches_legacy = (
            incoming_category == "UNKNOWN"
            and existing.get("date") == inspection.get("date")
            and normalize_key_text(existing.get("inspection_type"))
                == normalize_key_text(inspection.get("inspection_type"))
            and existing.get("score") == inspection.get("score")
        )

        if exact_match or state_matches_legacy:
            merge_inspection_fields(existing, inspection)
            return False

    history.append(deepcopy(inspection))
    return True


def inspection_sort_key(item: dict) -> Tuple[str, int, int]:
    type_name = normalize_key_text(item.get("inspection_type"))
    priority = {"REGULAR": 1, "COMPLAINT": 2, "FOLLOWUP": 3, "FOLLOW UP": 3}.get(type_name, 0)
    score = item.get("score") if isinstance(item.get("score"), int) else -1
    return (str(item.get("date") or "0000-00-00"), priority, score)


def add_current_state_inspections(record: dict, state_row: dict, today: date) -> int:
    history = record.setdefault("inspections", [])
    if not isinstance(history, list):
        history = []
        record["inspections"] = history

    added = 0
    regular_date = state_row.get("last_inspection_date")
    regular_score = state_row.get("last_inspection_score")
    if regular_date and regular_score is not None:
        inspection = {
            "date": regular_date,
            "inspection_type": "REGULAR",
            "category": "UNKNOWN",
            "score": regular_score,
            "violations": list(state_row.get("last_violations") or []),
            "violation_texts": list(state_row.get("last_violation_texts") or []),
            "unmapped_violation_texts": list(state_row.get("last_unmapped_violation_texts") or []),
            "source": SOURCE_NAME,
            "is_new": within_new_window(regular_date, today),
        }
        added += 1 if merge_inspection(history, inspection) else 0

    follow_date = state_row.get("followup_date")
    follow_score = state_row.get("followup_score")
    if follow_date and follow_score is not None:
        inspection = {
            "date": follow_date,
            "inspection_type": "FOLLOWUP",
            "category": "UNKNOWN",
            "score": follow_score,
            "violations": list(state_row.get("followup_violations") or []),
            "violation_texts": list(state_row.get("followup_violation_texts") or []),
            "unmapped_violation_texts": list(state_row.get("followup_unmapped_violation_texts") or []),
            "source": SOURCE_NAME,
            "is_new": within_new_window(follow_date, today),
        }
        added += 1 if merge_inspection(history, inspection) else 0

    # Recalculate is_new for every historical inspection so it expires automatically after 30 days.
    for inspection in history:
        if isinstance(inspection, dict):
            inspection["is_new"] = within_new_window(inspection.get("date"), today)

    history.sort(key=inspection_sort_key)
    return added


def current_inspection(history: List[dict]) -> Optional[dict]:
    valid = [x for x in history if isinstance(x, dict) and x.get("date") and x.get("score") is not None]
    if not valid:
        return None
    chosen = max(valid, key=inspection_sort_key)
    # Keep the public current summary small; the full inspection remains in history.
    return {
        "id": chosen.get("id"),
        "date": chosen.get("date"),
        "inspection_type": chosen.get("inspection_type"),
        "score": chosen.get("score"),
        "violations": list(chosen.get("violations") or []),
        "violation_texts": list(chosen.get("violation_texts") or []),
        "is_new": bool(chosen.get("is_new")),
        "source": chosen.get("source", "legacy"),
    }


def build_records(state_rows: List[dict], previous: List[dict], first_run: bool, today: date) -> Tuple[List[dict], int]:
    lookup = previous_lookup(previous)
    records: List[dict] = []
    new_inspections_added = 0
    matched_previous_objects = set()

    # Multiple KYEnvPBL rows can represent the same public establishment. Exact
    # name/address matches are grouped, and conservative aliases are collapsed.
    # Every source row is still processed, so distinct scores are never discarded.
    grouped_rows = group_state_rows(state_rows)

    for key, rows_for_establishment in grouped_rows:
        primary = rows_for_establishment[0]
        name = normalize_space(primary.get("name"))
        address = normalize_space(primary.get("address"))
        city = normalize_space(primary.get("city")) or "LEXINGTON"

        prev = find_previous_record(lookup, name, address, city)
        if prev:
            matched_previous_objects.add(id(prev))
            record = deepcopy(prev)
        else:
            record = {
                "permit": stable_state_id(key),
                "name": name,
                "address": address,
                "inspections": [],
            }

        record["name"] = name
        record["address"] = address
        record["city"] = city
        record["county"] = COUNTY_NAME
        record["state_id"] = stable_state_id(key)
        record["source"] = SOURCE_NAME
        record["state_record_count"] = len(rows_for_establishment)
        record["is_active"] = True
        record["last_seen"] = today.isoformat()

        if "first_seen" not in record:
            # Anything already present in historical data predates this sync
            # system and must never be falsely labeled as a newly opened place.
            record["first_seen"] = None if prev or first_run else today.isoformat()

        record["is_new_establishment"] = (
            within_new_window(record.get("first_seen"), today)
            if record.get("first_seen")
            else False
        )

        record["group"] = classify_establishment(name, address, prev)
        ensure_establishment_id(record, key)

        # Do not skip duplicate state rows. Each may carry a different latest or
        # follow-up inspection. merge_inspection() removes only true duplicates.
        for state_row in rows_for_establishment:
            new_inspections_added += add_current_state_inspections(record, state_row, today)

        ensure_inspection_ids(record)
        current = current_inspection(record.get("inspections", []))
        record["current_inspection"] = current
        record["has_new_inspection"] = any(
            bool(x.get("is_new")) for x in record.get("inspections", []) if isinstance(x, dict)
        )
        records.append(record)

    # Preserve every historical establishment even if it no longer appears in
    # the current state export. This is critical for a forensic-style archive:
    # closed/renamed/removed establishments become inactive, not deleted.
    for prev in previous:
        if not isinstance(prev, dict) or id(prev) in matched_previous_objects:
            continue

        record = deepcopy(prev)
        name = normalize_space(record.get("name"))
        address = normalize_space(record.get("address"))
        city = normalize_space(record.get("city")) or "LEXINGTON"
        if not name or not address:
            continue

        key = establishment_key(name, address, city)
        record["city"] = city
        record["county"] = record.get("county") or COUNTY_NAME
        record["is_active"] = False
        record.setdefault("last_seen", None)
        record.setdefault("first_seen", None)
        record["is_new_establishment"] = (
            within_new_window(record.get("first_seen"), today)
            if record.get("first_seen")
            else False
        )
        record["group"] = record.get("group") or classify_establishment(name, address, record)

        # Expire the rolling 30-day flags even on inactive history.
        history = record.get("inspections") or []
        if isinstance(history, list):
            for inspection in history:
                if isinstance(inspection, dict):
                    inspection["is_new"] = within_new_window(inspection.get("date"), today)
            history.sort(key=inspection_sort_key)

        ensure_establishment_id(record, key)
        ensure_inspection_ids(record)
        record["current_inspection"] = current_inspection(history if isinstance(history, list) else [])
        record["has_new_inspection"] = any(
            bool(x.get("is_new")) for x in history if isinstance(x, dict)
        ) if isinstance(history, list) else False
        records.append(record)

    records.sort(key=lambda r: (
        not bool(r.get("is_active", True)),
        normalize_key_text(r.get("name")),
        normalize_address_key(r.get("address")),
    ))
    validate_swiftdata_ids(records)
    return records, new_inspections_added


# ----------------------------- JSON publishing ----------------------------


def comparable_records(records: List[dict]) -> List[dict]:
    return records


def rebuild_legacy_index() -> List[dict]:
    files = [
        p for p in OUT_DIR.glob("inspection_data-*.json")
        if p.is_file() and not p.name.endswith(".tmp")
    ]
    # Keep the stable current file first so older EatLex clients that read the
    # first index entry automatically receive the new data.
    files.sort(
        key=lambda p: (p.name == MASTER_PATH.name, p.stat().st_mtime),
        reverse=True,
    )
    result = []
    for path in files:
        stat = path.stat()
        result.append({
            "file": path.name,
            "size_bytes": stat.st_size,
            "modified": datetime.fromtimestamp(stat.st_mtime).isoformat(),
        })
    return result


def write_category_files(records: List[dict]) -> List[dict]:
    CATEGORY_DIR.mkdir(parents=True, exist_ok=True)
    grouped: Dict[str, List[dict]] = {}
    for record in records:
        grouped.setdefault(record.get("group") or "Other / Uncategorized", []).append(record)

    expected_paths = set()
    category_manifest = []
    for category in sorted(grouped):
        items = grouped[category]
        filename = category_slug(category) + ".json"
        path = CATEGORY_DIR / filename
        # Category files intentionally contain the complete establishment
        # records, including full inspection history and violations. They are
        # not summary-only indexes; no inspection should disappear just because
        # a client chooses a category-specific JSON file.
        atomic_write_json(path, items)
        expected_paths.add(path.resolve())
        category_manifest.append({"name": category, "file": f"categories/{filename}", "count": len(items)})

    # Remove category files that no longer correspond to a category, but keep categories/index.json.
    for path in CATEGORY_DIR.glob("*.json"):
        if path.name == "index.json":
            continue
        if path.resolve() not in expected_paths:
            path.unlink()

    atomic_write_json(CATEGORY_DIR / "index.json", category_manifest)
    return category_manifest


def records_by_id(records: Any) -> Dict[str, dict]:
    if not isinstance(records, list):
        return {}
    return {
        str(r.get("id")): r
        for r in records
        if isinstance(r, dict) and normalize_space(r.get("id"))
    }


def compute_incremental_changes(old_records: Any, new_records: List[dict]) -> Tuple[List[dict], List[str]]:
    old_map = records_by_id(old_records)
    new_map = records_by_id(new_records)

    changed: List[dict] = []
    for record_id, record in new_map.items():
        old = old_map.get(record_id)
        if old is None or canonical_json(old) != canonical_json(record):
            changed.append(record)

    deleted = sorted(set(old_map) - set(new_map))
    return changed, deleted


def publish_json(records: List[dict], new_inspections_added: int, today: date) -> Tuple[bool, Optional[Path]]:
    old_records = None
    if MASTER_PATH.exists():
        try:
            old_records = load_json(MASTER_PATH)
        except Exception:
            old_records = None

    old_version = dataset_version(old_records) if isinstance(old_records, list) else None
    old_schema_version = None
    if METADATA_PATH.exists():
        try:
            old_metadata = load_json(METADATA_PATH)
            if isinstance(old_metadata, dict):
                old_schema_version = old_metadata.get("schema_version")
        except Exception:
            old_schema_version = None
    new_version = dataset_version(records)

    changed = old_records is None or canonical_json(comparable_records(old_records)) != canonical_json(comparable_records(records))
    if not changed:
        log("No published data changes detected; JSON and GitHub will not be touched")
        return False, None

    if old_version is None or old_schema_version != SWIFTDATA_SCHEMA_VERSION:
        # First SwiftData publish OR a sync-schema change requires a full import.
        # Avoid writing a second giant copy of the entire dataset into changes.json.
        changed_records, deleted_ids = [], []
        full_refresh_required = True
    else:
        changed_records, deleted_ids = compute_incremental_changes(old_records, records)
        full_refresh_required = False

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    atomic_write_json(MASTER_PATH, records)

    category_manifest = write_category_files(records)
    atomic_write_json(INDEX_PATH, rebuild_legacy_index())

    total_inspections = sum(
        len(r.get("inspections", []))
        for r in records
        if isinstance(r, dict) and isinstance(r.get("inspections"), list)
    )
    active_count = sum(1 for r in records if bool(r.get("is_active", True)))
    inactive_count = len(records) - active_count
    data_sha = file_sha256(MASTER_PATH)
    generated_at = datetime.now().astimezone().isoformat(timespec="seconds")

    changes = {
        "schema_version": SWIFTDATA_SCHEMA_VERSION,
        "dataset": DATASET_NAME,
        "base_dataset_version": old_version,
        "dataset_version": new_version,
        "generated_at": generated_at,
        "changed_establishment_count": len(changed_records),
        "deleted_establishment_count": len(deleted_ids),
        "full_refresh_required": full_refresh_required,
        "changed_establishments": changed_records,
        "deleted_establishment_ids": deleted_ids,
    }
    atomic_write_json(CHANGES_PATH, changes)
    changes_sha = file_sha256(CHANGES_PATH)

    metadata = {
        # Existing manifest fields retained for compatibility.
        "county": COUNTY_NAME,
        "county_code": COUNTY,
        "source": STATE_URL,
        "source_name": SOURCE_NAME,
        "updated_at": generated_at,
        "new_window_days": NEW_DAYS,
        "total_establishments": len(records),
        "active_establishments": active_count,
        "inactive_historical_establishments": inactive_count,
        "total_inspections": total_inspections,
        "new_establishments": sum(1 for r in records if r.get("is_new_establishment")),
        "establishments_with_new_inspections": sum(1 for r in records if r.get("has_new_inspection")),
        "new_inspection_records_discovered_this_run": new_inspections_added,
        "latest_file": MASTER_PATH.name,
        "categories": category_manifest,

        # SwiftData sync contract.
        "schema_version": SWIFTDATA_SCHEMA_VERSION,
        "dataset": DATASET_NAME,
        "dataset_version": new_version,
        "data_file": MASTER_PATH.name,
        "data_sha256": data_sha,
        "data_size_bytes": MASTER_PATH.stat().st_size,
        "changes_file": CHANGES_PATH.name,
        "changes_sha256": changes_sha,
        "changes_size_bytes": CHANGES_PATH.stat().st_size,
        "changes_base_dataset_version": old_version,
        "changes_establishment_count": len(changed_records),
        "deleted_establishment_count": len(deleted_ids),
        "full_refresh_required": full_refresh_required,
        "record_format": "nested_establishments_with_inspections",
    }
    atomic_write_json(MANIFEST_PATH, metadata)
    atomic_write_json(METADATA_PATH, metadata)

    log(
        f"Published {len(records):,} establishments / {total_inspections:,} inspections "
        f"to {MASTER_PATH} (dataset {new_version[:12]})"
    )
    log(
        f"SwiftData delta: {len(changed_records):,} changed establishments, "
        f"{len(deleted_ids):,} deleted IDs"
    )
    return True, MASTER_PATH


# ------------------------------- GitHub push ------------------------------


def run_git(args: List[str], check: bool = True) -> subprocess.CompletedProcess:
    cmd = ["git", "-C", str(REPO_DIR)] + args
    return subprocess.run(cmd, text=True, capture_output=True, check=check)


def git_sync_before_run() -> None:
    if not (REPO_DIR / ".git").exists():
        log("No .git repository found; GitHub sync skipped")
        return
    log("Syncing local repository with GitHub...")
    result = run_git(["pull", "--rebase", "--autostash", GIT_REMOTE, GIT_BRANCH], check=False)
    if result.returncode != 0:
        message = (result.stderr or result.stdout).strip()
        raise RuntimeError(f"git pull --rebase failed: {message}")
    if result.stdout.strip():
        log(result.stdout.strip().splitlines()[-1])


def git_commit_and_push(snapshot: Optional[Path]) -> bool:
    if not (REPO_DIR / ".git").exists():
        return False

    paths = [
        str(MASTER_PATH.relative_to(REPO_DIR)),
        str(MANIFEST_PATH.relative_to(REPO_DIR)),
        str(METADATA_PATH.relative_to(REPO_DIR)),
        str(CHANGES_PATH.relative_to(REPO_DIR)),
        str(INDEX_PATH.relative_to(REPO_DIR)),
        str(CATEGORY_DIR.relative_to(REPO_DIR)),
    ]
    if snapshot and snapshot != MASTER_PATH:
        paths.append(str(snapshot.relative_to(REPO_DIR)))

    add = run_git(["add", "--"] + paths, check=False)
    if add.returncode != 0:
        raise RuntimeError((add.stderr or add.stdout).strip())

    diff = run_git(["diff", "--cached", "--quiet"], check=False)
    if diff.returncode == 0:
        log("Git has no staged changes")
        return False
    if diff.returncode not in (0, 1):
        raise RuntimeError((diff.stderr or diff.stdout).strip())

    message = f"Update Fayette inspections {date.today().isoformat()}"
    commit = run_git(["commit", "-m", message], check=False)
    if commit.returncode != 0:
        raise RuntimeError((commit.stderr or commit.stdout).strip())
    log("Created Git commit")

    push = run_git(["push", GIT_REMOTE, GIT_BRANCH], check=False)
    if push.returncode != 0:
        raise RuntimeError(f"GitHub push failed: {(push.stderr or push.stdout).strip()}")
    log("✅ GitHub push complete")
    return True


def git_push_existing_commits() -> None:
    """Push any already-committed local work (for example, a prior run whose push failed)."""
    if not (REPO_DIR / ".git").exists():
        return
    push = run_git(["push", GIT_REMOTE, GIT_BRANCH], check=False)
    if push.returncode != 0:
        raise RuntimeError(f"GitHub push failed: {(push.stderr or push.stdout).strip()}")
    output = (push.stderr or push.stdout).strip()
    if output and "Everything up-to-date" not in output:
        log(output.splitlines()[-1])


# --------------------------------- Main -----------------------------------


def main() -> int:
    today = date.today()
    log("Starting Fayette County inspection update")

    # Sync first so we merge against whatever is currently on GitHub.
    git_sync_before_run()

    previous, first_run, previous_source = load_previous_records()
    if previous_source:
        log(f"Previous data source: {previous_source.name} ({len(previous):,} records)")
    else:
        log("No previous JSON found; creating a new baseline")

    state_rows = fetch_state_rows()
    if len(state_rows) < 500:
        raise RuntimeError(
            f"Safety check failed: only {len(state_rows)} Fayette County records were returned. "
            "Refusing to publish a likely partial scrape."
        )

    records, new_inspections_added = build_records(state_rows, previous, first_run, today)
    if len(records) < 500:
        raise RuntimeError(f"Safety check failed after merge: only {len(records)} records")

    changed, snapshot = publish_json(records, new_inspections_added, today)
    if changed:
        git_commit_and_push(snapshot)
    else:
        # This also repairs the case where an earlier run committed locally but its push failed.
        git_push_existing_commits()
        log("✅ Daily check complete; no new JSON changes")

    new_establishments = sum(1 for r in records if r.get("is_new_establishment"))
    new_inspection_locations = sum(1 for r in records if r.get("has_new_inspection"))
    log(
        f"Done: {len(records):,} establishments | "
        f"{new_establishments} new establishments | "
        f"{new_inspection_locations} establishments with an inspection in the last {NEW_DAYS} days"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        log("Interrupted")
        sys.exit(130)
    except Exception as exc:
        log(f"❌ ERROR: {exc}")
        sys.exit(1)
