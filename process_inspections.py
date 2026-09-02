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
  * Creates accurate multi-field V17 classifications with category/type/cuisine/tags.
  * Optionally validates uncertain classifications with Apple Maps Server API Search.
  * Writes needs_review.json and flags likely cross-permit source-data anomalies.
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
NEEDS_REVIEW_PATH = OUT_DIR / "needs_review.json"
CLASSIFICATION_SUMMARY_PATH = OUT_DIR / "classification_summary.json"
CLASSIFICATION_OVERRIDES_PATH = REPO_DIR / "classification_overrides.json"

SWIFTDATA_SCHEMA_VERSION = 3
CLASSIFICATION_VERSION = 17
DATASET_NAME = "EatLex Fayette County Inspections"

NEW_DAYS = 30
REQUEST_TIMEOUT = 60
FALLBACK_PAGE_SIZE = 10
FALLBACK_DELAY_SECONDS = 0.15
# The violation details only exist in the rendered HTML score cells.  The CDP
# page-size box accepts larger values, but its displayed page-count can remain
# stale after a page-size change.  V11 therefore tries large pages first and
# calculates the number of pages from *today's CSV row count* instead of trusting
# the ASP.NET "of N" value.  Any incomplete/duplicated attempt falls back to a
# smaller size; native 10-row paging remains the final safe fallback.
VIOLATION_PAGE_SIZE_CANDIDATES = (1000, 500, 250, 100, 50, 10)
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


def legacy_store_prefix_from_address(address: Any) -> Tuple[str, str]:
    """Return (store_number, cleaned_address) for a very specific legacy artifact.

    Some old LFCHD JSON rows placed a store/location number at the start of the
    address, e.g. ``#6373 1816 ALYSHEBA WAY``, while the current state feed puts
    that number in the establishment name: ``PANERA BREAD #6373`` with address
    ``1816 ALYSHEBA WAY``.  Only a leading ``#`` token followed by a numeric
    street address is treated this way, avoiding ordinary addresses such as
    ``905 905 S LIMESTONE`` or ``125 E REYNOLDS RD``.
    """
    raw = normalize_space(address)
    match = re.match(r"^#\s*([A-Z0-9-]{1,16})\s+(\d+[A-Z]?\b.*)$", raw, re.I)
    if not match:
        return "", raw
    store_number = normalize_key_text(match.group(1))
    cleaned_address = normalize_space(match.group(2))
    return store_number, cleaned_address


def canonical_match_address(address: Any) -> str:
    _store_number, cleaned_address = legacy_store_prefix_from_address(address)
    return normalize_address_key(cleaned_address)


def canonical_match_name(name: Any, address: Any = None) -> str:
    """Return a conservative matching-only establishment name.

    This handles both legacy forms we have observed:
      * address appended to the name, such as
        ``PANERA BREAD - #6373 1816 ALYSHEBA WAY``; and
      * store number prepended to the address, such as name ``PANERA BREAD``
        with address ``#6373 1816 ALYSHEBA WAY``.

    Display names are never changed by this helper.
    """
    name_key = normalize_key_text(name)
    store_number, cleaned_address = legacy_store_prefix_from_address(address) if address else ("", "")
    address_key = normalize_address_key(cleaned_address) if cleaned_address else ""

    # If the old parser misplaced a #store number into the address, move it
    # back into the matching-only name. This makes PANERA BREAD + #6373 ...
    # match PANERA BREAD #6373 + 1816 ....
    if store_number:
        tokens = name_key.split()
        if store_number not in tokens:
            name_key = normalize_space(f"{name_key} {store_number}")

    if not name_key or not address_key:
        return name_key

    # Address normalization changes STREET->ST, ROAD->RD, etc. Normalize the
    # name with the same suffix rules before testing an address tail.
    name_as_address = normalize_address_key(name_key)
    if name_as_address == address_key:
        return name_key
    suffix = f" {address_key}"
    if name_as_address.endswith(suffix):
        stripped = normalize_space(name_as_address[:-len(suffix)])
        if stripped:
            return stripped

    # A few legacy names include a suite/unit suffix in the address field but
    # omit it from the appended name. Strip the base street portion only when
    # it is a clear trailing sequence of at least three tokens including the
    # same leading house number.
    addr_tokens = address_key.split()
    name_tokens = name_as_address.split()
    if len(addr_tokens) >= 3 and len(name_tokens) > len(addr_tokens):
        for n in range(len(addr_tokens), 2, -1):
            tail = addr_tokens[:n]
            if name_tokens[-n:] == tail:
                stripped = normalize_space(" ".join(name_tokens[:-n]))
                if stripped:
                    return stripped
    return name_key


def canonical_match_lookup_key(name: Any, address: Any, city: Any = "LEXINGTON") -> str:
    return "MATCH|" + "|".join([
        canonical_match_name(name, address),
        canonical_match_address(address),
        normalize_key_text(city or "LEXINGTON"),
    ])


def same_establishment_name_variant(name_a: Any, name_b: Any, address_a: Any = None, address_b: Any = None) -> bool:
    """Conservative name-alias test used only when addresses are the same/near-same.

    This intentionally catches aliases such as "ASHLAND ELEMENTARY" vs
    "ASHLAND ELEMENTARY SCHOOL" while refusing to collapse unrelated businesses
    that merely share a building.
    """
    a = canonical_match_name(name_a, address_a)
    b = canonical_match_name(name_b, address_b)
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
                    and same_establishment_name_variant(
                        name, representative.get("name"), address, representative.get("address")
                    )
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
    return "ADDR|" + "|".join([canonical_match_address(address), normalize_key_text(city)])


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


def records_represent_same_establishment(a: dict, b: dict) -> bool:
    """Return True only for conservative aliases of the same physical place."""
    city_a = normalize_key_text(a.get("city") or "LEXINGTON")
    city_b = normalize_key_text(b.get("city") or "LEXINGTON")
    if city_a != city_b:
        return False

    return (
        same_physical_address_for_same_name(a.get("address"), b.get("address"))
        and same_establishment_name_variant(
            a.get("name"), b.get("name"), a.get("address"), b.get("address")
        )
    )


def _earliest_iso_date(*values: Any) -> Optional[str]:
    parsed = [(parse_date(v), normalize_space(v)) for v in values if v]
    parsed = [(d, raw) for d, raw in parsed if d]
    return min(parsed, key=lambda x: x[0])[0].isoformat() if parsed else None


def _latest_iso_date(*values: Any) -> Optional[str]:
    parsed = [(parse_date(v), normalize_space(v)) for v in values if v]
    parsed = [(d, raw) for d, raw in parsed if d]
    return max(parsed, key=lambda x: x[0])[0].isoformat() if parsed else None


def merge_establishment_record(target: dict, incoming: dict) -> None:
    """Merge a duplicate establishment record without discarding inspection history."""
    target_history = target.setdefault("inspections", [])
    if not isinstance(target_history, list):
        target_history = []
        target["inspections"] = target_history

    for inspection in incoming.get("inspections", []) or []:
        if isinstance(inspection, dict):
            merge_inspection(target_history, inspection)

    # Preserve useful alternate labels for troubleshooting/name changes.
    aliases = target.setdefault("aliases", [])
    if not isinstance(aliases, list):
        aliases = []
        target["aliases"] = aliases
    for candidate in (incoming.get("name"), incoming.get("address")):
        value = normalize_space(candidate)
        if value and value not in aliases and value not in (target.get("name"), target.get("address")):
            aliases.append(value)

    target["is_active"] = bool(target.get("is_active")) or bool(incoming.get("is_active"))
    target["state_record_count"] = int(target.get("state_record_count") or 0) + int(incoming.get("state_record_count") or 0)
    target["first_seen"] = _earliest_iso_date(target.get("first_seen"), incoming.get("first_seen"))
    target["last_seen"] = _latest_iso_date(target.get("last_seen"), incoming.get("last_seen"))

    # Keep the richest metadata but never overwrite a useful existing value with blank data.
    for key in ("group", "county", "city", "source", "permit", "state_id"):
        if not target.get(key) and incoming.get(key):
            target[key] = deepcopy(incoming.get(key))


def force_new_establishment_id(record: dict, used_ids: set) -> str:
    """Deterministically re-key a genuinely different place that inherited a duplicate legacy ID."""
    key = establishment_key(
        normalize_space(record.get("name")),
        normalize_space(record.get("address")),
        normalize_space(record.get("city")) or "LEXINGTON",
    )
    seed = f"location|{key}"
    candidate = _stable_hash("est", seed)
    counter = 2
    while candidate in used_ids:
        candidate = _stable_hash("est", f"{seed}|split-{counter}")
        counter += 1

    record["id"] = candidate
    # Inspection IDs are scoped to the establishment ID. Regenerate them only
    # for the re-keyed record so unchanged published IDs stay stable.
    for inspection in record.get("inspections", []) or []:
        if isinstance(inspection, dict):
            inspection.pop("id", None)
    ensure_inspection_ids(record)
    return candidate


def resolve_duplicate_establishment_ids(records: List[dict]) -> List[dict]:
    """Resolve legacy duplicate IDs while preserving all establishment/inspection data.

    Same-place aliases are merged into one record. If two genuinely different
    establishments inherited the same historical ID, the first keeps the
    published ID and the later record receives a deterministic location ID.
    """
    by_id: Dict[str, dict] = {}
    used_ids = set()
    resolved: List[dict] = []
    merged_count = 0
    rekeyed_count = 0

    for record in records:
        record_id = normalize_space(record.get("id"))
        if not record_id:
            key = establishment_key(
                normalize_space(record.get("name")),
                normalize_space(record.get("address")),
                normalize_space(record.get("city")) or "LEXINGTON",
            )
            record_id = ensure_establishment_id(record, key)

        existing = by_id.get(record_id)
        if existing is None:
            by_id[record_id] = record
            used_ids.add(record_id)
            resolved.append(record)
            continue

        if records_represent_same_establishment(existing, record):
            merge_establishment_record(existing, record)
            # Rebuild IDs/current summary after the union so every inspection remains addressable.
            ensure_inspection_ids(existing)
            existing["current_inspection"] = current_inspection(existing.get("inspections", []))
            existing["has_new_inspection"] = any(
                bool(x.get("is_new")) for x in existing.get("inspections", []) if isinstance(x, dict)
            )
            merged_count += 1
            continue

        old_id = record_id
        new_id = force_new_establishment_id(record, used_ids)
        used_ids.add(new_id)
        by_id[new_id] = record
        resolved.append(record)
        record["current_inspection"] = current_inspection(record.get("inspections", []))
        log(
            f"Resolved duplicate establishment ID {old_id}: kept original for "
            f"{existing.get('name')} @ {existing.get('address')}; re-keyed "
            f"{record.get('name')} @ {record.get('address')} as {new_id}"
        )
        rekeyed_count += 1

    if merged_count or rekeyed_count:
        log(
            f"Resolved duplicate establishment IDs: merged {merged_count} same-place alias(es), "
            f"re-keyed {rekeyed_count} distinct establishment(s)"
        )
    return resolved



def force_new_inspection_id(record: dict, inspection: dict, used_ids: set, position: int = 0) -> str:
    """Deterministically re-key an inspection whose published ID collides globally.

    Inspection history is never removed. The seed is scoped to the CURRENT
    establishment ID so an inspection that was previously cloned/inherited from
    another establishment receives a stable ID under the correct establishment.
    """
    establishment_id = normalize_space(record.get("id"))
    if not establishment_id:
        raise ValueError("Establishment ID must be assigned before inspection IDs")

    base_seed = "|".join([
        establishment_id,
        str(inspection.get("date") or ""),
        normalize_key_text(inspection.get("inspection_type")),
        str(inspection.get("score") if inspection.get("score") is not None else ""),
        normalize_key_text(inspection.get("category")),
    ])

    candidate = _stable_hash("insp", base_seed)
    counter = max(2, position + 2)
    while candidate in used_ids:
        candidate = _stable_hash("insp", f"{base_seed}|collision-{counter}")
        counter += 1

    inspection["id"] = candidate
    return candidate


def resolve_duplicate_inspection_ids(records: List[dict]) -> None:
    """Resolve GLOBAL SwiftData inspection-ID collisions without losing history.

    IDs can collide after old establishment aliases are merged/split because an
    inspection may have inherited an ID that was originally scoped to a different
    establishment. The first occurrence keeps its already-published ID for sync
    stability. Every later occurrence is deterministically re-keyed under its
    current establishment.
    """
    used_ids = set()
    owners: Dict[str, Tuple[str, str]] = {}
    rekeyed = 0

    for record in records:
        establishment_id = normalize_space(record.get("id"))
        establishment_label = f"{record.get('name')} @ {record.get('address')}"

        for position, inspection in enumerate(record.get("inspections", []) or []):
            if not isinstance(inspection, dict):
                continue

            inspection_id = normalize_space(inspection.get("id"))
            if not inspection_id:
                new_id = force_new_inspection_id(record, inspection, used_ids, position)
                used_ids.add(new_id)
                owners[new_id] = (establishment_id, establishment_label)
                continue

            if inspection_id not in used_ids:
                used_ids.add(inspection_id)
                owners[inspection_id] = (establishment_id, establishment_label)
                continue

            old_owner = owners.get(inspection_id, ("", "unknown establishment"))[1]
            old_id = inspection_id
            new_id = force_new_inspection_id(record, inspection, used_ids, position)
            used_ids.add(new_id)
            owners[new_id] = (establishment_id, establishment_label)
            rekeyed += 1
            log(
                f"Resolved duplicate inspection ID {old_id}: kept original under "
                f"{old_owner}; re-keyed {inspection.get('date')} "
                f"{inspection.get('inspection_type')} score {inspection.get('score')} under "
                f"{establishment_label} as {new_id}"
            )

    if rekeyed:
        log(f"Resolved duplicate inspection IDs: re-keyed {rekeyed} inspection(s); no history removed")

def validate_swiftdata_ids(records: List[dict]) -> None:
    establishment_ids = set()
    inspection_ids = set()

    for record in records:
        record_id = normalize_space(record.get("id"))
        if not record_id:
            raise RuntimeError(f"Missing establishment ID for {record.get('name')}")
        if record_id in establishment_ids:
            raise RuntimeError(
                f"Duplicate establishment ID remained after resolution: {record_id} "
                f"({record.get('name')} @ {record.get('address')})"
            )
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




# --------------------- V17 establishment classification -------------------
#
# V17 replaces the old single broad ``group`` heuristic with a richer,
# conservative taxonomy.  ``group`` is still written for backwards
# compatibility and mirrors ``primary_category``.
#
# Optional Apple Maps Server API enrichment is used only to validate/resolve
# place type.  Raw Apple place details are not published; only the persistent
# Apple Place ID plus EatLex's own derived classification are retained.

APPLE_MAPS_TOKEN_URL = "https://maps-api.apple.com/v1/token"
APPLE_MAPS_SEARCH_URL = "https://maps-api.apple.com/v1/search"
# Fayette/Lexington search box: north,east,south,west.  Required priority keeps
# same-named chains in other cities from winning a search.
APPLE_LEXINGTON_SEARCH_REGION = "38.22,-84.25,37.84,-84.76"
APPLE_MIN_MATCH_SCORE = 0.74
APPLE_RECHECK_DAYS = 30
APPLE_REQUEST_DELAY_SECONDS = 0.04

PRIMARY_CATEGORIES = [
    "Restaurants",
    "Fast Food & Fast Casual",
    "Coffee & Cafes",
    "Bakery & Desserts",
    "Bars & Nightlife",
    "Breweries & Distilleries",
    "Grocery & Supermarkets",
    "Convenience & Gas",
    "Specialty Food & Markets",
    "Food Trucks & Mobile",
    "Catering & Commissaries",
    "Concessions & Event Food",
    "Retail Food & Vending",
    "Schools & Universities",
    "Childcare",
    "Healthcare & Senior Living",
    "Hotels & Lodging",
    "Pools & Aquatics",
    "Recreation & Clubs",
    "Farms & Farmers Markets",
    "Body Art & Personal Services",
    "Community & Institutional",
    "Other / Needs Review",
]

FAST_FOOD_BRANDS = {
    "MCDONALD": "American / Burgers",
    "BISHOP S SMASH BURGERS": "American / Burgers",
    "BURGER KING": "American / Burgers",
    "WENDY": "American / Burgers",
    "CULVER": "American / Burgers",
    "SONIC": "American / Burgers",
    "WHITE CASTLE": "American / Burgers",
    "RALLY": "American / Burgers",
    "CHECKERS": "American / Burgers",
    "FIVE GUYS": "American / Burgers",
    "FREDDY": "American / Burgers",
    "A AND W": "American / Burgers",
    "A W BURGERS": "American / Burgers",
    "CHICK FIL A": "Chicken",
    "KENTUCKY FRIED CHICKEN": "Chicken",
    "KFC": "Chicken",
    "POPEYES": "Chicken",
    "RAISING CANE": "Chicken",
    "ZAXBY": "Chicken",
    "DAVE S HOT CHICKEN": "Chicken",
    "TACO BELL": "Mexican / Latin",
    "CHIPOTLE": "Mexican / Latin",
    "CHIPOLTE": "Mexican / Latin",
    "QDOBA": "Mexican / Latin",
    "PANERA": "American / Sandwiches",
    "SUBWAY": "American / Sandwiches",
    "JIMMY JOHN": "American / Sandwiches",
    "JERSEY MIKE": "American / Sandwiches",
    "FIREHOUSE SUB": "American / Sandwiches",
    "ARBY S": "American / Sandwiches",
    "ARBYS": "American / Sandwiches",
    "PENN STATION": "American / Sandwiches",
    "LITTLE CAESAR": "Pizza / Italian",
    "PAPA JOHN": "Pizza / Italian",
    "DOMINO": "Pizza / Italian",
    "DONATO": "Pizza / Italian",
    "JET S PIZZA": "Pizza / Italian",
    "BLAZE PIZZA": "Pizza / Italian",
    "DAIRY QUEEN": "American / Burgers",
}

COFFEE_BRANDS = (
    "STARBUCKS", "7 BREW", "DUTCH BROS", "DUTCH BROTHERS", "DUNKIN",
    "BIGGBY", "SCOOTER S COFFEE", "A CUP OF COMMONWEALTH", "COMMON GROUNDS",
    "COFFEE TIMES", "NORTH LIME COFFEE", "LEESTOWN COFFEE", "OLD SCHOOL COFFEE",
    "4TH LEVEL ROASTERS", "AMANDAS CUP OF JOE", "BLUEGRASS BEAN", "BETTER BLEND",
)

GROCERY_BRANDS = (
    "KROGER", "PUBLIX", "ALDI", "WHOLE FOODS", "TRADER JOE", "WALMART",
    "WAL MART", "MEIJER", "COSTCO", "SAM S CLUB", "SAMS CLUB", "FRESH MARKET",
)

GAS_BRANDS = (
    "SPEEDWAY", "CIRCLE K", "THORNTON", "MARATHON", "SHELL", "SUNOCO", "CASEYS", "CASEY S",
    "EXXON", "MOBIL", "REDI MART", "HUCKS STORE", "HUCK S STORE", "MINIT MART",
)

POOL_VIOLATION_MARKERS = (
    "PH 7 2 7 8", "DISINFECTANT FREE RESIDUAL", "DISINFECTANT COMBINED RESIDUAL",
    "PERIMETER OVERFLOW", "SKIMMERS", "MAIN DRAIN", "RECIRCULATING PIPING",
    "BOTTOM SIDEWALLS DECK", "OPERATOR TESTING FREQUENCY", "POOL WATER",
    "LADDERS STEPS HANDRAILS", "SPA TIME SWITCH", "DECK DRAINAGE",
)
HOTEL_VIOLATION_MARKERS = (
    "BEDDING MATERIALS", "MATTRESS", "DRAPES FURNITURE", "CLEAN AND SOILED LINEN",
    "GUEST ROOM", "LINEN STORAGE", "SAFETY AND FIRE HAZARDS",
)
BODY_ART_VIOLATION_MARKERS = (
    "TATTOO", "PIERCING", "AUTOCLAVE", "STERILIZATION", "BODY ART", "NEEDLE",
)


def _contains_any(text: str, terms: Iterable[str]) -> bool:
    padded = f" {normalize_key_text(text)} "
    for term in terms:
        key = normalize_key_text(term)
        if key and f" {key} " in padded:
            return True
    return False


def inspection_program_domain(inspection: Any) -> str:
    if not isinstance(inspection, dict):
        return "unknown"
    raw = " ".join(
        normalize_key_text(x)
        for x in (inspection.get("violation_texts") or inspection.get("unmapped_violation_texts") or [])
    )
    if raw and any(marker in raw for marker in POOL_VIOLATION_MARKERS):
        return "pool"
    if raw and any(marker in raw for marker in HOTEL_VIOLATION_MARKERS):
        return "hotel"
    if raw and any(marker in raw for marker in BODY_ART_VIOLATION_MARKERS):
        return "body_art"
    category = normalize_key_text(inspection.get("category"))
    if inspection.get("violations") or category in {"FOOD", "RETAIL"}:
        return "food"
    return "unknown"


def establishment_programs(record: dict) -> List[str]:
    values = {
        inspection_program_domain(i)
        for i in (record.get("inspections") or [])
        if isinstance(i, dict)
    }
    values.discard("unknown")
    return sorted(values)


def current_program_domain(record: dict) -> str:
    return inspection_program_domain(record.get("current_inspection") or {})


def cuisine_from_name(name: Any) -> Optional[str]:
    text = f" {normalize_key_text(name)} "
    rules = [
        ("Mexican / Latin", ("MEXICAN", "TAQUERIA", "TACO", "BURRITO", "CHURRERIA", "ANTOJITO", "CANTINA", "QUESADILLA")),
        ("Chinese", ("CHINESE", "CHINA ", " WOK ", "SZECHUAN", "SICHUAN", "DIM SUM")),
        ("Japanese / Sushi", ("SUSHI", "RAMEN", "HIBACHI", "JAPANESE", "TERIYAKI")),
        ("Thai", ("THAI",)),
        ("Indian / South Asian", ("INDIAN", "NEPALI", "NEPAL", "HIMALAYAN", "BIRYANI", "TANDOOR")),
        ("Mediterranean / Greek / Middle Eastern", ("GREEK", "MEDITERRANEAN", "GYRO", "HALAL", "KEBAB", "SHAWARMA", "FALAFEL", "ATHENIAN")),
        ("Korean", ("KOREAN",)),
        ("Vietnamese", ("VIETNAMESE", " PHO ")),
        ("Caribbean / Cuban", ("CARIBBEAN", "CUBANO", "CUBAN", "JAMAICAN", "JERK")),
        ("African / Ethiopian", ("ETHIOPIAN", "AFRICAN")),
        ("Cajun / Creole", ("CAJUN", "CREOLE", "BOURBON N TOULOUSE")),
        ("BBQ", (" BBQ", "BARBECUE", "BARBEQUE")),
        ("Seafood", ("SEAFOOD", "FISH HOUSE", "CRAB", "LOBSTER")),
        ("Steakhouse", ("STEAKHOUSE", "STEAK HOUSE")),
        ("Pizza / Italian", ("PIZZA", "PIZZERIA", "ITALIAN", "PASTA")),
        ("Chicken / Wings", ("CHICKEN", "WINGS")),
        ("Burgers", ("BURGER",)),
        ("Breakfast / Brunch", ("BREAKFAST", "BRUNCH", "FIRST WATCH", "WAFFLE", "IHOP")),
    ]
    for cuisine, terms in rules:
        if any(normalize_key_text(term) in text for term in terms):
            return cuisine
    return None


def classification_result(primary: str, establishment_type: str, cuisine: Optional[str],
                          tags: Optional[List[str]], confidence: float, source: str,
                          reason: str) -> dict:
    return {
        "primary_category": primary,
        "establishment_type": establishment_type,
        "cuisine": cuisine,
        "tags": sorted(set(tags or [])),
        "classification_confidence": round(max(0.0, min(1.0, confidence)), 3),
        "classification_source": source,
        "classification_reason": reason,
    }


def local_classification_v17(record: dict) -> dict:
    name = normalize_key_text(record.get("name"))
    text = f" {name} "
    legacy_group = normalize_space(record.get("group"))
    current_domain = current_program_domain(record)
    programs = set(establishment_programs(record))
    cuisine = cuisine_from_name(name)

    # Explicit program/facility names beat mixed historical inspection domains.
    if _contains_any(text, ("POOL", "AQUATIC", "AQUA TOTS", "SWIM", "WADING", "SPRAYGROUND", "SPLASH PAD", "OUTDOOR SPA", "INDOOR SPA", "COLD PLUNGE", "HOT PLUNGE", "HYDROTHERAPY")) or (
        current_domain == "pool" and _contains_any(text, ("OUTDOOR", "INDOOR", "APARTMENTS", "CONDOMINIUM", "TOWNHOMES", "CLUBHOUSE"))
    ):
        subtype = "Spa / Plunge" if _contains_any(text, ("SPA", "PLUNGE", "HYDROTHERAPY")) else (
            "Indoor Pool" if " INDOOR " in text else ("Outdoor Pool" if " OUTDOOR " in text else "Pool / Aquatic Facility")
        )
        return classification_result("Pools & Aquatics", subtype, None, ["Aquatic Facility"], 0.98, "rules", "explicit aquatic facility name/domain")

    if _contains_any(text, ("TATTOO", "TATTOOS", "PIERCING", "BODY ART", "MICROBLADING", "PERMANENT MAKEUP", "BROW BOUTIQUE", "BROWS", "INK STUDIO", "INK TATTOO", "NAIL SPA", "NAILS N LASHES")):
        return classification_result("Body Art & Personal Services", "Body Art / Personal Service", None, [], 0.97, "rules", "body-art/personal-service name")

    if _contains_any(text, ("CHILD CARE", "CHILDCARE", "DAYCARE", "DAY CARE", "EARLY LEARNING", "HEAD START", "PRESCHOOL", "MONTESSORI")):
        return classification_result("Childcare", "Childcare / Preschool", None, [], 0.96, "rules", "childcare/preschool name")

    if _contains_any(text, ("ELEMENTARY", "MIDDLE SCHOOL", "HIGH SCHOOL", "SENIOR HIGH", "SCHOOL", "ACADEMY", "UNIVERSITY", "COLLEGE", "AGRISCIENCE CENTER")):
        subtype = "Elementary School" if "ELEMENTARY" in text else (
            "Middle School" if "MIDDLE SCHOOL" in text else (
                "High School" if "HIGH SCHOOL" in text else (
                    "University / College" if _contains_any(text, ("UNIVERSITY", "COLLEGE")) else "School / Academy"
                )
            )
        )
        return classification_result("Schools & Universities", subtype, None, [], 0.95, "rules", "school/university name")

    if _contains_any(text, ("HOSPITAL", "HEALTH CARE", "HEALTHCARE", "NURSING", "SENIOR LIVING", "ASSISTED LIVING", "ADULT DAY", "MEDICAL CENTER", "REHAB", "RETIREMENT")):
        return classification_result("Healthcare & Senior Living", "Healthcare / Senior Living", None, [], 0.94, "rules", "healthcare/senior-living name")

    if _contains_any(text, ("STATE MOBILE", "FOOD TRUCK", "SELF CONTAINED MOBILE", "MOBILE CART", "MOBILE VENDOR", "ON WHEEL", "CHILL WAGON")) or (
        " MOBILE " in text and "MOBILE HOME" not in text
    ):
        return classification_result("Food Trucks & Mobile", "Mobile Food Vendor", cuisine, ["Mobile"], 0.97, "rules", "mobile-food wording")

    if any(brand in text for brand in COFFEE_BRANDS) or _contains_any(text, ("COFFEE", "ROASTER", "ROASTERS", "CAFE", "TEA HOUSE", "BOBA", "MATCHA", "NUTRITION", "SMOOTHIE", "JUICE")):
        return classification_result("Coffee & Cafes", "Coffee / Cafe", "Coffee / Cafe", ["Beverages"], 0.95, "rules", "coffee/cafe brand or wording")

    if _contains_any(text, ("BAKERY", "BAKE SHOP", "DONUT", "DOUGHNUT", "ICE CREAM", "CREAMERY", "BASKIN ROBBINS", "FROZEN CUSTARD", "FUDGE", "CRUMBL", "COOKIE", "CAKE", "DESSERT", "CANDY", "SWEET SHOP", "PRETZEL", "SHAVED ICE", "KETTLE CORN", "PASTRY")):
        return classification_result("Bakery & Desserts", "Bakery / Dessert", "Bakery / Desserts", ["Dessert"], 0.95, "rules", "bakery/dessert wording")

    for brand, brand_cuisine in FAST_FOOD_BRANDS.items():
        if brand in text:
            return classification_result("Fast Food & Fast Casual", "Fast Food / Fast Casual", brand_cuisine, ["Chain"], 0.98, "brand", f"recognized brand: {brand}")

    if any(brand in text for brand in GROCERY_BRANDS) or _contains_any(text, ("GROCERY", "SUPERMARKET")):
        return classification_result("Grocery & Supermarkets", "Grocery / Supermarket", None, ["Retail Food"], 0.96, "rules", "grocery/supermarket brand or wording")

    if any(brand in text for brand in GAS_BRANDS) or _contains_any(text, ("GAS STATION", "FOOD MART", "FUEL CENTER", "BP FOOD", " BP ")):
        return classification_result("Convenience & Gas", "Convenience / Gas", None, ["Retail Food"], 0.95, "rules", "gas/convenience brand or wording")

    if _contains_any(text, ("MEAT MARKET", "SEAFOOD MARKET", "INTERNATIONAL MARKET", "FOOD MARKET")) or (
        " MARKET " in text and not _contains_any(text, ("WORLD MARKET", "FARMERS MARKET", "MARKETPLACE"))
    ):
        return classification_result("Specialty Food & Markets", "Specialty Food Market", cuisine, ["Retail Food"], 0.86, "rules", "specialty market wording")

    if _contains_any(text, ("COMMISSARY", "CATERING", "CATERER", "BANQUET", "TASTEFUL GATHERINGS")):
        return classification_result("Catering & Commissaries", "Catering / Commissary", cuisine, [], 0.94, "rules", "catering/commissary wording")

    if _contains_any(text, ("CONCESSION", "CONCESSIONS", "SNACK BAR", "AUXILIARY STAND", "FOOD STAND", "GRAB AND GO", "BREAKROOM")) and "FOOD BANK" not in text:
        return classification_result("Concessions & Event Food", "Concession / Event Food", cuisine, [], 0.92, "rules", "concession/event-food wording")

    if _contains_any(text, ("BREWERY", "BREWING", "BEWING", "DISTILLERY", "WINERY", "TAPROOM", "TAP ROOM")):
        return classification_result("Breweries & Distilleries", "Brewery / Distillery / Winery", None, ["Alcohol"], 0.97, "rules", "brewery/distillery/winery wording")

    restaurant_terms = (
        "RESTAURANT", "GRILL", "KITCHEN", "PIZZA", "PIZZERIA", "SUSHI", "STEAK", "BISTRO", "DINER",
        "BBQ", "BARBECUE", "BARBEQUE", "TAQUERIA", "TACO", "WINGS", "CHICKEN", "BURGER", "BURGERS", "SEAFOOD",
        "RAMEN", "THAI", "INDIAN", "MEXICAN", "CHINESE", "BUFFET", "GYRO", "HALAL", "DELI", "EATERY",
        "FOOD AND DRINK", "CANTINA", "NOODLE", "WAFFLE", "CUISINE", "EMPANADA", "HOT DOG", "DAWGS", "BISCUIT BELLY", "DRAGON FEAST", "ROASTED CORN",
        "SMASHING TOMATO", "WHICH WICH", "SOUTHERN EATS", "MUNCHIES",
    )
    if _contains_any(text, restaurant_terms):
        return classification_result("Restaurants", "Restaurant", cuisine, [], 0.94, "rules", "restaurant/cuisine wording")

    if _contains_any(text, (" BAR ", "PUB", "TAVERN", "LOUNGE", "COCKTAIL", "NIGHTCLUB")):
        return classification_result("Bars & Nightlife", "Bar / Pub / Lounge", cuisine, ["Nightlife"], 0.92, "rules", "bar/nightlife wording")

    # Hotels are intentionally after explicit restaurant/bar rules: a named
    # hotel restaurant can remain a restaurant, while hotel facility permits
    # remain under lodging.
    if _contains_any(text, ("HOTEL", "MOTEL", "INN", "SUITES", "LODGE", "EXTENDED STAY", "MICROTEL", "RESIDENCE INN", "HOME2", "HOMEWOOD", "HAMPTON", "MARRIOTT", "HYATT", "HILTON", "LA QUINTA", "FAIRFIELD", "CANDLEWOOD", "STAYBRIDGE", "21C")):
        subtype = "Hotel Food Service" if current_domain == "food" else "Hotel / Lodging"
        return classification_result("Hotels & Lodging", subtype, None, [], 0.94, "rules", "hotel/lodging name")

    if _contains_any(text, ("FARMERS MARKET", "FARMER S MARKET", " FARM ", " FARMS", "ORCHARD", "HERB FARM", "MUSHROOMS")):
        return classification_result("Farms & Farmers Markets", "Farm / Farmers Market", None, [], 0.90, "rules", "farm/farmers-market wording")

    if _contains_any(text, ("GOLF", "COUNTRY CLUB", "TENNIS", "RECREATION", "REC CENTER", "MARTIAL ARTS", "CAMP ", "YOUTH CAMP", "BALLPARK", "STADIUM", "HUNT CLUB")):
        return classification_result("Recreation & Clubs", "Recreation / Club", None, [], 0.87, "rules", "recreation/club wording")

    if _contains_any(text, ("CHURCH", "CORRECTION", "JAIL", "FOOD BANK", "FOOD PANTRY", "SHELTER", "SALVATION ARMY")):
        return classification_result("Community & Institutional", "Institution / Community", None, [], 0.90, "rules", "community/institution wording")

    # Names ending in OUTDOOR/INDOOR are overwhelmingly pool permits on this
    # public-health listing. Do this late so explicit restaurants/mobile food
    # and lodging facilities already had a chance to classify.
    if (_contains_any(text, ("OUTDOOR", "INDOOR")) and current_domain != "food"):
        return classification_result("Pools & Aquatics", "Pool / Aquatic Facility", None, ["Aquatic Facility"], 0.80, "rules+inspection", "public-health facility name uses indoor/outdoor aquatic convention")

    # Personal-service terms that are less specific than tattoo/piercing.
    if _contains_any(text, ("AESTHET", "SKIN", "BROW", "LASH", "NAIL", "PERMANENT MAKEUP", "ART COLLECTIVE")) or current_domain == "body_art":
        return classification_result("Body Art & Personal Services", "Personal Service", None, [], 0.82, "rules", "personal-service wording/domain")

    # Apartment/condo permits with current pool-domain data are aquatic permits
    # even when the word POOL isn't in the public premise name.
    if current_domain == "pool" or (
        _contains_any(text, ("APARTMENTS", "APT", "CONDOMINIUM", "CONDOS", "TOWNHOMES", "SUBDIVISION"))
        and _contains_any(text, ("OUTDOOR", "INDOOR"))
    ):
        return classification_result("Pools & Aquatics", "Pool / Aquatic Facility", None, ["Residential Pool"], 0.85, "inspection+rules", "aquatic inspection domain/residential facility")

    if current_domain == "hotel":
        return classification_result("Hotels & Lodging", "Hotel / Lodging", None, [], 0.78, "inspection", "hotel inspection domain")

    if legacy_group == "Hotels & Lodging":
        return classification_result("Hotels & Lodging", "Hotel / Lodging", None, [], 0.68, "legacy", "legacy category fallback")
    if legacy_group == "Pools & Recreation":
        return classification_result("Pools & Aquatics", "Pool / Aquatic Facility", None, [], 0.68, "legacy", "legacy category fallback")
    if legacy_group == "Fast Food & Fast Casual":
        return classification_result("Fast Food & Fast Casual", "Fast Food / Fast Casual", cuisine, [], 0.72, "legacy", "legacy category fallback")
    if legacy_group == "Coffee, Bakery & Desserts":
        return classification_result("Coffee & Cafes", "Coffee / Cafe", cuisine, [], 0.68, "legacy", "legacy category fallback")
    if legacy_group == "Grocery & Markets":
        return classification_result("Specialty Food & Markets", "Food Market / Retail", None, ["Retail Food"], 0.64, "legacy", "legacy category fallback")
    if legacy_group == "Convenience & Gas":
        return classification_result("Convenience & Gas", "Convenience / Gas", None, ["Retail Food"], 0.64, "legacy", "legacy category fallback")
    if legacy_group == "Bars, Breweries & Distilleries":
        return classification_result("Bars & Nightlife", "Bar / Nightlife", cuisine, ["Nightlife"], 0.64, "legacy", "legacy category fallback")
    if legacy_group in {"Restaurants & Food Establishments", "Restaurants & Dining"} and ("food" in programs or current_domain == "food"):
        return classification_result("Restaurants", "Food Establishment", cuisine, [], 0.70, "legacy+inspection", "legacy food category plus food inspection history")

    if current_domain == "food" or "food" in programs:
        # Workplace cafeterias, vending rooms, specialty retail, etc. land here
        # instead of being incorrectly called restaurants.
        return classification_result("Retail Food & Vending", "Food / Retail Permit", None, ["Food Permit"], 0.55, "inspection", "food inspection history without a reliable business-type cue")

    return classification_result("Other / Needs Review", "Unknown", None, [], 0.20, "unclassified", "no reliable deterministic classification")


def load_classification_overrides() -> dict:
    if not CLASSIFICATION_OVERRIDES_PATH.exists():
        return {}
    try:
        data = load_json(CLASSIFICATION_OVERRIDES_PATH)
        return data if isinstance(data, dict) else {}
    except Exception as exc:
        log(f"Warning: could not read classification_overrides.json: {exc}")
        return {}


def override_for_record(record: dict, overrides: dict) -> Optional[dict]:
    if not overrides:
        return None
    record_id = normalize_space(record.get("id"))
    if record_id and isinstance(overrides.get(record_id), dict):
        return overrides[record_id]
    key = canonical_match_lookup_key(record.get("name"), record.get("address"), record.get("city") or "LEXINGTON")
    if isinstance(overrides.get(key), dict):
        return overrides[key]
    return None


def apply_override(base: dict, override: dict) -> dict:
    result = dict(base)
    for key in ("primary_category", "establishment_type", "cuisine", "tags"):
        if key in override:
            result[key] = deepcopy(override.get(key))
    result["classification_confidence"] = 1.0
    result["classification_source"] = "manual_override"
    result["classification_reason"] = normalize_space(override.get("note")) or "classification_overrides.json"
    return result


APPLE_POI_TO_PRIMARY = {
    "Restaurant": "Restaurants",
    "Cafe": "Coffee & Cafes",
    "Bakery": "Bakery & Desserts",
    "Brewery": "Breweries & Distilleries",
    "Distillery": "Breweries & Distilleries",
    "Winery": "Breweries & Distilleries",
    "Nightlife": "Bars & Nightlife",
    "FoodMarket": "Specialty Food & Markets",
    "GasStation": "Convenience & Gas",
    "School": "Schools & Universities",
    "University": "Schools & Universities",
    "Hospital": "Healthcare & Senior Living",
    "Hotel": "Hotels & Lodging",
    "Swimming": "Pools & Aquatics",
    "Golf": "Recreation & Clubs",
    "Tennis": "Recreation & Clubs",
    "FitnessCenter": "Recreation & Clubs",
    "Stadium": "Recreation & Clubs",
    "ReligiousSite": "Community & Institutional",
}


class AppleMapsClient:
    def __init__(self):
        self.access_token = normalize_space(os.environ.get("APPLE_MAPS_ACCESS_TOKEN"))
        self.auth_token = normalize_space(os.environ.get("APPLE_MAPS_AUTH_TOKEN"))
        self.team_id = normalize_space(os.environ.get("APPLE_MAPS_TEAM_ID"))
        self.key_id = normalize_space(os.environ.get("APPLE_MAPS_KEY_ID"))
        self.private_key_path = normalize_space(os.environ.get("APPLE_MAPS_PRIVATE_KEY_PATH"))
        token_file = normalize_space(os.environ.get("APPLE_MAPS_AUTH_TOKEN_FILE"))
        if not self.auth_token and token_file:
            try:
                self.auth_token = normalize_space(Path(token_file).read_text())
            except Exception as exc:
                log(f"Warning: could not read APPLE_MAPS_AUTH_TOKEN_FILE: {exc}")
        self.enabled = bool(
            self.access_token or self.auth_token
            or (self.team_id and self.key_id and self.private_key_path)
        )
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": HEADERS["User-Agent"], "Accept": "application/json"})
        self.mode = normalize_space(os.environ.get("APPLE_MAPS_ENRICH_MODE") or "uncertain").lower()
        if self.mode not in {"uncertain", "all", "off"}:
            self.mode = "uncertain"
        if self.mode == "off":
            self.enabled = False
        self.calls = 0
        self.matches = 0
        self.failures = 0

    def _dynamic_auth_token(self) -> str:
        if not (self.team_id and self.key_id and self.private_key_path):
            return ""
        try:
            import jwt  # PyJWT; install with: python3 -m pip install pyjwt cryptography
            key = Path(self.private_key_path).read_text()
            now = int(time.time())
            return jwt.encode(
                {
                    "iss": self.team_id,
                    "iat": now,
                    "exp": now + 20 * 60,
                    "scope": "server_api",
                },
                key,
                algorithm="ES256",
                headers={"kid": self.key_id, "typ": "JWT"},
            )
        except Exception as exc:
            log(f"Warning: could not generate Apple Maps server JWT: {exc}")
            return ""

    def ensure_access_token(self) -> bool:
        if not self.enabled:
            return False
        if self.access_token:
            return True
        if not self.auth_token:
            self.auth_token = self._dynamic_auth_token()
        if not self.auth_token:
            self.enabled = False
            return False
        try:
            response = self.session.get(
                APPLE_MAPS_TOKEN_URL,
                headers={"Authorization": f"Bearer {self.auth_token}"},
                timeout=REQUEST_TIMEOUT,
            )
            response.raise_for_status()
            payload = response.json()
            self.access_token = normalize_space(payload.get("accessToken"))
            if not self.access_token:
                raise RuntimeError("Apple token response did not contain accessToken")
            return True
        except Exception as exc:
            log(f"Warning: Apple Maps token exchange failed; continuing with local classification: {exc}")
            self.enabled = False
            return False

    @staticmethod
    def _place_address(place: dict) -> str:
        structured = place.get("structuredAddress") or {}
        full = normalize_space(structured.get("fullThoroughfare"))
        if full:
            return full
        lines = place.get("formattedAddressLines") or []
        return normalize_space(lines[0]) if lines else ""

    @staticmethod
    def _match_score(record: dict, place: dict) -> float:
        record_name = canonical_match_name(record.get("name"), record.get("address"))
        place_name = canonical_match_name(place.get("name"), AppleMapsClient._place_address(place))
        record_address = canonical_match_address(record.get("address"))
        place_address = canonical_match_address(AppleMapsClient._place_address(place))
        if not place_name or not place_address:
            return 0.0
        name_ratio = SequenceMatcher(None, record_name, place_name).ratio()
        address_ratio = SequenceMatcher(None, record_address, place_address).ratio()
        record_house = address_house_number(record_address)
        place_house = address_house_number(place_address)
        if record_house and place_house and record_house != place_house:
            return min(0.45, 0.45 * name_ratio + 0.10 * address_ratio)
        return 0.46 * name_ratio + 0.54 * address_ratio

    def search(self, record: dict) -> Optional[dict]:
        if not self.ensure_access_token():
            return None
        query = f"{normalize_space(record.get('name'))}, {normalize_space(record.get('address'))}, Lexington, KY"
        params = {
            "q": query,
            "limitToCountries": "US",
            "resultTypeFilter": "Poi",
            "lang": "en-US",
            "searchRegion": APPLE_LEXINGTON_SEARCH_REGION,
            "searchRegionPriority": "required",
        }
        try:
            response = self.session.get(
                APPLE_MAPS_SEARCH_URL,
                params=params,
                headers={"Authorization": f"Bearer {self.access_token}"},
                timeout=REQUEST_TIMEOUT,
            )
            self.calls += 1
            if response.status_code == 401 and self.auth_token:
                self.access_token = ""
                if self.team_id and self.key_id and self.private_key_path:
                    self.auth_token = self._dynamic_auth_token()
                if self.ensure_access_token():
                    response = self.session.get(
                        APPLE_MAPS_SEARCH_URL,
                        params=params,
                        headers={"Authorization": f"Bearer {self.access_token}"},
                        timeout=REQUEST_TIMEOUT,
                    )
                    self.calls += 1
            if response.status_code == 429:
                log("Warning: Apple Maps daily quota/rate limit reached; stopping Apple enrichment for this run")
                self.enabled = False
                return None
            response.raise_for_status()
            payload = response.json()
            results = payload.get("results") or []
            scored = [(self._match_score(record, p), p) for p in results if isinstance(p, dict)]
            if not scored:
                return None
            score, place = max(scored, key=lambda x: x[0])
            if score < APPLE_MIN_MATCH_SCORE:
                return None
            self.matches += 1
            return {
                "place_id": normalize_space(place.get("identifier") or place.get("id")),
                "poi_category": normalize_space(place.get("poiCategory")),
                "match_score": round(score, 3),
            }
        except Exception as exc:
            self.failures += 1
            log(f"Apple Maps lookup failed for {record.get('name')} @ {record.get('address')}: {exc}")
            return None
        finally:
            if APPLE_REQUEST_DELAY_SECONDS:
                time.sleep(APPLE_REQUEST_DELAY_SECONDS)


def apple_check_due(record: dict, base: dict, client: AppleMapsClient, today: date) -> bool:
    if not client.enabled or not bool(record.get("is_active", True)):
        return False
    if client.mode == "all":
        checked = parse_date(record.get("classification_checked_at"))
        return not checked or (today - checked).days >= APPLE_RECHECK_DAYS
    # Default: spend Apple calls where deterministic classification is weakest.
    confidence = float(base.get("classification_confidence") or 0.0)
    if confidence < 0.88 or base.get("primary_category") in {"Other / Needs Review", "Retail Food & Vending"}:
        checked = parse_date(record.get("classification_checked_at"))
        return not checked or (today - checked).days >= APPLE_RECHECK_DAYS
    return False


def merge_apple_classification(base: dict, apple: dict) -> dict:
    if not apple:
        return base
    result = dict(base)
    apple_primary = APPLE_POI_TO_PRIMARY.get(apple.get("poi_category"))
    base_primary = base.get("primary_category")
    base_conf = float(base.get("classification_confidence") or 0.0)

    if apple_primary:
        if base_primary == apple_primary:
            result["classification_confidence"] = round(max(base_conf, 0.96), 3)
            result["classification_source"] = "apple+rules"
            result["classification_reason"] = f"Apple Maps POI category corroborates {apple_primary}"
        elif base_conf < 0.88 or base_primary in {"Other / Needs Review", "Retail Food & Vending"}:
            result["primary_category"] = apple_primary
            result["classification_confidence"] = round(max(base_conf, 0.90), 3)
            result["classification_source"] = "apple+rules"
            result["classification_reason"] = f"Apple Maps POI category resolved low-confidence local classification"
            if apple_primary == "Restaurants" and result.get("establishment_type") in {"Unknown", "Food / Retail Permit"}:
                result["establishment_type"] = "Restaurant"
            elif apple_primary == "Coffee & Cafes":
                result["establishment_type"] = "Coffee / Cafe"
            elif apple_primary == "Bakery & Desserts":
                result["establishment_type"] = "Bakery / Dessert"
            elif apple_primary == "Hotels & Lodging":
                result["establishment_type"] = "Hotel / Lodging"
            elif apple_primary == "Pools & Aquatics":
                result["establishment_type"] = "Pool / Aquatic Facility"
        else:
            warnings = list(result.get("classification_warnings") or [])
            warnings.append(f"Apple Maps suggested {apple_primary}; high-confidence local classifier kept {base_primary}")
            result["classification_warnings"] = sorted(set(warnings))
    return result


def apply_classification_fields(record: dict, result: dict, today: date, apple: Optional[dict] = None) -> None:
    for key in (
        "primary_category", "establishment_type", "cuisine", "tags",
        "classification_confidence", "classification_source", "classification_reason",
        "classification_warnings",
    ):
        if key in result:
            record[key] = deepcopy(result.get(key))
        elif key == "classification_warnings":
            record.pop(key, None)
    record["classification_version"] = CLASSIFICATION_VERSION
    record["group"] = record.get("primary_category") or "Other / Needs Review"  # legacy client compatibility
    record["inspection_programs"] = establishment_programs(record)
    record["needs_classification_review"] = (
        record.get("primary_category") == "Other / Needs Review"
        or float(record.get("classification_confidence") or 0.0) < 0.60
    )
    if apple:
        if apple.get("place_id"):
            record["apple_place_id"] = apple.get("place_id")
        record["apple_match_confidence"] = apple.get("match_score")
        record["classification_checked_at"] = today.isoformat()


def expected_program_domain(record: dict) -> Optional[str]:
    primary = record.get("primary_category")
    if primary in {
        "Restaurants", "Fast Food & Fast Casual", "Coffee & Cafes", "Bakery & Desserts",
        "Bars & Nightlife", "Breweries & Distilleries", "Grocery & Supermarkets",
        "Convenience & Gas", "Specialty Food & Markets", "Food Trucks & Mobile",
        "Catering & Commissaries", "Concessions & Event Food", "Retail Food & Vending",
    }:
        return "food"
    if primary == "Pools & Aquatics":
        return "pool"
    if primary == "Hotels & Lodging":
        return "hotel"
    if primary == "Body Art & Personal Services":
        return "body_art"
    return None


def flag_possible_cross_permit_associations(records: List[dict]) -> int:
    """Flag, never delete, suspicious violation-domain assignments at shared addresses.

    The KY public site can expose multiple public-health permits at one address
    (restaurant + pool + spa + hotel, etc.).  If a food business suddenly has
    pool-style violation text and another same-address record is an aquatic
    permit, retain the inspection but mark it so EatLex doesn't silently present
    the source anomaly as unquestionably correct.
    """
    by_address: Dict[str, List[dict]] = {}
    for record in records:
        if not bool(record.get("is_active", True)):
            continue
        key = canonical_match_address(record.get("address"))
        if key:
            by_address.setdefault(key, []).append(record)

    flagged = 0
    for record in records:
        current = record.get("current_inspection") or {}
        observed = inspection_program_domain(current)
        expected = expected_program_domain(record)
        # clear old derived flags before recalculating
        if isinstance(current, dict):
            current.pop("data_quality_flags", None)
        record.pop("data_quality_flags", None)
        if not expected or observed in {"unknown", expected}:
            continue
        peers = [p for p in by_address.get(canonical_match_address(record.get("address")), []) if p is not record]
        matching_peers = [
            p for p in peers
            if expected_program_domain(p) == observed or current_program_domain(p) == observed
        ]
        flag = {
            "type": "possible_cross_permit_inspection_association",
            "expected_program": expected,
            "observed_violation_program": observed,
            "same_address_establishment_ids": [p.get("id") for p in matching_peers if p.get("id")],
        }
        current["data_quality_flags"] = [flag]
        record["data_quality_flags"] = [flag]
        flagged += 1
    return flagged


def apply_v17_classifications(records: List[dict], today: date) -> dict:
    overrides = load_classification_overrides()
    apple = AppleMapsClient()
    if apple.enabled:
        log(f"Apple Maps classification enrichment enabled (mode={apple.mode})")
    else:
        log("Apple Maps classification enrichment not configured; using deterministic V17 rules")

    review = []
    primary_counts: Dict[str, int] = {}
    apple_attempts = 0
    for idx, record in enumerate(records, 1):
        base = local_classification_v17(record)
        override = override_for_record(record, overrides)
        apple_result = None
        if override:
            result = apply_override(base, override)
        else:
            if apple_check_due(record, base, apple, today):
                apple_attempts += 1
                apple_result = apple.search(record)
            result = merge_apple_classification(base, apple_result) if apple_result else base

        apply_classification_fields(record, result, today, apple_result)
        primary = record.get("primary_category") or "Other / Needs Review"
        primary_counts[primary] = primary_counts.get(primary, 0) + 1

        if record.get("needs_classification_review"):
            review.append({
                "id": record.get("id"),
                "name": record.get("name"),
                "address": record.get("address"),
                "is_active": bool(record.get("is_active", True)),
                "current_score": (record.get("current_inspection") or {}).get("score"),
                "proposed_primary_category": primary,
                "proposed_establishment_type": record.get("establishment_type"),
                "confidence": record.get("classification_confidence"),
                "reason": record.get("classification_reason"),
            })

        if apple.enabled and idx % 250 == 0 and apple_attempts:
            log(f"Apple classification progress: {idx:,}/{len(records):,}; {apple.matches:,} accepted matches from {apple.calls:,} calls")

    anomalies = flag_possible_cross_permit_associations(records)
    summary = {
        "classification_version": CLASSIFICATION_VERSION,
        "generated_at": datetime.now().astimezone().isoformat(timespec="seconds"),
        "total_records": len(records),
        "active_records": sum(1 for r in records if bool(r.get("is_active", True))),
        "needs_review": len(review),
        "data_quality_anomalies": anomalies,
        "apple_enabled": apple.enabled or bool(apple.calls),
        "apple_mode": apple.mode,
        "apple_calls": apple.calls,
        "apple_matches": apple.matches,
        "apple_failures": apple.failures,
        "categories": [
            {"name": name, "count": primary_counts.get(name, 0)}
            for name in PRIMARY_CATEGORIES
            if primary_counts.get(name, 0)
        ],
    }
    review.sort(key=lambda x: (not x.get("is_active", True), normalize_key_text(x.get("name")), normalize_address_key(x.get("address"))))
    return {"summary": summary, "review": review}


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

    KYEnvPBL currently puts only ``gPersist=true`` in the score link's
    ``onclick`` attribute.  The actual ``detailRolloverPopup(...)`` call and
    its ``<ul><li>...</li></ul>`` violation markup are stored in
    ``onmouseover``.  Older versions of the page have used slightly different
    event attributes, so inspect all likely event attributes rather than
    assuming ``onclick``.

    Returns (mapped_codes, raw_texts, unmapped_texts).
    """
    link = cell.find("a")
    if not link:
        return [], [], []

    event_texts: List[str] = []
    for attr in ("onmouseover", "onclick", "onmouseenter", "onfocus", "href"):
        value = link.get(attr)
        if isinstance(value, str) and value:
            event_texts.append(html_lib.unescape(value))

    if not event_texts:
        return [], [], []

    popup_text = "\n".join(event_texts)

    # The HTML fragment can appear literally as <ul>...</ul> or HTML-escaped
    # in the JavaScript attribute.  html.unescape above handles the latter.
    match = re.search(r"(<ul\b[^>]*>.*?</ul>)", popup_text, re.I | re.S)
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


def pagination_item_count(soup: BeautifulSoup) -> Optional[int]:
    """Return the total result-row count shown by the ASP.NET pager."""
    text = normalize_space(soup.get_text(" ", strip=True))
    match = re.search(r"\b([0-9][0-9,]*)\s+Items\b", text, re.I)
    if not match:
        return None
    try:
        return int(match.group(1).replace(",", ""))
    except ValueError:
        return None


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
    max_pages: Optional[int] = None,
) -> List[dict]:
    response, soup = get_landing(session)

    # The CDP ASP.NET pager behaves inconsistently when its page-size textbox is
    # changed by postback: it can keep the old page count while returning a new
    # number of rows, which can skip/duplicate records. For the native 10-row
    # size, do not post a page-size change at all. This is slower but reliable.
    if requested_page_size != FALLBACK_PAGE_SIZE:
        try:
            response, soup = submit_postback(
                session,
                response,
                soup,
                event_target="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_PageSizeButton",
                extra={"ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_PageSize": str(requested_page_size)},
            )
        except Exception as exc:
            log(f"Could not change page size ({exc}); continuing with server default")

    pages = pagination_page_count(soup)
    total_items = pagination_item_count(soup)
    if pages > MAX_FALLBACK_PAGES:
        raise RuntimeError(f"Refusing to scrape {pages} pages; safety limit is {MAX_FALLBACK_PAGES}")

    pages_to_fetch = pages if max_pages is None else min(pages, max_pages)
    all_rows: List[dict] = []
    for page_num in range(1, pages_to_fetch + 1):
        page_rows = rows_from_html(soup)

        # Safety: when using the native 10-row pager, seeing more than 10 result
        # rows means the ASP.NET page-size state changed underneath us. Abort
        # instead of publishing duplicated/skipped violation details.
        if requested_page_size == FALLBACK_PAGE_SIZE and len(page_rows) > FALLBACK_PAGE_SIZE:
            raise RuntimeError(
                f"{log_prefix} page {page_num} returned {len(page_rows)} rows "
                f"while native page size is {FALLBACK_PAGE_SIZE}; refusing inconsistent pagination"
            )

        all_rows.extend(page_rows)
        log(f"{log_prefix} page {page_num}/{pages}: +{len(page_rows)} rows ({len(all_rows):,} total)")

        if total_items is not None and len(all_rows) > total_items:
            raise RuntimeError(
                f"{log_prefix} collected {len(all_rows):,} rows but pager reports only "
                f"{total_items:,} items; refusing duplicated pagination"
            )

        if page_num >= pages_to_fetch:
            break
        response, soup = submit_postback(
            session,
            response,
            soup,
            image_button="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_NextPage",
        )
        time.sleep(delay_seconds)

    # On a full crawl, require exact agreement with the site's own item count.
    if max_pages is None and total_items is not None and len(all_rows) != total_items:
        raise RuntimeError(
            f"{log_prefix} collected {len(all_rows):,} rows but pager reports "
            f"{total_items:,}; refusing incomplete violation enrichment"
        )

    return all_rows


def _page_signature(rows: List[dict]) -> str:
    """Hash the ordered contents of one rendered page to detect repeated pages."""
    payload = "\n".join(state_row_detail_key(row) for row in rows)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def scrape_violation_details_fast(
    expected_total: int,
    page_sizes: Tuple[int, ...] = VIOLATION_PAGE_SIZE_CANDIDATES,
    delay_seconds: float = VIOLATION_DELAY_SECONDS,
) -> List[dict]:
    """Fetch rendered violation details using the largest safe ASP.NET page size.

    The KY CDP page can return 100/1000 rows after changing Items/Page while its
    visible "of N" page count still reflects the native 10-row setting.  We
    intentionally ignore that stale page count.  For each candidate size we:

      1. start from a fresh HTTP/ASP.NET session,
      2. request the candidate Items/Page value,
      3. infer the *effective* page size from the first returned page,
      4. force First Page so the requested size is applied from row 1,
      5. calculate ceil(current_CSV_count / effective_page_size),
      6. reject repeated pages, unexpected row counts, or totals that differ
         from the current CSV export.

    If a large size is capped or behaves oddly, the next smaller candidate is
    tried automatically.  Ten rows/page is the final reliable fallback.
    """
    if expected_total <= 0:
        raise ValueError("expected_total must be greater than zero")

    failures: List[str] = []

    for requested_size in page_sizes:
        try:
            with requests.Session() as attempt_session:
                attempt_session.headers.update(HEADERS)
                response, soup = get_landing(attempt_session)

                landing_total = pagination_item_count(soup)
                if landing_total is not None and landing_total != expected_total:
                    raise RuntimeError(
                        f"live HTML reports {landing_total:,} items but this run's CSV has "
                        f"{expected_total:,}; source changed during update"
                    )

                if requested_size != FALLBACK_PAGE_SIZE:
                    response, soup = submit_postback(
                        attempt_session,
                        response,
                        soup,
                        event_target="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_PageSizeButton",
                        extra={
                            "ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_PageSize": str(requested_size)
                        },
                    )

                    # CDP keeps rendering the old 10-row page immediately after
                    # the page-size postback.  A subsequent pager action applies
                    # the new size.  Force First Page so the crawl begins at row 1
                    # with the requested size instead of skipping the first block.
                    response, soup = submit_postback(
                        attempt_session,
                        response,
                        soup,
                        image_button="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_FirstPage",
                    )

                first_rows = rows_from_html(soup)
                effective_size = len(first_rows)
                stale_pages = pagination_page_count(soup)

                if effective_size <= 0:
                    raise RuntimeError("first page contained no establishment rows")
                if effective_size > expected_total:
                    raise RuntimeError(
                        f"first page returned {effective_size:,} rows for only {expected_total:,} CSV rows"
                    )

                # The final native page can be short only when the entire data set
                # fits on one page.  Otherwise the first page reveals the server's
                # actual accepted/capped page size.
                calculated_pages = (expected_total + effective_size - 1) // effective_size
                if calculated_pages > MAX_FALLBACK_PAGES:
                    raise RuntimeError(
                        f"calculated {calculated_pages} pages; safety limit is {MAX_FALLBACK_PAGES}"
                    )

                log(
                    f"Violation detail requested {requested_size:,} items/page; server returned "
                    f"{effective_size:,} on page 1. Using {calculated_pages} calculated page(s) "
                    f"for today's {expected_total:,} CSV rows (ignoring displayed {stale_pages} pages)."
                )

                all_rows: List[dict] = []
                seen_page_signatures: set[str] = set()

                for page_num in range(1, calculated_pages + 1):
                    page_rows = first_rows if page_num == 1 else rows_from_html(soup)
                    expected_on_page = min(
                        effective_size,
                        expected_total - (page_num - 1) * effective_size,
                    )

                    if len(page_rows) != expected_on_page:
                        raise RuntimeError(
                            f"page {page_num} returned {len(page_rows):,} rows; expected "
                            f"{expected_on_page:,} based on effective page size {effective_size:,}"
                        )

                    signature = _page_signature(page_rows)
                    if signature in seen_page_signatures:
                        raise RuntimeError(
                            f"page {page_num} repeated a previously collected page; refusing duplicate crawl"
                        )
                    seen_page_signatures.add(signature)

                    all_rows.extend(page_rows)
                    log(
                        f"Violation detail page {page_num}/{calculated_pages}: "
                        f"+{len(page_rows):,} rows ({len(all_rows):,}/{expected_total:,} total)"
                    )

                    if page_num >= calculated_pages:
                        break

                    response, soup = submit_postback(
                        attempt_session,
                        response,
                        soup,
                        image_button="ctl00$PageContent$VW_PUBLIC_EST_INSPPagination$_NextPage",
                    )
                    time.sleep(delay_seconds)

                if len(all_rows) != expected_total:
                    raise RuntimeError(
                        f"collected {len(all_rows):,} HTML rows but current CSV contains "
                        f"{expected_total:,}"
                    )

                log(
                    f"Violation detail crawl succeeded with requested page size "
                    f"{requested_size:,} (effective {effective_size:,}): {len(all_rows):,} rows"
                )
                return all_rows

        except Exception as exc:
            msg = f"{requested_size:,} items/page failed: {exc}"
            failures.append(msg)
            log(f"Violation detail {msg}")
            continue

    raise RuntimeError(
        "All violation-detail page-size attempts failed: " + " | ".join(failures)
    )


def fetch_state_rows() -> List[dict]:
    with requests.Session() as session:
        session.headers.update(HEADERS)
        response, soup = get_landing(session)
        try:
            rows = try_csv_export(session, response, soup)
            log(f"Downloaded {len(rows):,} Fayette County records via CSV export")

            # CSV has the master rows/scores but NOT violation detail. The live
            # HTML score cells contain violation item titles in rollover markup.
            # V12 tries 1000 rows/page first and calculates page count from this
            # run's CSV total, falling back automatically when the server caps or
            # mishandles a larger page size.
            log("Fetching live violation details from KYEnvPBL HTML...")
            html_rows = scrape_violation_details_fast(expected_total=len(rows))

            matched, unmapped = merge_violation_enrichment(rows, html_rows)
            coverage = matched / len(rows) if rows else 0.0
            log(
                f"Violation enrichment matched {matched:,}/{len(rows):,} CSV rows "
                f"({coverage:.1%})"
            )
            if unmapped:
                preview = "; ".join(unmapped[:12])
                log(f"Warning: {len(unmapped)} unique violation title(s) were not mapped to codes: {preview}")

            # Complete inspection history is the goal.  A violation-detail row
            # that cannot be matched to today's CSV means the source changed or
            # pagination skipped/duplicated something.  Do not publish a partial
            # data set; a later daily run can try again against a consistent view.
            if REQUIRE_VIOLATION_ENRICHMENT and matched != len(rows):
                raise RuntimeError(
                    f"Violation enrichment matched only {matched:,}/{len(rows):,} rows; "
                    f"refusing to publish incomplete data"
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


def _record_preference_score(record: dict) -> Tuple[int, int, str, int]:
    """Prefer the already-published active/current record when aliases coalesce."""
    active = 1 if bool(record.get("is_active")) else 0
    state_backed = 1 if record.get("state_id") or record.get("source") == SOURCE_NAME else 0
    current = current_inspection(record.get("inspections", []) or [])
    current_date = str((current or {}).get("date") or record.get("last_seen") or "")
    history_size = len(record.get("inspections", []) or [])
    return (active, state_backed, current_date, history_size)


def coalesce_canonical_legacy_aliases(records: List[dict]) -> List[dict]:
    """Collapse only high-confidence legacy/current aliases before live matching.

    This primarily fixes old LFCHD rows whose *name* contains the same address
    already stored in the address field.  Distinct permits at one address with
    genuinely different names/scores remain separate.
    """
    buckets: Dict[str, List[dict]] = {}
    passthrough: List[dict] = []
    for record in records:
        if not isinstance(record, dict):
            continue
        name = normalize_space(record.get("name"))
        address = normalize_space(record.get("address"))
        city = normalize_space(record.get("city")) or "LEXINGTON"
        if not name or not address:
            passthrough.append(record)
            continue
        key = canonical_match_lookup_key(name, address, city)
        buckets.setdefault(key, []).append(record)

    result = list(passthrough)
    merged_aliases = 0
    for items in buckets.values():
        if len(items) == 1:
            result.append(items[0])
            continue

        # All members share exact normalized address + canonical stripped name.
        # Keep the active/current published record's stable ID when available.
        preferred = max(items, key=_record_preference_score)
        for item in items:
            if item is preferred:
                continue
            merge_establishment_record(preferred, item)
            merged_aliases += 1
        ensure_inspection_ids(preferred)
        preferred["current_inspection"] = current_inspection(preferred.get("inspections", []))
        preferred["has_new_inspection"] = any(
            bool(x.get("is_new")) for x in preferred.get("inspections", []) if isinstance(x, dict)
        )
        result.append(preferred)

    if merged_aliases:
        log(f"Coalesced {merged_aliases} canonical legacy/current establishment alias(es)")
    return result


def load_previous_records() -> Tuple[List[dict], bool, Optional[Path]]:
    paths = legacy_snapshot_paths()
    if not paths:
        return [], True, None

    data = union_legacy_snapshots(paths)
    data = coalesce_canonical_legacy_aliases(data)
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
        lookup.setdefault(canonical_match_lookup_key(name, address, city), record)
        lookup.setdefault(canonical_match_lookup_key(name, address, "LEXINGTON"), record)

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
        or lookup.get(canonical_match_lookup_key(name, address, city))
        or lookup.get(canonical_match_lookup_key(name, address, "LEXINGTON"))
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
    claimed_previous_objects = set()

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

        # A legacy record may be reachable through a broad unique-name/address
        # alias. Never clone that same historical record into two different live
        # establishments. The first live match claims its history; later groups
        # start clean and can still be coalesced later if they are truly aliases
        # of the same physical establishment.
        if prev and id(prev) in claimed_previous_objects:
            log(
                f"Legacy match already claimed; not cloning history into second live record: "
                f"{name} @ {address}"
            )
            prev = None

        if prev:
            claimed_previous_objects.add(id(prev))
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

    # Historical snapshots created before stable SwiftData IDs can contain the
    # same published ID on more than one merged record. Resolve that safely
    # before validation: true aliases merge; distinct places are re-keyed.
    records = resolve_duplicate_establishment_ids(records)
    resolve_duplicate_inspection_ids(records)

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
        grouped.setdefault(record.get("primary_category") or record.get("group") or "Other / Needs Review", []).append(record)

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


def publish_json(records: List[dict], new_inspections_added: int, today: date, classification: Optional[dict] = None) -> Tuple[bool, Optional[Path]]:
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

    classification = classification or {"summary": {}, "review": []}
    atomic_write_json(NEEDS_REVIEW_PATH, classification.get("review") or [])
    atomic_write_json(CLASSIFICATION_SUMMARY_PATH, classification.get("summary") or {})

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
        "classification_version": CLASSIFICATION_VERSION,
        "classification_needs_review": (classification.get("summary") or {}).get("needs_review", 0),
        "classification_data_quality_anomalies": (classification.get("summary") or {}).get("data_quality_anomalies", 0),
        "apple_classification_calls": (classification.get("summary") or {}).get("apple_calls", 0),
        "apple_classification_matches": (classification.get("summary") or {}).get("apple_matches", 0),
        "needs_review_file": NEEDS_REVIEW_PATH.name,
        "classification_summary_file": CLASSIFICATION_SUMMARY_PATH.name,

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
        str(NEEDS_REVIEW_PATH.relative_to(REPO_DIR)),
        str(CLASSIFICATION_SUMMARY_PATH.relative_to(REPO_DIR)),
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

    classification = apply_v17_classifications(records, today)
    log(
        f"V17 classification: {classification['summary']['needs_review']:,} need review; "
        f"{classification['summary']['data_quality_anomalies']:,} possible cross-permit inspection association(s) flagged"
    )

    changed, snapshot = publish_json(records, new_inspections_added, today, classification)
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
