#!/usr/bin/env python3
"""Scan hike assets, match media timestamps to the GPX track, write timeline JSON + thumbs."""

from __future__ import annotations

import json
import math
import os
import struct
import subprocess
import sys
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ASSETS = ROOT / "assets"
OUT_DIR = ROOT / "data"
THUMB_DIR = ROOT / "thumbs"
GPX_NS = {"g": "http://www.topografix.com/GPX/1/1"}

IMAGE_EXT = {".jpg", ".jpeg", ".png", ".heic", ".webp"}
VIDEO_EXT = {".mov", ".mp4", ".m4v"}
MEDIA_EXT = IMAGE_EXT | VIDEO_EXT


def parse_iso(text: str) -> datetime:
    return datetime.fromisoformat(text.replace("Z", "+00:00"))


def load_gpx(path: Path) -> dict:
    tree = ET.parse(path)
    root = tree.getroot()
    meta_name = root.findtext("g:metadata/g:name", default="", namespaces=GPX_NS)
    trk_name = root.findtext("g:trk/g:name", default=meta_name, namespaces=GPX_NS)
    points = []
    for pt in root.findall(".//g:trkpt", GPX_NS):
        t = pt.findtext("g:time", namespaces=GPX_NS)
        if not t:
            continue
        ele = pt.findtext("g:ele", namespaces=GPX_NS)
        points.append(
            {
                "t": parse_iso(t).timestamp(),
                "iso": parse_iso(t).isoformat().replace("+00:00", "Z"),
                "lat": float(pt.attrib["lat"]),
                "lon": float(pt.attrib["lon"]),
                "ele": float(ele) if ele else None,
            }
        )
    if not points:
        raise SystemExit(f"No timed track points in {path}")
    return {
        "name": trk_name or path.stem,
        "path": str(path.relative_to(ROOT)),
        "start": points[0]["iso"],
        "end": points[-1]["iso"],
        "startTs": points[0]["t"],
        "endTs": points[-1]["t"],
        "points": points,
    }


def read_jpeg_exif(path: Path, max_read: int = 512 * 1024) -> dict:
    with path.open("rb") as f:
        data = f.read(max_read)
    if data[:2] != b"\xff\xd8":
        return {}
    i = 2
    while i + 4 < len(data):
        if data[i] != 0xFF:
            break
        marker = data[i + 1]
        if marker == 0xDA:
            break
        seglen = struct.unpack(">H", data[i + 2 : i + 4])[0]
        if marker == 0xE1 and data[i + 4 : i + 10] == b"Exif\x00\x00":
            return parse_tiff_exif(data[i + 10 : i + 2 + seglen])
        i += 2 + seglen
    return {}


def parse_tiff_exif(buf: bytes) -> dict:
    if len(buf) < 8:
        return {}
    endian = "<" if buf[:2] == b"II" else ">"
    if buf[2:4] not in (b"\x2a\x00", b"\x00\x2a"):
        return {}
    tags: dict = {}
    walk_ifd(buf, endian, struct.unpack(endian + "I", buf[4:8])[0], tags)
    if 0x8769 in tags:
        walk_ifd(buf, endian, tags[0x8769], tags)
    if 0x8825 in tags:
        gps: dict = {}
        walk_ifd(buf, endian, tags[0x8825], gps)
        tags["gps"] = gps
    return tags


def walk_ifd(buf: bytes, endian: str, off: int, dest: dict) -> None:
    if off + 2 > len(buf):
        return
    n = struct.unpack(endian + "H", buf[off : off + 2])[0]
    sizes = {1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 7: 1, 9: 4, 10: 8}
    for k in range(min(n, 100)):
        e = off + 2 + k * 12
        if e + 12 > len(buf):
            break
        tag, typ, cnt = struct.unpack(endian + "HHI", buf[e : e + 8])
        val = buf[e + 8 : e + 12]
        sz = sizes.get(typ, 1) * cnt
        if sz > 4:
            voff = struct.unpack(endian + "I", val)[0]
            if voff + sz > len(buf):
                continue
            raw = buf[voff : voff + sz]
        else:
            raw = val[:sz]
        if typ == 2:
            dest[tag] = raw.split(b"\x00")[0].decode("ascii", "ignore")
        elif typ == 3 and cnt == 1:
            dest[tag] = struct.unpack(endian + "H", raw[:2])[0]
        elif typ == 4 and cnt == 1:
            dest[tag] = struct.unpack(endian + "I", raw[:4])[0]
        elif typ == 5:
            vals = []
            for j in range(cnt):
                a, b = struct.unpack(endian + "II", raw[j * 8 : j * 8 + 8])
                vals.append(a / b if b else 0.0)
            dest[tag] = vals if cnt > 1 else vals[0]


def gps_datetime(gps: dict) -> datetime | None:
    if not gps or 0x1D not in gps or 0x07 not in gps:
        return None
    date = gps[0x1D]
    t = gps[0x07]
    if not isinstance(t, (list, tuple)) or len(t) < 3:
        return None
    try:
        y, m, d = map(int, date.split(":"))
        h, mi, s = t[:3]
        return datetime(y, m, d, int(h), int(mi), int(s), tzinfo=timezone.utc)
    except (ValueError, TypeError):
        return None


def dms_to_deg(dms, ref: str | None) -> float | None:
    if not isinstance(dms, (list, tuple)) or len(dms) < 3:
        return None
    deg = dms[0] + dms[1] / 60.0 + dms[2] / 3600.0
    if ref in ("S", "W"):
        deg = -deg
    return deg


def gps_img_direction(gps: dict) -> float | None:
    """GPSImgDirection (0x0011), degrees from true/magnetic north."""
    if not gps or 0x11 not in gps:
        return None
    val = gps[0x11]
    if isinstance(val, (list, tuple)):
        if not val:
            return None
        val = val[0]
    try:
        deg = float(val)
    except (TypeError, ValueError):
        return None
    # Prefer True North (T); if Magnetic (M) still usable as approximate heading
    return deg % 360.0


def bearing_deg(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    φ1, φ2 = math.radians(lat1), math.radians(lat2)
    Δλ = math.radians(lon2 - lon1)
    y = math.sin(Δλ) * math.cos(φ2)
    x = math.cos(φ1) * math.sin(φ2) - math.sin(φ1) * math.cos(φ2) * math.cos(Δλ)
    return (math.degrees(math.atan2(y, x)) + 360.0) % 360.0


def track_heading_at(points: list[dict], ts: float) -> float | None:
    if not points:
        return None
    i = min(range(len(points)), key=lambda j: abs(points[j]["t"] - ts))
    a = points[max(0, i - 1)]
    b = points[min(len(points) - 1, i + 1)]
    if a["lat"] == b["lat"] and a["lon"] == b["lon"]:
        return None
    return bearing_deg(a["lat"], a["lon"], b["lat"], b["lon"])


def parse_dto(text: str | None, offset: str | None) -> datetime | None:
    if not text:
        return None
    try:
        naive = datetime.strptime(text, "%Y:%m:%d %H:%M:%S")
    except ValueError:
        return None
    if not offset or len(offset) < 6:
        offset = "+00:00"
    sign = 1 if offset[0] == "+" else -1
    hh, mm = map(int, offset[1:].split(":"))
    tz = timezone(sign * timedelta(hours=hh, minutes=mm))
    return naive.replace(tzinfo=tz).astimezone(timezone.utc)


def sips_creation(path: Path) -> datetime | None:
    try:
        out = subprocess.check_output(
            ["sips", "-g", "creation", str(path)],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None
    for line in out.splitlines():
        if "creation:" in line:
            raw = line.split("creation:", 1)[1].strip()
            if not raw or raw == "null":
                return None
            try:
                # Treat as local wall time in CEST for this trip when no offset.
                return parse_dto(raw, "+02:00")
            except Exception:
                return None
    return None


def qt_creation(path: Path) -> datetime | None:
    try:
        with path.open("rb") as f:
            data = f.read()
    except OSError:
        return None
    idx = data.find(b"mvhd")
    if idx < 0:
        return None
    ver = data[idx + 4]
    try:
        if ver == 0:
            cts = struct.unpack(">I", data[idx + 8 : idx + 12])[0]
        elif ver == 1:
            cts = struct.unpack(">Q", data[idx + 12 : idx + 20])[0]
        else:
            return None
    except struct.error:
        return None
    epoch = datetime(1904, 1, 1, tzinfo=timezone.utc)
    return epoch + timedelta(seconds=cts)


def mp4_name_time(name: str) -> datetime | None:
    # back_2026-10-02T05-58-57Z.MP4
    if "T" not in name or not name.endswith("Z"):
        return None
    stem = Path(name).stem
    parts = stem.split("_")
    for part in reversed(parts):
        if part.endswith("Z") and "T" in part:
            try:
                return datetime.strptime(part, "%Y-%m-%dT%H-%M-%SZ").replace(
                    tzinfo=timezone.utc
                )
            except ValueError:
                continue
    return None


def calibrate_ricoh_delta(dto_list: list[datetime], gpx_start: float, gpx_end: float) -> int:
    """Return minutes to add to Ricoh DateTimeOriginal-as-UTC to land on true UTC."""
    best = (0, 0)
    for minutes in range(-14 * 60, 14 * 60 + 1, 5):
        delta = timedelta(minutes=minutes)
        count = 0
        for d in dto_list:
            ts = (d.replace(tzinfo=timezone.utc) + delta).timestamp()
            if gpx_start <= ts <= gpx_end:
                count += 1
        if count > best[0]:
            best = (count, minutes)
    return best[1]


def nearest_point(points: list[dict], ts: float) -> dict:
    lo, hi = 0, len(points) - 1
    if ts <= points[0]["t"]:
        return points[0]
    if ts >= points[-1]["t"]:
        return points[-1]
    while lo < hi:
        mid = (lo + hi) // 2
        if points[mid]["t"] < ts:
            lo = mid + 1
        else:
            hi = mid
    cand = [points[max(0, lo - 1)], points[lo]]
    return min(cand, key=lambda p: abs(p["t"] - ts))


def ensure_thumb(src: Path, dest: Path, width: int = 480) -> bool:
    if dest.exists() and dest.stat().st_mtime >= src.stat().st_mtime:
        return True
    dest.parent.mkdir(parents=True, exist_ok=True)
    ext = src.suffix.lower()
    # Convert HEIC/PNG/JPEG via sips; for video, grab a poster frame with sips if possible.
    try:
        if ext in VIDEO_EXT:
            # sips cannot read MOV reliably; skip poster — UI will show a video badge.
            return False
        subprocess.check_call(
            [
                "sips",
                "-Z",
                str(width),
                str(src),
                "--out",
                str(dest.with_suffix(".jpg")),
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if dest.suffix.lower() != ".jpg":
            # sips may write exact out path; normalize to .jpg
            written = dest.with_suffix(".jpg")
            if written.exists() and written != dest:
                written.replace(dest)
        return dest.exists() or dest.with_suffix(".jpg").exists()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def collect_media() -> list[Path]:
    files = []
    for path in ASSETS.rglob("*"):
        if not path.is_file():
            continue
        if path.name.startswith("."):
            continue
        if path.suffix.lower() in MEDIA_EXT:
            files.append(path)
    return sorted(files)


def main() -> None:
    gpx_files = list(ASSETS.rglob("*.gpx"))
    if not gpx_files:
        raise SystemExit("No GPX file found under assets/")
    gpx_path = gpx_files[0]
    gpx = load_gpx(gpx_path)

    media_paths = collect_media()
    print(f"GPX: {gpx['name']} ({len(gpx['points'])} points)", file=sys.stderr)
    print(f"Media files: {len(media_paths)}", file=sys.stderr)

    # First pass: Ricoh DateTimeOriginal values for clock calibration
    ricoh_dtos: list[datetime] = []
    for path in media_paths:
        if "ricoh" not in path.parts:
            continue
        if path.suffix.lower() not in {".jpg", ".jpeg"}:
            continue
        tags = read_jpeg_exif(path)
        dto = tags.get(0x9003) or tags.get(0x0132)
        if isinstance(dto, str):
            try:
                ricoh_dtos.append(datetime.strptime(dto, "%Y:%m:%d %H:%M:%S"))
            except ValueError:
                pass
    ricoh_delta_min = calibrate_ricoh_delta(ricoh_dtos, gpx["startTs"], gpx["endTs"])
    print(
        f"Ricoh clock calibration: {ricoh_delta_min} minutes "
        f"({sum(1 for d in ricoh_dtos if gpx['startTs'] <= (d.replace(tzinfo=timezone.utc)+timedelta(minutes=ricoh_delta_min)).timestamp() <= gpx['endTs'])} in GPX window)",
        file=sys.stderr,
    )

    THUMB_DIR.mkdir(parents=True, exist_ok=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    items = []
    matched = 0
    for i, path in enumerate(media_paths):
        rel = path.relative_to(ROOT).as_posix()
        source = "ricoh" if "ricoh" in path.parts else "iphone" if "iphone" in path.parts else "other"
        ext = path.suffix.lower()
        kind = "video" if ext in VIDEO_EXT else "image"
        ts: datetime | None = None
        ts_source = None
        lat = lon = None
        heading = None
        heading_source = None
        orientation = None

        if ext in {".jpg", ".jpeg"}:
            tags = read_jpeg_exif(path)
            gps = tags.get("gps") or {}
            orientation = tags.get(0x0112)  # Orientation
            heading = gps_img_direction(gps)
            if heading is not None:
                heading_source = "exif"
            gdt = gps_datetime(gps)
            if gdt:
                ts, ts_source = gdt, "gps"
                lat = dms_to_deg(gps.get(0x02), gps.get(0x01))
                lon = dms_to_deg(gps.get(0x04), gps.get(0x03))
            else:
                dto = tags.get(0x9003) or tags.get(0x0132)
                if source == "ricoh" and isinstance(dto, str):
                    try:
                        naive = datetime.strptime(dto, "%Y:%m:%d %H:%M:%S")
                        ts = naive.replace(tzinfo=timezone.utc) + timedelta(
                            minutes=ricoh_delta_min
                        )
                        ts_source = f"exif+calibrated({ricoh_delta_min}m)"
                    except ValueError:
                        pass
                else:
                    offset = tags.get(0x9010) or "+02:00"
                    ts = parse_dto(dto if isinstance(dto, str) else None, offset)
                    ts_source = "exif+offset" if ts else None
        elif ext in VIDEO_EXT:
            ts = mp4_name_time(path.name) or qt_creation(path)
            ts_source = "filename" if ts and mp4_name_time(path.name) else "mvhd" if ts else None
        elif ext in {".heic", ".png", ".webp"}:
            ts = sips_creation(path)
            ts_source = "sips" if ts else None

        if not ts:
            # last resort: file mtime
            ts = datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc)
            ts_source = "mtime"

        ts_utc = ts.astimezone(timezone.utc)
        ts_val = ts_utc.timestamp()
        on_track = gpx["startTs"] <= ts_val <= gpx["endTs"]
        point = nearest_point(gpx["points"], ts_val) if on_track else None
        if on_track:
            matched += 1

        if heading is None and on_track:
            heading = track_heading_at(gpx["points"], ts_val)
            if heading is not None:
                heading_source = "track"

        thumb_rel = None
        if kind == "image":
            thumb_name = f"{source}_{path.stem}.jpg".replace(" ", "_")
            thumb_path = THUMB_DIR / thumb_name
            if ensure_thumb(path, thumb_path):
                # normalize extension
                if not thumb_path.exists() and thumb_path.with_suffix(".jpg").exists():
                    thumb_path = thumb_path.with_suffix(".jpg")
                if thumb_path.exists():
                    thumb_rel = thumb_path.relative_to(ROOT).as_posix()

        items.append(
            {
                "id": f"{source}-{path.name}",
                "name": path.name,
                "path": rel,
                "thumb": thumb_rel,
                "source": source,
                "kind": kind,
                "time": ts_utc.isoformat().replace("+00:00", "Z"),
                "ts": ts_val,
                "timeSource": ts_source,
                "onTrack": on_track,
                "lat": lat if lat is not None else (point["lat"] if point else None),
                "lon": lon if lon is not None else (point["lon"] if point else None),
                "ele": point["ele"] if point else None,
                "trackDeltaSec": (ts_val - point["t"]) if point else None,
                "heading": round(heading, 3) if heading is not None else None,
                "headingSource": heading_source,
                "orientation": orientation,
            }
        )
        if (i + 1) % 100 == 0:
            print(f"  processed {i + 1}/{len(media_paths)}", file=sys.stderr)

    items.sort(key=lambda x: x["ts"])

    # Downsample track for the UI (keep denser near elevation changes)
    track = gpx["points"]
    slim = []
    for idx, p in enumerate(track):
        if idx == 0 or idx == len(track) - 1 or idx % 3 == 0:
            slim.append(
                {
                    "t": p["t"],
                    "iso": p["iso"],
                    "lat": p["lat"],
                    "lon": p["lon"],
                    "ele": p["ele"],
                }
            )

    manifest = {
        "generatedAt": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "gpx": {
            "name": gpx["name"],
            "path": gpx["path"],
            "start": gpx["start"],
            "end": gpx["end"],
            "startTs": gpx["startTs"],
            "endTs": gpx["endTs"],
            "pointCount": len(gpx["points"]),
            "track": slim,
        },
        "calibration": {"ricohDeltaMinutes": ricoh_delta_min},
        "stats": {
            "media": len(items),
            "onTrack": matched,
            "offTrack": len(items) - matched,
            "bySource": {
                "iphone": sum(1 for x in items if x["source"] == "iphone"),
                "ricoh": sum(1 for x in items if x["source"] == "ricoh"),
                "other": sum(1 for x in items if x["source"] == "other"),
            },
        },
        "media": items,
    }

    out_path = OUT_DIR / "timeline.json"
    out_path.write_text(json.dumps(manifest, separators=(",", ":")))
    print(
        f"Wrote {out_path.relative_to(ROOT)} — {matched}/{len(items)} on GPX timeline",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
