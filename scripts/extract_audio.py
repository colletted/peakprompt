#!/usr/bin/env python3
"""Extract a spaced sample of video audio clips into audio/ and merge into the timeline manifest."""

from __future__ import annotations

import json
import struct
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data" / "timeline.json"
AUDIO_DIR = ROOT / "audio"


def qt_duration(path: Path) -> float | None:
    data = path.read_bytes()
    idx = data.find(b"mvhd")
    if idx < 0:
        return None
    ver = data[idx + 4]
    if ver == 0:
        timescale = struct.unpack(">I", data[idx + 16 : idx + 20])[0]
        duration = struct.unpack(">I", data[idx + 20 : idx + 24])[0]
    else:
        timescale = struct.unpack(">I", data[idx + 24 : idx + 28])[0]
        duration = struct.unpack(">Q", data[idx + 28 : idx + 36])[0]
    if not timescale:
        return None
    return duration / timescale


def pick_spaced(items: list[dict], n: int) -> list[dict]:
    if not items:
        return []
    if len(items) <= n:
        return items
    start, end = items[0]["ts"], items[-1]["ts"]
    buckets: list[list[dict]] = [[] for _ in range(n)]
    for it in items:
        i = min(n - 1, int((it["ts"] - start) / max(end - start, 1) * n))
        buckets[i].append(it)
    out = []
    for bucket in buckets:
        if bucket:
            out.append(max(bucket, key=lambda x: x.get("duration") or 0))
    return out


def afinfo_duration(path: Path) -> float | None:
    try:
        out = subprocess.check_output(["afinfo", str(path)], text=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None
    for line in out.splitlines():
        if "estimated duration:" in line:
            return float(line.split(":")[1].split()[0])
    return None


def main() -> None:
    if not MANIFEST.exists():
        raise SystemExit("Missing data/timeline.json — run scripts/build_manifest.py first")

    manifest = json.loads(MANIFEST.read_text())
    vids = [m for m in manifest["media"] if m.get("kind") == "video"]
    candidates = []
    for v in vids:
        if not v["name"].startswith("IMG_"):
            continue
        dur = qt_duration(ROOT / v["path"])
        if dur is None or dur < 1.5:
            continue
        candidates.append({**v, "duration": dur})
    candidates.sort(key=lambda x: x["ts"])

    on = [c for c in candidates if c.get("onTrack")]
    off = [c for c in candidates if not c.get("onTrack")]
    picks = pick_spaced(on, 8) + pick_spaced(off, 3)
    # Prefer a few extra mid-hike clips when present
    by_name = {c["name"]: c for c in candidates}
    for name in ("IMG_3815.MOV", "IMG_3818.MOV", "IMG_3975.MOV", "IMG_4001.MOV"):
        if name in by_name:
            picks.append(by_name[name])

    seen = set()
    uniq = []
    for p in sorted(picks, key=lambda x: x["ts"]):
        if p["path"] in seen:
            continue
        seen.add(p["path"])
        uniq.append(p)

    AUDIO_DIR.mkdir(exist_ok=True)
    audio_items = []
    for p in uniq:
        stem = Path(p["name"]).stem
        out = AUDIO_DIR / f"{stem}.m4a"
        print(f"Extracting {p['name']} → {out.relative_to(ROOT)}", file=sys.stderr)
        subprocess.run(
            [
                "avconvert",
                "--source",
                str(ROOT / p["path"]),
                "--preset",
                "PresetAppleM4A",
                "--output",
                str(out.resolve()),
                "--replace",
            ],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if not out.exists():
            print(f"  failed: {p['name']}", file=sys.stderr)
            continue
        audio_items.append(
            {
                "id": f"audio-{stem}",
                "name": out.name,
                "path": out.relative_to(ROOT).as_posix(),
                "thumb": None,
                "source": p.get("source", "iphone"),
                "kind": "audio",
                "time": p["time"],
                "ts": p["ts"],
                "timeSource": "from-video",
                "onTrack": p.get("onTrack", False),
                "lat": p.get("lat"),
                "lon": p.get("lon"),
                "ele": p.get("ele"),
                "trackDeltaSec": p.get("trackDeltaSec"),
                "duration": afinfo_duration(out),
                "fromVideo": p["path"],
            }
        )

    manifest["media"] = [m for m in manifest["media"] if m.get("kind") != "audio"]
    manifest["media"].extend(audio_items)
    manifest["media"].sort(key=lambda x: x["ts"])
    manifest["stats"]["media"] = len(manifest["media"])
    manifest["stats"]["audio"] = len(audio_items)
    manifest["stats"]["onTrack"] = sum(1 for m in manifest["media"] if m.get("onTrack"))
    manifest["stats"]["offTrack"] = sum(1 for m in manifest["media"] if not m.get("onTrack"))
    MANIFEST.write_text(json.dumps(manifest, separators=(",", ":")))
    print(f"Added {len(audio_items)} audio clips to timeline", file=sys.stderr)


if __name__ == "__main__":
    main()
