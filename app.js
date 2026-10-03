import * as THREE from "three";

const els = {
  experience: document.querySelector(".experience"),
  viewport: document.getElementById("viewport"),
  scrollRail: document.getElementById("scroll-rail"),
  scrollHint: document.getElementById("scroll-hint"),
  journeyLyrics: document.getElementById("journey-lyrics"),
  modeToggle: document.getElementById("mode-toggle"),
  metaTime: document.getElementById("meta-time"),
  metaAltitude: document.getElementById("meta-altitude"),
  metaLocation: document.getElementById("meta-location"),
  metaSteps: document.getElementById("meta-steps"),
  pageTitle: document.getElementById("page-title"),
};

const fmtMetaTime = new Intl.DateTimeFormat(undefined, {
  hour: "2-digit",
  minute: "2-digit",
  second: "2-digit",
  hour12: false,
});

const BRAND_WEIGHTS = [300, 400, 500]; // light → regular → medium (no bold/heavy)
const TITLE_FALLBACK = "grateful chasing summits";

const VERTICAL_EXAGGERATION = 1.8;
const MEDIA_SAMPLE = 72;
const OFF_TRACK_SAMPLE = 18; // each side: before start / after end
const TIME_WINDOW = 0.07;
const AUDIO_TIME_SIGMA = 100; // seconds — images near a recording
const AUDIO_SCROLL_SIGMA = 0.04;
const TIMELINE_CARD_GAP = 22;
const TIMELINE_RECED = 11;
const TIMELINE_YAW = 0.48;
const STEP_STRIDE_M = 0.75; // estimated hiking stride
const TUNNEL_IMAGE_CAP = 40;
const TUNNEL_GAP = 14;
const TUNNEL_WORLD_SIZE = 20; // fixed world height for cavern planes
const TUNNEL_ROLE_ORDER = ["background", "mid", "foreground"];
const TUNNEL_ROLE_SCALE = {
  background: 1.16,
  mid: 1,
  foreground: 0.88,
};

let data = null;
let renderer, scene, camera;
let interactives = [];
/** Front-camera portraits for SELFIES (timeline rolodex) mode. */
let selfieInteractives = [];
let audioClips = [];
let trackCurve = null;
let trackMesh = null;
let trackPoints = [];
let journeyColors = []; // [{ t, r, g, b }] along hike time 0..1
let frameId = 0;
let scrollProgress = 0;
let smoothProgress = 0;
let smoothCloseness = 0.35;
let closenessExtent = { min: 0, max: 1 };
let smoothJourneyColor = { r: 200, g: 200, b: 200 };
let hintHidden = false;
let metaLabelsVisible = true;
let audioCtx = null;
let audioUnlocked = false;
let lastTitleKey = "";
let titleText = TITLE_FALLBACK;
let captionsById = {};
let lyricLines = [];
let lastLyricKey = "";
let smoothLyricProgress = 0;
let lyricBubbleIndex = -1;
let lyricBubbleEl = null;
const VIEW_MODES = ["elevation", "timeline", "tunnel"];
let viewMode = "elevation";
let timelineFocus = 0;
let timelineFocusSmooth = 0;
let timelinePointerX = 0.5; // 0..1 across viewport
let savedScrollY = 0;
let tunnelGroup = null;
let tunnelPlanes = [];
let tunnelProgress = 0;
let smoothTunnelProgress = 0;
let introActive = true;
let overviewCenter = new THREE.Vector3();
let overviewRadius = 400;
let selfieGroup = null;
let selfieItems = [];
let selfieFocus = 0;
let selfieFocusSmooth = 0;
let selfieDrag = {
  active: false,
  x: 0,
  y: 0,
  yaw: 0,
  pitch: 0,
  yawT: 0,
  pitchT: 0,
};
/** Press-and-hold: dark inspect with the original photo centered. */
let inspectHold = {
  active: false,
  group: null,
  pointerId: null,
  token: 0,
};
const inspectRaycaster = new THREE.Raycaster();
const inspectPointer = new THREE.Vector2();

const thresholdResponse = 0.8;
const layerResponse = 0.8;
let altitudeTemplate = null;
let eleMin = 2100;
let eleMax = 2700;
let trackDistances = []; // cumulative path metres at each GPX index

const imageCache = new Map();
const matchCache = new Map();

const _side = new THREE.Vector3();
const _up = new THREE.Vector3(0, 1, 0);
const _camPos = new THREE.Vector3();
const _look = new THREE.Vector3();
const _tmp = new THREE.Vector3();

function clamp(v, lo, hi) {
  return Math.min(hi, Math.max(lo, v));
}

function lerp(a, b, t) {
  return a + (b - a) * t;
}

function paramsFromAltitude(ele) {
  const t =
    ele == null || eleMax <= eleMin
      ? 0.5
      : clamp((ele - eleMin) / (eleMax - eleMin), 0, 1);
  const threshold = Math.round(
    clamp(100 + (t - 0.5) * 2 * 75 * thresholdResponse, 24, 200)
  );
  const layers = Math.round(
    clamp(4 + (t - 0.5) * 2 * 2 * layerResponse, 2, 6)
  );
  return { threshold, layers, altitudeT: t };
}

function toLocalFrame(track) {
  const lat0 = track.reduce((s, p) => s + p.lat, 0) / track.length;
  const lon0 = track.reduce((s, p) => s + p.lon, 0) / track.length;
  const ele0 = Math.min(...track.map((p) => p.ele));
  const mPerDegLat = 111_320;
  const mPerDegLon = 111_320 * Math.cos((lat0 * Math.PI) / 180);

  const project = (lat, lon, ele) => {
    const x = (lon - lon0) * mPerDegLon;
    const z = -((lat - lat0) * mPerDegLat);
    const y = ((ele ?? ele0) - ele0) * VERTICAL_EXAGGERATION;
    return new THREE.Vector3(x, y, z);
  };

  return { project };
}

function nearestPoint(track, ts) {
  let best = track[0];
  let bestD = Infinity;
  for (const p of track) {
    const d = Math.abs(p.t - ts);
    if (d < bestD) {
      best = p;
      bestD = d;
    }
  }
  return best;
}

function bearingDeg(lat1, lon1, lat2, lon2) {
  const φ1 = (lat1 * Math.PI) / 180;
  const φ2 = (lat2 * Math.PI) / 180;
  const Δλ = ((lon2 - lon1) * Math.PI) / 180;
  const y = Math.sin(Δλ) * Math.cos(φ2);
  const x =
    Math.cos(φ1) * Math.sin(φ2) - Math.sin(φ1) * Math.cos(φ2) * Math.cos(Δλ);
  return ((Math.atan2(y, x) * 180) / Math.PI + 360) % 360;
}

function trackHeadingAt(ts) {
  const track = data?.gpx?.track;
  if (!track?.length) return 0;
  let i = 0;
  for (let j = 1; j < track.length; j++) {
    if (Math.abs(track[j].t - ts) < Math.abs(track[i].t - ts)) i = j;
  }
  const a = track[Math.max(0, i - 1)];
  const b = track[Math.min(track.length - 1, i + 1)];
  if (a.lat === b.lat && a.lon === b.lon) return 0;
  return bearingDeg(a.lat, a.lon, b.lat, b.lon);
}

function headingForItem(item) {
  if (item?.heading != null && Number.isFinite(item.heading)) return item.heading;
  if (item?.ts != null) return trackHeadingAt(item.ts);
  return 0;
}

function applyCaptureFacing(facing, headingDeg) {
  const θ = THREE.MathUtils.degToRad(headingDeg);
  facing.rotation.set(0, Math.atan2(Math.sin(θ), -Math.cos(θ)), 0);
}

function timeNorm(item) {
  const start = data.gpx.startTs;
  const end = data.gpx.endTs;
  if (end <= start) return 0;
  return clamp((item.ts - start) / (end - start), 0, 1);
}

function timeNormTs(ts) {
  const start = data.gpx.startTs;
  const end = data.gpx.endTs;
  if (end <= start) return 0;
  return clamp((ts - start) / (end - start), 0, 1);
}

function ensureAudioCtx() {
  if (!audioCtx) {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return null;
    audioCtx = new AC();
  }
  if (audioCtx.state === "suspended") audioCtx.resume().catch(() => {});
  audioUnlocked = true;
  return audioCtx;
}

function buildEnvelope(channelData, bins = 160) {
  const out = new Float32Array(bins);
  const chunk = Math.max(1, Math.floor(channelData.length / bins));
  let peak = 0;
  for (let i = 0; i < bins; i++) {
    let sum = 0;
    const start = i * chunk;
    const end = Math.min(channelData.length, start + chunk);
    for (let j = start; j < end; j++) sum += channelData[j] * channelData[j];
    const rms = Math.sqrt(sum / Math.max(1, end - start));
    out[i] = rms;
    if (rms > peak) peak = rms;
  }
  if (peak > 1e-8) {
    for (let i = 0; i < bins; i++) out[i] /= peak;
  }
  return out;
}

function sampleEnvelope(env, t) {
  if (!env?.length) return 0;
  const x = clamp(t, 0, 1) * (env.length - 1);
  const i = Math.floor(x);
  const f = x - i;
  const a = env[i];
  const b = env[Math.min(env.length - 1, i + 1)];
  return a * (1 - f) + b * f;
}

async function loadSoundClips(media) {
  const items = media.filter((m) => m.kind === "audio" && m.onTrack && m.path);
  const ctx = ensureAudioCtx();
  const loaded = await Promise.all(
    items.map(async (item) => {
      try {
        const res = await fetch(item.path);
        if (!res.ok) return null;
        const ab = await res.arrayBuffer();
        let envelope = null;
        if (ctx) {
          const buffer = await ctx.decodeAudioData(ab.slice(0));
          envelope = buildEnvelope(buffer.getChannelData(0));
        }
        const dur = item.duration || 4;
        const el = new Audio(item.path);
        el.preload = "auto";
        el.loop = true;
        el.volume = 0;
        return {
          item,
          ts: item.ts,
          duration: dur,
          timeT: timeNormTs(item.ts),
          endT: timeNormTs(item.ts + dur),
          envelope: envelope || new Float32Array([0.3, 0.6, 0.4, 0.7, 0.35]),
          el,
        };
      } catch (err) {
        console.warn("audio skip", item.path, err);
        return null;
      }
    })
  );
  audioClips = loaded.filter(Boolean);
}

function soundEnergyForMarker(marker, progress, clockSec) {
  if (!audioClips.length) return 0;
  const ts = marker.userData.item?.ts;
  if (ts == null) return 0;
  let best = 0;
  for (const clip of audioClips) {
    const dt = ts - clip.ts;
    const timeProx = Math.exp(
      -(dt * dt) / (2 * AUDIO_TIME_SIGMA * AUDIO_TIME_SIGMA)
    );
    if (timeProx < 0.05) continue;

    const mid = (clip.timeT + clip.endT) * 0.5;
    const span = Math.max(clip.endT - clip.timeT, 0.006);
    const scrollProx = Math.exp(
      -((progress - mid) * (progress - mid)) /
        (2 * (span * 0.85 + AUDIO_SCROLL_SIGMA) * (span * 0.85 + AUDIO_SCROLL_SIGMA))
    );
    if (scrollProx < 0.04) continue;

    let phase;
    if (progress >= clip.timeT && progress <= clip.endT) {
      phase = (progress - clip.timeT) / span;
    } else if (clip.el && !clip.el.paused && clip.el.duration > 0) {
      phase = clip.el.currentTime / clip.el.duration;
    } else {
      phase = (clockSec * 0.45 + clip.timeT * 12) % 1;
    }
    const amp = sampleEnvelope(clip.envelope, phase);
    // Keep a soft floor so quiet moments still breathe
    const energy = (0.18 + amp * 0.82) * timeProx * scrollProx;
    if (energy > best) best = energy;
  }
  return clamp(best, 0, 1);
}

function applySoundMotion(group, energy, clockSec) {
  const facing = group.userData.facing;
  if (!facing) return;
  applyCaptureFacing(facing, headingForItem(group.userData.item));
  if (energy < 0.02) {
    facing.position.x = 0;
    facing.position.y = 0;
    facing.rotation.z = 0;
    facing.scale.setScalar(1);
    for (const p of group.userData.planes || []) {
      if (p.userData.baseZ != null) p.position.z = p.userData.baseZ;
    }
    return;
  }
  const seed = (group.userData.timeT || 0) * 40;
  const t = clockSec;
  const e = energy;
  facing.position.x = Math.sin(t * 5.4 + seed) * e * 3.6;
  facing.position.y = Math.cos(t * 4.2 + seed * 0.7) * e * 2.4;
  facing.rotation.z = Math.sin(t * 6.5 + seed) * e * 0.07;
  facing.scale.setScalar(1 + e * 0.1 * (0.55 + 0.45 * Math.sin(t * 7.5)));
  const planes = group.userData.planes || [];
  planes.forEach((p, i) => {
    const baseZ = p.userData.baseZ ?? p.position.z;
    p.position.z = baseZ + Math.sin(t * 4.8 + i * 0.85 + seed) * e * 2.1;
  });
}

function syncSoundPlayback(progress) {
  if (!audioClips.length) return;
  for (const clip of audioClips) {
    const el = clip.el;
    if (!el) continue;
    const mid = (clip.timeT + clip.endT) * 0.5;
    const span = Math.max(clip.endT - clip.timeT, 0.006);
    const prox = Math.exp(
      -((progress - mid) * (progress - mid)) /
        (2 * (span + 0.025) * (span + 0.025))
    );
    if (prox > 0.22 && audioUnlocked) {
      el.volume = 0.42 * clamp(prox, 0, 1);
      if (el.paused) el.play().catch(() => {});
    } else if (!el.paused) {
      el.pause();
    }
  }
}

function spacePick(arr, n) {
  if (!arr.length || n <= 0) return [];
  const count = Math.min(n, arr.length);
  const out = [];
  for (let i = 0; i < count; i++) {
    const idx = Math.round((i / Math.max(count - 1, 1)) * (arr.length - 1));
    out.push(arr[idx]);
  }
  return out;
}

const SELFIE_MAX = 36;

function isFrontCameraItem(item) {
  const s = `${item?.id || ""} ${item?.name || ""} ${item?.path || ""}`.toLowerCase();
  return s.includes("front_");
}

function isUuidPortraitName(name = "") {
  return /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\.(jpe?g|heic|png)$/i.test(
    name
  );
}

/** Named selfie / portrait exports (combined_ dual-cam thumbs are often undecodable). */
function isSelfieItem(item) {
  const name = item?.name || "";
  if (isFrontCameraItem(item)) return true;
  if (isUuidPortraitName(name)) return true;
  return false;
}

function withTrackCoords(item, gpx) {
  const pt = nearestPoint(gpx.track, item.ts);
  return {
    ...item,
    lat: item.lat ?? pt.lat,
    lon: item.lon ?? pt.lon,
    ele: item.ele ?? pt.ele,
  };
}

/** Rough skin + fill check for a clear human figure in frame. */
function estimateHumanPresence(pixels, w, h) {
  let skin = 0;
  let centerSkin = 0;
  let center = 0;
  let fill = 0;
  const total = w * h;
  for (let y = 0, i = 0; y < h; y++) {
    for (let x = 0; x < w; x++, i += 4) {
      const r = pixels[i];
      const g = pixels[i + 1];
      const b = pixels[i + 2];
      const a = pixels[i + 3];
      if (a < 160) continue;
      const nx = (x / w - 0.5) / 0.35;
      const ny = (y / h - 0.5) / 0.45;
      const inCenter = nx * nx + ny * ny < 1;
      if (inCenter) center++;
      const mean = (r + g + b) / 3;
      if (mean > 18 && mean < 245) fill++;
      const chroma = Math.max(r, g, b) - Math.min(r, g, b);
      const skinTone =
        r >= 60 &&
        g >= 30 &&
        b >= 15 &&
        r >= g &&
        r >= b &&
        chroma >= 15 &&
        r - g > 10 &&
        r - b > 15;
      if (skinTone) {
        skin++;
        if (inCenter) centerSkin++;
      }
    }
  }
  const skinFrac = total ? skin / total : 0;
  const centerSkinFrac = center ? centerSkin / center : 0;
  const fillFrac = total ? fill / total : 0;
  const score = centerSkinFrac * 0.62 + skinFrac * 0.28 + fillFrac * 0.1;
  return { skinFrac, centerSkinFrac, fillFrac, score };
}

function hasClearHumanSilhouette(gray) {
  const human = gray?.human;
  if (!human) return false;
  if (human.fillFrac < 0.45) return false;
  // Need a readable figure — centre skin is the strongest cue we have client-side
  return human.centerSkinFrac >= 0.08 && human.skinFrac >= 0.035;
}

/** Named selfie candidates first, then fill with portrait frames that have a clear human. */
async function resolveSelfieMedia(media, gpx) {
  const named = media
    .filter(
      (m) =>
        isSelfieItem(m) &&
        m.thumb &&
        (m.kind === "image" || m.kind === "video")
    )
    .sort((a, b) => (a.ts || 0) - (b.ts || 0))
    .map((m) => withTrackCoords(m, gpx));

  const picked = [];
  const seen = new Set();

  const tryAdd = async (item, { requirePortrait = true } = {}) => {
    if (!item?.thumb || !item.path || seen.has(item.path)) return;
    if (picked.length >= SELFIE_MAX) return;
    try {
      const gray = await getGrayBuffer(item.thumb);
      if (!hasClearHumanSilhouette(gray)) return;
      const portrait = gray.height >= gray.width * 0.92;
      if (requirePortrait && !isFrontCameraItem(item) && !portrait) return;
      seen.add(item.path);
      picked.push(item);
    } catch {
      // undecodable / empty thumb — skip so the rolodex stays dense
    }
  };

  for (const item of named) {
    await tryAdd(item, { requirePortrait: false });
  }

  if (picked.length < SELFIE_MAX) {
    const extras = media
      .filter(
        (m) =>
          m.kind === "image" &&
          m.thumb &&
          m.source === "iphone" &&
          !m.onTrack &&
          !isSelfieItem(m) &&
          !seen.has(m.path)
      )
      .sort((a, b) => (a.ts || 0) - (b.ts || 0));

    for (const raw of spacePick(extras, 64)) {
      if (picked.length >= SELFIE_MAX) break;
      await tryAdd(withTrackCoords(raw, gpx), { requirePortrait: true });
    }
  }

  return picked.sort((a, b) => (a.ts || 0) - (b.ts || 0));
}

function timelineCards() {
  return selfieInteractives;
}

function sampleMedia(media, gpx) {
  // Keep selfie / portrait set out of THE HIKE
  const hikeMedia = media.filter((m) => !isSelfieItem(m));
  const onTrack = hikeMedia.filter(
    (m) => m.onTrack && (m.kind === "image" || m.kind === "video") && m.thumb
  );
  const offTrack = hikeMedia.filter(
    (m) => !m.onTrack && (m.kind === "image" || m.kind === "video") && m.thumb
  );
  const before = offTrack
    .filter((m) => m.ts < gpx.startTs)
    .sort((a, b) => a.ts - b.ts);
  const after = offTrack
    .filter((m) => m.ts > gpx.endTs)
    .sort((a, b) => a.ts - b.ts);

  const picks = [
    ...spacePick(onTrack, MEDIA_SAMPLE),
    ...spacePick(before, OFF_TRACK_SAMPLE).map((m, i, arr) => ({
      ...m,
      beyond: "before",
      floatT: arr.length <= 1 ? 0.5 : i / (arr.length - 1),
      ele: m.ele ?? gpx.track[0]?.ele,
    })),
    ...spacePick(after, OFF_TRACK_SAMPLE).map((m, i, arr) => ({
      ...m,
      beyond: "after",
      floatT: arr.length <= 1 ? 0.5 : i / (arr.length - 1),
      ele: m.ele ?? gpx.track[gpx.track.length - 1]?.ele,
    })),
  ];

  const seen = new Set();
  const unique = [];
  for (const m of picks) {
    if (seen.has(m.path)) continue;
    seen.add(m.path);
    if (m.beyond) {
      unique.push(m);
      continue;
    }
    const pt = m.lat != null && m.lon != null ? m : nearestPoint(gpx.track, m.ts);
    unique.push({
      ...m,
      lat: m.lat ?? pt.lat,
      lon: m.lon ?? pt.lon,
      ele: m.ele ?? pt.ele,
    });
  }
  return unique;
}

/** Journey parameter for presence: on-track 0..1, floaters just outside. */
function timeTForItem(item) {
  if (item?.beyond === "before") {
    const t = item.floatT ?? 0.5;
    // Spread just before the trailhead so they bloom when scroll ≈ 0
    return -0.015 - (1 - t) * 0.11;
  }
  if (item?.beyond === "after") {
    const t = item.floatT ?? 0.5;
    return 1.015 + t * 0.11;
  }
  return timeNorm(item);
}

/** Place off-track frames in floating clouds beyond the path ends. */
function positionForItem(item, project, trackPoints, curve) {
  if (!item.beyond) {
    return project(item.lat, item.lon, item.ele);
  }

  const up = new THREE.Vector3(0, 1, 0);
  const t = item.floatT ?? 0.5;
  if (item.beyond === "before") {
    const origin = trackPoints[0];
    const tan = curve.getTangentAt(0.002).normalize();
    let side = new THREE.Vector3().crossVectors(tan, up);
    if (side.lengthSq() < 1e-6) side.set(1, 0, 0);
    else side.normalize();
    return origin
      .clone()
      .addScaledVector(tan, -(50 + t * 200))
      .addScaledVector(side, 70 + Math.sin(t * 10.3) * 50)
      .addScaledVector(up, 20 + Math.cos(t * 7.1) * 40);
  }

  const origin = trackPoints[trackPoints.length - 1];
  const tan = curve.getTangentAt(0.998).normalize();
  let side = new THREE.Vector3().crossVectors(tan, up);
  if (side.lengthSq() < 1e-6) side.set(1, 0, 0);
  else side.normalize();
  return origin
    .clone()
    .addScaledVector(tan, 50 + t * 200)
    .addScaledVector(side, -(70 + Math.sin(t * 9.7) * 50))
    .addScaledVector(up, 20 + Math.cos(t * 6.4) * 40);
}

const ALTITUDE_LINE_COLOR = 0x9a9a9a;

function makeStrokeLine(points, { transparent = false } = {}) {
  const geo = new THREE.BufferGeometry().setFromPoints(points);
  const mat = new THREE.LineBasicMaterial({
    color: ALTITUDE_LINE_COLOR,
    linewidth: 1, // most platforms ignore >1; keep as a hairline stroke
    transparent,
    opacity: 1,
  });
  const line = new THREE.Line(geo, mat);
  line.frustumCulled = false;
  return line;
}

function makeTrackMesh(points) {
  const curve = new THREE.CatmullRomCurve3(points, false, "catmullrom", 0.15);
  const segs = Math.max(points.length * 2, 64);
  const sampled = curve.getPoints(segs);
  return { mesh: makeStrokeLine(sampled), curve };
}

function lerpRgb(a, b, t) {
  return {
    r: a.r + (b.r - a.r) * t,
    g: a.g + (b.g - a.g) * t,
    b: a.b + (b.b - a.b) * t,
  };
}

/** Interpolate / extrapolate key colours along the hike timeline. */
function buildJourneyColorField(markers) {
  const raw = markers
    .map((g) => {
      const c = g.userData.keyColor;
      if (!c || g.userData.timeT == null) return null;
      return { t: g.userData.timeT, r: c.r, g: c.g, b: c.b };
    })
    .filter(Boolean)
    .sort((a, b) => a.t - b.t);

  // Merge samples that sit on nearly the same moment
  const field = [];
  for (const s of raw) {
    const prev = field[field.length - 1];
    if (prev && Math.abs(prev.t - s.t) < 0.008) {
      prev.r = (prev.r + s.r) * 0.5;
      prev.g = (prev.g + s.g) * 0.5;
      prev.b = (prev.b + s.b) * 0.5;
    } else {
      field.push({ ...s });
    }
  }
  return field;
}

function sampleJourneyColor(field, t) {
  if (!field.length) return { r: 170, g: 170, b: 170 };
  if (field.length === 1) return { r: field[0].r, g: field[0].g, b: field[0].b };

  if (t <= field[0].t) {
    const u = (t - field[0].t) / Math.max(field[1].t - field[0].t, 1e-6);
    const c = lerpRgb(field[0], field[1], u);
    return {
      r: clamp(c.r, 0, 255),
      g: clamp(c.g, 0, 255),
      b: clamp(c.b, 0, 255),
    };
  }
  const last = field.length - 1;
  if (t >= field[last].t) {
    const u =
      (t - field[last - 1].t) /
      Math.max(field[last].t - field[last - 1].t, 1e-6);
    const c = lerpRgb(field[last - 1], field[last], u);
    return {
      r: clamp(c.r, 0, 255),
      g: clamp(c.g, 0, 255),
      b: clamp(c.b, 0, 255),
    };
  }

  let i = 0;
  while (i < last && field[i + 1].t < t) i++;
  const a = field[i];
  const b = field[i + 1];
  const u = (t - a.t) / Math.max(b.t - a.t, 1e-6);
  // Smoothstep for gentler blends between photos
  const s = u * u * (3 - 2 * u);
  return lerpRgb(a, b, s);
}

function applyJourneyAtmosphere(progress) {
  if (inspectHold.active) {
    applyInspectAtmosphere();
    return;
  }

  const key = sampleJourneyColor(journeyColors, progress);
  smoothJourneyColor = lerpRgb(smoothJourneyColor, key, 0.07);

  // Canvas stays pure white; journey colour drives the difference type only
  if (scene?.background) scene.background.setRGB(1, 1, 1);
  if (scene?.fog) scene.fog.color.setRGB(1, 1, 1);

  document.documentElement.style.setProperty(
    "--journey",
    `rgb(${Math.round(smoothJourneyColor.r)}, ${Math.round(
      smoothJourneyColor.g
    )}, ${Math.round(smoothJourneyColor.b)})`
  );
}

function loadImageElement(url) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.crossOrigin = "anonymous";
    img.onload = () => resolve(img);
    img.onerror = reject;
    img.src = url;
  });
}

function rgbToHsl(r, g, b) {
  r /= 255;
  g /= 255;
  b /= 255;
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const l = (max + min) / 2;
  if (max === min) return { h: 0, s: 0, l };
  const d = max - min;
  const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
  let h = 0;
  if (max === r) h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
  else if (max === g) h = ((b - r) / d + 2) / 6;
  else h = ((r - g) / d + 4) / 6;
  return { h, s, l };
}

function hslToRgb(h, s, l) {
  if (s === 0) {
    const v = Math.round(l * 255);
    return { r: v, g: v, b: v };
  }
  const hue2rgb = (p, q, t) => {
    if (t < 0) t += 1;
    if (t > 1) t -= 1;
    if (t < 1 / 6) return p + (q - p) * 6 * t;
    if (t < 1 / 2) return q;
    if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
    return p;
  };
  const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
  const p = 2 * l - q;
  return {
    r: Math.round(hue2rgb(p, q, h + 1 / 3) * 255),
    g: Math.round(hue2rgb(p, q, h) * 255),
    b: Math.round(hue2rgb(p, q, h - 1 / 3) * 255),
  };
}

function extractKeyColor(data) {
  const buckets = new Map();
  let fallbackR = 0;
  let fallbackG = 0;
  let fallbackB = 0;
  let fallbackN = 0;

  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const a = data[i + 3];
    if (a < 200) continue;
    const lum = r * 0.299 + g * 0.587 + b * 0.114;
    fallbackR += r;
    fallbackG += g;
    fallbackB += b;
    fallbackN++;
    if (lum < 28 || lum > 230) continue;
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    if (max - min < 18) continue;
    const key = `${r >> 4},${g >> 4},${b >> 4}`;
    const bucket = buckets.get(key) || { r: 0, g: 0, b: 0, n: 0 };
    bucket.r += r;
    bucket.g += g;
    bucket.b += b;
    bucket.n++;
    buckets.set(key, bucket);
  }

  let best = null;
  for (const bucket of buckets.values()) {
    if (!best || bucket.n > best.n) best = bucket;
  }
  if (best && best.n > 8) {
    return {
      r: Math.round(best.r / best.n),
      g: Math.round(best.g / best.n),
      b: Math.round(best.b / best.n),
    };
  }
  if (fallbackN) {
    return {
      r: Math.round(fallbackR / fallbackN),
      g: Math.round(fallbackG / fallbackN),
      b: Math.round(fallbackB / fallbackN),
    };
  }
  return { r: 90, g: 90, b: 90 };
}

/** True mean RGB of opaque pixels — used for the intro flat swatches. */
function averageColorFromPixels(data) {
  let r = 0;
  let g = 0;
  let b = 0;
  let n = 0;
  for (let i = 0; i < data.length; i += 4) {
    if (data[i + 3] < 200) continue;
    r += data[i];
    g += data[i + 1];
    b += data[i + 2];
    n++;
  }
  if (!n) return { r: 140, g: 140, b: 140 };
  return {
    r: Math.round(r / n),
    g: Math.round(g / n),
    b: Math.round(b / n),
  };
}

/** Push extracted photo colour toward higher chroma / clearer value. */
function contrastBoostColor(rgb, role = "mid") {
  let { h, s, l } = rgbToHsl(rgb.r, rgb.g, rgb.b);
  // Expand saturation hard so layers read as the photo's palette
  s = clamp(Math.pow(Math.max(s, 0.08), 0.72) * 1.65 + 0.18, 0.28, 0.96);
  if (role === "foreground") {
    l = clamp(l * 0.62 + 0.08, 0.18, 0.42);
  } else if (role === "mid") {
    l = clamp((l - 0.5) * 1.25 + 0.48, 0.34, 0.62);
  } else {
    // background — keep airy but not washed out
    l = clamp(l * 0.55 + 0.42, 0.52, 0.84);
    s = clamp(s * 0.92, 0.22, 0.9);
  }
  return hslToRgb(h, s, l);
}

/**
 * Average the real pixels in each luminance band, then contrast-boost.
 * Returns { foreground, mid, background }.
 */
function extractDepthPalette(pixels, gray, cutA, cutB) {
  const acc = {
    foreground: { r: 0, g: 0, b: 0, n: 0, cr: 0, cg: 0, cb: 0, cn: 0 },
    mid: { r: 0, g: 0, b: 0, n: 0, cr: 0, cg: 0, cb: 0, cn: 0 },
    background: { r: 0, g: 0, b: 0, n: 0, cr: 0, cg: 0, cb: 0, cn: 0 },
  };

  for (let p = 0, i = 0; p < gray.length; p++, i += 4) {
    const a = pixels[i + 3];
    if (a < 180) continue;
    const r = pixels[i];
    const g = pixels[i + 1];
    const b = pixels[i + 2];
    const lum = gray[p];
    const role =
      lum <= cutA ? "foreground" : lum <= cutB ? "mid" : "background";
    const bucket = acc[role];
    bucket.r += r;
    bucket.g += g;
    bucket.b += b;
    bucket.n++;
    const span = Math.max(r, g, b) - Math.min(r, g, b);
    if (span >= 14) {
      bucket.cr += r;
      bucket.cg += g;
      bucket.cb += b;
      bucket.cn++;
    }
  }

  const avg = (bucket) => {
    if (bucket.cn > 6) {
      return {
        r: Math.round(bucket.cr / bucket.cn),
        g: Math.round(bucket.cg / bucket.cn),
        b: Math.round(bucket.cb / bucket.cn),
      };
    }
    if (bucket.n > 0) {
      return {
        r: Math.round(bucket.r / bucket.n),
        g: Math.round(bucket.g / bucket.n),
        b: Math.round(bucket.b / bucket.n),
      };
    }
    return null;
  };

  const fg = avg(acc.foreground) || { r: 70, g: 55, b: 40 };
  const mid = avg(acc.mid) || extractKeyColor(pixels);
  const bg = avg(acc.background) || { r: 170, g: 190, b: 210 };

  return {
    foreground: contrastBoostColor(fg, "foreground"),
    mid: contrastBoostColor(mid, "mid"),
    background: contrastBoostColor(bg, "background"),
  };
}

/** Percentile stretch so underexposed frames regain shape for banding. */
function stretchGray(gray) {
  const hist = new Uint32Array(256);
  let sum = 0;
  for (let i = 0; i < gray.length; i++) {
    hist[gray[i]]++;
    sum += gray[i];
  }
  const meanLum = sum / gray.length;
  const total = gray.length;
  const pick = (q) => {
    const target = total * q;
    let acc = 0;
    for (let i = 0; i < 256; i++) {
      acc += hist[i];
      if (acc >= target) return i;
    }
    return 255;
  };
  let lo = pick(0.02);
  let hi = pick(0.98);
  if (hi - lo < 24) {
    lo = pick(0.005);
    hi = Math.max(lo + 32, pick(0.995));
  }
  if (hi <= lo) {
    lo = 0;
    hi = 255;
  }
  const span = hi - lo;
  const out = new Uint8ClampedArray(gray.length);
  const gamma = meanLum < 70 ? lerp(0.65, 1, meanLum / 70) : 1;
  for (let i = 0; i < gray.length; i++) {
    const n = clamp((gray[i] - lo) / span, 0, 1);
    out[i] = Math.round(Math.pow(n, gamma) * 255);
  }
  return { gray: out, meanLum, lo, hi };
}

/** Thresholds spaced across the stretched histogram (altitude biases the window). */
function layerThresholdsForGray(stretched, count, altitudeBase) {
  const hist = new Uint32Array(256);
  for (let i = 0; i < stretched.length; i++) hist[stretched[i]]++;
  const total = stretched.length;
  const bias = clamp((altitudeBase - 100) / 160, -0.2, 0.25);
  const steps = [];
  for (let i = 1; i <= count; i++) {
    const q = clamp(i / count + bias * (1 - i / count), 0.06, 0.98);
    const target = total * q;
    let acc = 0;
    let val = 255;
    for (let b = 0; b < 256; b++) {
      acc += hist[b];
      if (acc >= target) {
        val = b;
        break;
      }
    }
    if (steps.length && val <= steps[steps.length - 1]) {
      val = Math.min(255, steps[steps.length - 1] + 1);
    }
    steps.push(val);
  }
  steps[steps.length - 1] = 255;
  return steps;
}

/**
 * Estimate framing density from luminance.
 * 0 ≈ open landscape / zoomed out · 1 ≈ dense close-up.
 */
function estimateCloseness(gray, w, h) {
  const tile = 10;
  let topTiles = 0;
  let skyTiles = 0;
  let centerVar = 0;
  let centerN = 0;
  let rimVar = 0;
  let rimN = 0;
  let gradSum = 0;
  let gradN = 0;

  for (let ty = 0; ty < h; ty += tile) {
    for (let tx = 0; tx < w; tx += tile) {
      let sum = 0;
      let sumSq = 0;
      let n = 0;
      const y1 = Math.min(h, ty + tile);
      const x1 = Math.min(w, tx + tile);
      for (let y = ty; y < y1; y++) {
        const row = y * w;
        for (let x = tx; x < x1; x++) {
          const v = gray[row + x];
          sum += v;
          sumSq += v * v;
          n++;
          if (x + 1 < x1) {
            gradSum += Math.abs(v - gray[row + x + 1]);
            gradN++;
          }
          if (y + 1 < y1) {
            gradSum += Math.abs(v - gray[row + w + x]);
            gradN++;
          }
        }
      }
      if (!n) continue;
      const mean = sum / n;
      const variance = Math.max(0, sumSq / n - mean * mean);
      const cy = (ty + tile * 0.5) / h;
      const cx = (tx + tile * 0.5) / w;
      const inCenter = cx > 0.22 && cx < 0.78 && cy > 0.18 && cy < 0.82;

      if (cy < 0.34) {
        topTiles++;
        if (mean > 145 && variance < 520) skyTiles++;
      }
      if (inCenter) {
        centerVar += variance;
        centerN++;
      } else {
        rimVar += variance;
        rimN++;
      }
    }
  }

  const skyFrac = topTiles ? skyTiles / topTiles : 0;
  const cVar = centerN ? centerVar / centerN : 0;
  const rVar = rimN ? rimVar / rimN : 1;
  // Subject filling the frame: stronger structure in the center than the rim
  const centerFill = clamp(cVar / (rVar + 80), 0, 2.2) / 2.2;
  // Fine local contrast — close rock/plant texture runs high
  const texture = clamp((gradN ? gradSum / gradN : 0) / 28, 0, 1);
  // Open views often keep a bright, calm upper band
  const openAir = clamp(skyFrac, 0, 1);

  const closeness =
    (1 - openAir) * 0.42 + centerFill * 0.33 + texture * 0.25 - openAir * 0.12;
  return clamp(closeness, 0, 1);
}

async function getGrayBuffer(url) {
  if (imageCache.has(url)) return imageCache.get(url);
  const img = await loadImageElement(url);
  const maxW = 320;
  const scale = Math.min(1, maxW / img.naturalWidth);
  const w = Math.max(1, Math.round(img.naturalWidth * scale));
  const h = Math.max(1, Math.round(img.naturalHeight * scale));
  const canvas = document.createElement("canvas");
  canvas.width = w;
  canvas.height = h;
  const ctx = canvas.getContext("2d", { willReadFrequently: true });
  ctx.drawImage(img, 0, 0, w, h);
  const { data: pixels } = ctx.getImageData(0, 0, w, h);
  const gray = new Uint8ClampedArray(w * h);
  for (let i = 0, p = 0; i < pixels.length; i += 4, p++) {
    gray[p] =
      (pixels[i] * 0.299 + pixels[i + 1] * 0.587 + pixels[i + 2] * 0.114) | 0;
  }
  const { gray: stretched, meanLum } = stretchGray(gray);
  let cutA = grayPercentile(stretched, 0.34);
  let cutB = grayPercentile(stretched, 0.67);
  if (cutB <= cutA) {
    cutA = 85;
    cutB = 170;
  }
  const palette = extractDepthPalette(pixels, stretched, cutA, cutB);
  const avgColor = averageColorFromPixels(pixels);
  const human = estimateHumanPresence(pixels, w, h);
  const entry = {
    width: w,
    height: h,
    gray,
    stretched,
    meanLum,
    cutA,
    cutB,
    palette,
    avgColor,
    keyColor: palette.mid,
    closeness: estimateCloseness(gray, w, h),
    human,
    sourceUrl: url,
  };
  imageCache.set(url, entry);
  return entry;
}

/** Stretch framing scores across the hike so Light↔Black actually hits. */
function calibrateClosenessExtent(markers) {
  let min = Infinity;
  let max = -Infinity;
  for (const g of markers) {
    const c = g.userData.closeness;
    if (c == null) continue;
    if (c < min) min = c;
    if (c > max) max = c;
  }
  if (!Number.isFinite(min) || !Number.isFinite(max) || max - min < 0.08) {
    closenessExtent = { min: 0, max: 1 };
  } else {
    // Slight pad so extremes still land on Light / Black
    const pad = (max - min) * 0.06;
    closenessExtent = { min: min + pad, max: max - pad };
  }
}

/** Map raw closeness → 0..1 with hard contrast for dramatic weight swings. */
function dramaticCloseness(raw) {
  const { min, max } = closenessExtent;
  let n = (raw - min) / Math.max(max - min, 1e-6);
  n = clamp(n, 0, 1);
  // S-curve then expand past mid so scrolls feel decisive
  const s = n * n * (3 - 2 * n);
  return clamp((s - 0.5) * 1.85 + 0.5, 0, 1);
}

async function loadBrandFonts() {
  await Promise.all(
    BRAND_WEIGHTS.map((w) => document.fonts.load(`${w} 180px "Garara"`))
  );
}

function captionForItem(item) {
  if (!item) return TITLE_FALLBACK;
  const basename = (item.path || item.thumb || "")
    .split("/")
    .pop();
  const phrase =
    captionsById[item.id] ||
    captionsById[item.name] ||
    (basename ? captionsById[basename] : null) ||
    TITLE_FALLBACK;
  return String(phrase).toLowerCase();
}

/** Update centered narrative title: exclusion blend, variable light weight. */
function setBrandWeightFromCloseness(closeness, text = titleText) {
  const el = els.pageTitle;
  if (!el) return;
  const dramatized = dramaticCloseness(closeness);
  const idx = Math.round(dramatized * (BRAND_WEIGHTS.length - 1));
  const weight = BRAND_WEIGHTS[clamp(idx, 0, BRAND_WEIGHTS.length - 1)];
  const phrase = (text || TITLE_FALLBACK).trim().toLowerCase() || TITLE_FALLBACK;
  const key = `${weight}|${phrase}`;
  if (key === lastTitleKey) return;
  lastTitleKey = key;
  titleText = phrase;
  el.textContent = phrase;
  el.style.fontWeight = String(weight);
}

function layerThresholds(base, count) {
  const start = Math.max(12, base - 50);
  const end = Math.min(248, base + 110);
  const steps = [];
  for (let i = 1; i <= count; i++) {
    steps.push(Math.round(start + ((end - start) * i) / count));
  }
  return steps;
}

function resampleSeries(values, n) {
  if (!values.length) return new Float32Array(n);
  const out = new Float32Array(n);
  for (let i = 0; i < n; i++) {
    const t = (i / Math.max(n - 1, 1)) * (values.length - 1);
    const lo = Math.floor(t);
    const hi = Math.min(values.length - 1, lo + 1);
    const f = t - lo;
    out[i] = values[lo] * (1 - f) + values[hi] * f;
  }
  return out;
}

function normalizeSeries(values) {
  let min = Infinity;
  let max = -Infinity;
  for (const v of values) {
    if (v < min) min = v;
    if (v > max) max = v;
  }
  const span = Math.max(max - min, 1e-6);
  const out = new Float32Array(values.length);
  for (let i = 0; i < values.length; i++) out[i] = (values[i] - min) / span;
  return out;
}

function buildAltitudeTemplate(track, samples = 64) {
  const eles = track.map((p) => p.ele).filter((e) => e != null);
  return normalizeSeries(resampleSeries(eles, samples));
}

/** Percentile cut on a luminance buffer. */
function grayPercentile(gray, q) {
  const hist = new Uint32Array(256);
  for (let i = 0; i < gray.length; i++) hist[gray[i]]++;
  const target = gray.length * clamp(q, 0, 1);
  let acc = 0;
  for (let b = 0; b < 256; b++) {
    acc += hist[b];
    if (acc >= target) return b;
  }
  return 255;
}

/**
 * Split each image into exactly 3 depth planes by luminance:
 * foreground (dark / near) · mid · background (light / far).
 */
function buildDepthLayerCanvases(grayEntry) {
  const { width: w, height: h } = grayEntry;
  const gray = grayEntry.stretched || grayEntry.gray;
  let cutA = grayEntry.cutA ?? grayPercentile(gray, 0.34);
  let cutB = grayEntry.cutB ?? grayPercentile(gray, 0.67);
  if (cutB <= cutA) {
    cutA = 85;
    cutB = 170;
  }

  const palette = grayEntry.palette || {
    foreground: contrastBoostColor(grayEntry.keyColor || { r: 80, g: 60, b: 40 }, "foreground"),
    mid: contrastBoostColor(grayEntry.keyColor || { r: 120, g: 110, b: 90 }, "mid"),
    background: contrastBoostColor({ r: 160, g: 180, b: 200 }, "background"),
  };

  const bands = ["foreground", "mid", "background"];

  return bands.map((role) => {
    const canvas = document.createElement("canvas");
    canvas.width = w;
    canvas.height = h;
    const ctx = canvas.getContext("2d");
    const img = ctx.createImageData(w, h);
    const out = img.data;
    const { r, g, b } = palette[role];
    for (let p = 0, i = 0; p < gray.length; p++, i += 4) {
      const lum = gray[p];
      let keep = false;
      if (role === "foreground") keep = lum <= cutA;
      else if (role === "mid") keep = lum > cutA && lum <= cutB;
      else keep = lum > cutB;

      if (keep) {
        out[i] = r;
        out[i + 1] = g;
        out[i + 2] = b;
        out[i + 3] = 255;
      } else {
        out[i + 3] = 0;
      }
    }
    ctx.putImageData(img, 0, 0);
    return { role, canvas };
  });
}

function canvasToTexture(canvas) {
  const tex = new THREE.CanvasTexture(canvas);
  tex.colorSpace = THREE.SRGBColorSpace;
  tex.anisotropy = 2;
  tex.needsUpdate = true;
  return tex;
}

function disposeObject3D(obj) {
  if (obj.material) {
    const mats = Array.isArray(obj.material) ? obj.material : [obj.material];
    mats.forEach((m) => {
      if (m.map) m.map.dispose();
      m.dispose();
    });
  }
  if (obj.geometry) obj.geometry.dispose();
}

function clearMarkerVisuals(group) {
  const facing = group.userData.facing;
  if (facing) {
    for (const child of [...facing.children]) {
      disposeObject3D(child);
      facing.remove(child);
    }
  }
  for (const child of [...group.children]) {
    if (child.userData?.keep) continue;
    disposeObject3D(child);
    group.remove(child);
  }
}

function setGroupPresence(group, amount) {
  const a = clamp(amount, 0, 1);
  group.visible = a > 0.03;
  if (!group.visible) return;
  const s = lerp(0.4, 1.05, a);
  group.scale.setScalar(s);
  group.traverse((obj) => {
    if ((!obj.isMesh && !obj.isLine) || !obj.material) return;
    const mats = Array.isArray(obj.material) ? obj.material : [obj.material];
    mats.forEach((m) => {
      m.transparent = true;
      m.opacity = a;
      if ("depthWrite" in m) m.depthWrite = a > 0.55;
    });
  });
}

function applyMarkerVisualMode(group, mode) {
  const flat = mode === "flat";
  const swatch = group.userData.flatPlane;
  if (swatch) swatch.visible = flat;
  for (const p of group.userData.planes || []) {
    p.visible = !flat;
  }
}

function setAllMarkersVisualMode(mode) {
  for (const g of interactives) applyMarkerVisualMode(g, mode);
  for (const g of selfieInteractives) applyMarkerVisualMode(g, mode);
}

async function rebuildMarkerVisuals(group) {
  const item = group.userData.item;
  if (!item) return;

  clearMarkerVisuals(group);
  group.userData.flatPlane = null;

  let facing = group.userData.facing;
  if (!facing) {
    facing = new THREE.Group();
    facing.userData.keep = true;
    group.add(facing);
    group.userData.facing = facing;
  }
  applyCaptureFacing(facing, headingForItem(item));

  const url = item.thumb || item.path;
  const planes = [];
  group.visible = true;

  let closeness = 0.35;
  let keyColor = { r: 140, g: 140, b: 140 };
  let avgColor = { r: 140, g: 140, b: 140 };
  const showFlat = introActive;
  try {
    const gray = await getGrayBuffer(url);
    closeness = gray.closeness ?? 0.35;
    keyColor = gray.keyColor || keyColor;
    avgColor = gray.avgColor || keyColor;

    const flatPlane = new THREE.Mesh(
      new THREE.PlaneGeometry(26, 19.5),
      new THREE.MeshBasicMaterial({
        color: new THREE.Color(avgColor.r / 255, avgColor.g / 255, avgColor.b / 255),
        transparent: true,
        depthWrite: false,
        side: THREE.DoubleSide,
      })
    );
    flatPlane.position.y = 18;
    flatPlane.userData.flatSwatch = true;
    flatPlane.userData.hitGroup = group;
    flatPlane.visible = showFlat;
    facing.add(flatPlane);
    group.userData.flatPlane = flatPlane;

    const depthLayers = buildDepthLayerCanvases(gray);
    // Stack into the scene: foreground nearest the viewer, background furthest
    const stack = {
      foreground: { z: -0.9, scale: 0.97 },
      mid: { z: 1.35, scale: 1 },
      background: { z: 3.5, scale: 1.06 },
    };
    depthLayers.forEach(({ role, canvas }) => {
      const layout = stack[role] || stack.mid;
      const tex = canvasToTexture(canvas);
      const plane = new THREE.Mesh(
        new THREE.PlaneGeometry(26, 19.5),
        new THREE.MeshBasicMaterial({
          map: tex,
          transparent: true,
          depthWrite: false,
          side: THREE.DoubleSide,
        })
      );
      plane.position.y = 18;
      plane.position.z = layout.z;
      plane.userData.baseZ = layout.z;
      plane.userData.depthRole = role;
      plane.userData.hitGroup = group;
      plane.scale.set(layout.scale, layout.scale, 1);
      plane.visible = !showFlat;
      facing.add(plane);
      planes.push(plane);
    });
  } catch {
    // leave empty if silhouette fails
  }

  group.userData.planes = planes;
  group.userData.sourcePlane = null;
  group.userData.timeT = timeTForItem(item);
  group.userData.closeness = closeness;
  group.userData.keyColor = keyColor;
  group.userData.avgColor = avgColor;
}

async function makeMediaMarker(item, position) {
  const group = new THREE.Group();
  group.position.copy(position);
  group.userData = {
    item,
    timeT: timeTForItem(item),
    hikePos: position.clone(),
  };

  // Same thin grey stroke as the altitude path — track → image plane
  const stem = makeStrokeLine(
    [new THREE.Vector3(0, 0, 0), new THREE.Vector3(0, 18, 0)],
    { transparent: true }
  );
  stem.userData.keep = true;
  stem.userData.stem = true;
  group.add(stem);
  group.userData.stem = stem;

  await rebuildMarkerVisuals(group);
  return group;
}

function markerStem(group) {
  return group.userData.stem || null;
}

function setStemVisible(group, visible) {
  const stem = markerStem(group);
  if (stem) stem.visible = visible;
}

function restoreHikeLayout() {
  for (const g of interactives) {
    const home = g.userData.hikePos;
    if (home) g.position.copy(home);
    g.rotation.set(0, 0, 0);
    g.scale.setScalar(1);
    setStemVisible(g, true);
    const facing = g.userData.facing;
    if (facing) {
      applyCaptureFacing(facing, headingForItem(g.userData.item));
      facing.position.set(0, 0, 0);
      facing.rotation.x = 0;
      facing.rotation.z = 0;
      facing.scale.setScalar(1);
      for (const p of g.userData.planes || []) {
        if (p.userData.baseZ != null) p.position.z = p.userData.baseZ;
      }
    }
  }
  if (trackMesh) trackMesh.visible = true;
  restoreJourneyFog();
}

function loadTexture(url) {
  return new Promise((resolve, reject) => {
    const loader = new THREE.TextureLoader();
    loader.load(
      url,
      (tex) => {
        tex.colorSpace = THREE.SRGBColorSpace;
        tex.anisotropy = 2;
        resolve(tex);
      },
      undefined,
      reject
    );
  });
}

/** Pull front-camera stills onto one shared wall plane. */
async function buildSelfiePlane() {
  if (selfieGroup) {
    scene.remove(selfieGroup);
    selfieGroup.traverse((obj) => disposeObject3D(obj));
  }

  selfieGroup = new THREE.Group();
  selfieGroup.visible = false;
  selfieItems = (data?.media || [])
    .filter((m) => isFrontCameraItem(m) && m.kind === "image" && m.thumb)
    .sort((a, b) => (a.ts || 0) - (b.ts || 0));

  const n = selfieItems.length;
  if (!n) {
    scene.add(selfieGroup);
    return;
  }

  const cols = Math.ceil(Math.sqrt(n));
  const rows = Math.ceil(n / cols);
  const cellW = 20;
  const cellH = 26;
  const gap = 2.4;
  const boardW = cols * (cellW + gap) + gap;
  const boardH = rows * (cellH + gap) + gap;

  const board = new THREE.Mesh(
    new THREE.PlaneGeometry(boardW, boardH),
    new THREE.MeshBasicMaterial({
      color: 0xf0f0f0,
      transparent: true,
      opacity: 0.96,
      side: THREE.DoubleSide,
    })
  );
  board.position.z = -0.8;
  board.userData.board = true;
  selfieGroup.add(board);

  await Promise.all(
    selfieItems.map(async (item, i) => {
      try {
        const tex = await loadTexture(item.thumb);
        const mesh = new THREE.Mesh(
          new THREE.PlaneGeometry(cellW, cellH),
          new THREE.MeshBasicMaterial({
            map: tex,
            side: THREE.DoubleSide,
            transparent: true,
          })
        );
        const col = i % cols;
        const row = Math.floor(i / cols);
        mesh.position.set(
          (col - (cols - 1) / 2) * (cellW + gap),
          ((rows - 1) / 2 - row) * (cellH + gap),
          0.05
        );
        mesh.userData.item = item;
        mesh.userData.selfieIndex = i;
        mesh.userData.baseScale = 1;
        selfieGroup.add(mesh);
      } catch (err) {
        console.warn("Selfie texture failed", item.thumb, err);
      }
    })
  );

  scene.add(selfieGroup);
}

function setHikeWorldVisible(visible) {
  for (const g of interactives) {
    g.visible = visible;
    if (visible) setStemVisible(g, true);
  }
  if (trackMesh) trackMesh.visible = visible;
}

function setSelfieCardsVisible(visible) {
  for (const g of selfieInteractives) {
    g.visible = visible;
    if (!visible) setGroupPresence(g, 0);
  }
}

function enterTimelineMode() {
  document.documentElement.style.overflow = "hidden";
  leaveTunnelMode();
  setHikeWorldVisible(false);
  setSelfieCardsVisible(true);
  for (const g of selfieInteractives) {
    setStemVisible(g, false);
    applyMarkerVisualMode(g, "layers");
  }
  if (trackMesh) trackMesh.visible = false;
  if (selfieGroup) selfieGroup.visible = false;
  if (scene?.fog) {
    scene.fog.near = 40;
    scene.fog.far = 280;
  }
  const cards = timelineCards();
  const n = Math.max(cards.length - 1, 1);
  let best = 0;
  let bestD = Infinity;
  for (let i = 0; i < cards.length; i++) {
    const d = Math.abs(cards[i].userData.timeT - smoothProgress);
    if (d < bestD) {
      bestD = d;
      best = i;
    }
  }
  timelineFocus = best;
  timelineFocusSmooth = best;
  timelinePointerX = cards.length <= 1 ? 0.5 : best / n;
  if (els.scrollHint) {
    els.scrollHint.textContent = cards.length
      ? "MOVE TO BROWSE"
      : "NO SELFIES FOUND";
    els.scrollHint.classList.remove("is-gone");
    hintHidden = false;
  }
  if (els.viewport) els.viewport.setAttribute("aria-label", "Selfies rolodex");
}

function enterSelfieMode() {
  document.documentElement.style.overflow = "hidden";
  restoreHikeLayout();
  setHikeWorldVisible(false);
  if (selfieGroup) selfieGroup.visible = true;
  if (scene?.fog) {
    scene.fog.near = 30;
    scene.fog.far = 220;
  }
  selfieFocus = 0;
  selfieFocusSmooth = 0;
  selfieDrag.yaw = 0;
  selfieDrag.pitch = 0;
  selfieDrag.yawT = 0;
  selfieDrag.pitchT = 0;
  if (els.scrollHint) {
    els.scrollHint.textContent =
      selfieItems.length > 0 ? "DRAG TO LOOK" : "NO SELFIES FOUND";
    els.scrollHint.classList.remove("is-gone");
    hintHidden = false;
  }
  if (els.viewport) els.viewport.setAttribute("aria-label", "Selfie plane");
  setBrandWeightFromCloseness(0.45, captionForItem(selfieItems[0]));
}

function clearTunnelWorld() {
  if (!tunnelGroup) return;
  scene.remove(tunnelGroup);
  tunnelGroup.traverse((obj) => {
    // Tunnel planes share hike marker textures — don't dispose the maps
    if (obj.material) {
      const mats = Array.isArray(obj.material) ? obj.material : [obj.material];
      mats.forEach((m) => {
        m.map = null;
        m.dispose();
      });
    }
    if (obj.geometry) obj.geometry.dispose();
  });
  tunnelGroup = null;
  tunnelPlanes = [];
}

function textureAspect(map) {
  const img = map?.image;
  const w = img?.naturalWidth || img?.width || 4;
  const h = img?.naturalHeight || img?.height || 3;
  return w / Math.max(h, 1e-6);
}

/** One transparent threshold band from a hike marker (shared texture map). */
function tunnelPlaneFromLayer(srcPlane, group, role) {
  const map = srcPlane?.material?.map;
  if (!map) return null;
  const mesh = new THREE.Mesh(
    new THREE.PlaneGeometry(1, 1),
    new THREE.MeshBasicMaterial({
      map,
      transparent: true,
      depthWrite: false,
      side: THREE.DoubleSide,
      opacity: 1,
      alphaTest: 0.04,
    })
  );
  mesh.userData.item = group.userData.item;
  mesh.userData.timeT = group.userData.timeT;
  mesh.userData.depthRole = role;
  mesh.userData.roleScale = TUNNEL_ROLE_SCALE[role] ?? 1;
  mesh.userData.aspect = textureAspect(map);
  return mesh;
}

function ensureTunnelBuilt({ force = false } = {}) {
  if (!force && tunnelGroup && tunnelPlanes.length) return;
  clearTunnelWorld();

  const markers = interactives
    .filter((g) => (g.userData.planes || []).length)
    .sort((a, b) => a.userData.timeT - b.userData.timeT);
  const picks =
    markers.length <= TUNNEL_IMAGE_CAP
      ? markers
      : spacePick(markers, TUNNEL_IMAGE_CAP);

  tunnelGroup = new THREE.Group();
  tunnelGroup.visible = false;
  tunnelPlanes = [];

  // For each image: travel background → mid → foreground (threshold cutouts)
  picks.forEach((g) => {
    const byRole = {};
    for (const p of g.userData.planes || []) {
      if (p.userData?.depthRole) byRole[p.userData.depthRole] = p;
    }
    for (const role of TUNNEL_ROLE_ORDER) {
      const mesh = tunnelPlaneFromLayer(byRole[role], g, role);
      if (!mesh) continue;
      mesh.position.set(0, 0, -tunnelPlanes.length * TUNNEL_GAP);
      mesh.userData.tunnelIndex = tunnelPlanes.length;
      tunnelGroup.add(mesh);
      tunnelPlanes.push(mesh);
    }
  });

  scene.add(tunnelGroup);
}

function enterTunnelMode() {
  document.documentElement.style.overflow = "";
  setHikeWorldVisible(false);
  setSelfieCardsVisible(false);
  if (selfieGroup) selfieGroup.visible = false;
  if (trackMesh) trackMesh.visible = false;

  ensureTunnelBuilt({ force: true });
  if (tunnelGroup) tunnelGroup.visible = true;
  document.documentElement.classList.add("is-tunneling");

  if (scene?.fog) {
    scene.fog.near = 6;
    scene.fog.far = 48;
    scene.fog.color.setRGB(0.07, 0.07, 0.08);
  }
  if (scene?.background) scene.background.setRGB(0.07, 0.07, 0.08);

  const vh = Math.max(640, tunnelPlanes.length * 36);
  if (els.scrollRail) els.scrollRail.style.height = `${vh}vh`;

  window.scrollTo(0, 0);
  tunnelProgress = 0;
  smoothTunnelProgress = 0;
  scrollProgress = 0;
  smoothProgress = 0;

  if (els.scrollHint) {
    els.scrollHint.textContent = tunnelPlanes.length
      ? "SCROLL INTO THE TUNNEL"
      : "NO LAYERS FOUND";
    els.scrollHint.classList.remove("is-gone");
    hintHidden = false;
  }
  if (els.viewport) {
    els.viewport.setAttribute("aria-label", "Layer tunnel");
  }
}

function leaveTunnelMode() {
  if (tunnelGroup) tunnelGroup.visible = false;
  if (els.scrollRail) els.scrollRail.style.height = "";
  document.documentElement.classList.remove("is-tunneling");
}

function enterElevationMode() {
  document.documentElement.style.overflow = "";
  leaveTunnelMode();
  if (selfieGroup) selfieGroup.visible = false;
  setSelfieCardsVisible(false);
  restoreHikeLayout();
  setHikeWorldVisible(true);
  restoreJourneyFog();
  window.scrollTo(0, savedScrollY);
  scrollProgress = readScrollProgress();
  smoothProgress = scrollProgress;
  if (els.scrollHint) {
    els.scrollHint.textContent = "SCROLL TO BEGIN THE PASSAGE";
    if (scrollProgress > 0.01) {
      els.scrollHint.classList.add("is-gone");
      hintHidden = true;
    } else {
      els.scrollHint.classList.remove("is-gone");
      hintHidden = false;
    }
  }
  if (els.viewport) els.viewport.setAttribute("aria-label", "Hike through time");
}

function updateModeToggle() {
  if (!els.modeToggle) return;
  const labels = {
    elevation: "THE HIKE",
    timeline: "SELFIES",
    tunnel: "TUNNEL",
  };
  const next = VIEW_MODES[(VIEW_MODES.indexOf(viewMode) + 1) % VIEW_MODES.length];
  els.modeToggle.textContent = labels[viewMode] || "THE HIKE";
  els.modeToggle.setAttribute(
    "aria-pressed",
    viewMode === "elevation" ? "false" : "true"
  );
  els.modeToggle.setAttribute(
    "aria-label",
    `Current view ${labels[viewMode] || "THE HIKE"}. Click for ${labels[next]}`
  );
}

function setViewMode(mode) {
  if (!VIEW_MODES.includes(mode) || mode === viewMode) return;
  if (introActive) endIntro({ keepHint: true });
  endInspect();

  if (viewMode === "elevation") savedScrollY = window.scrollY;
  if (viewMode === "timeline") {
    document.documentElement.style.overflow = "";
  }
  if (viewMode === "tunnel") leaveTunnelMode();

  viewMode = mode;
  els.experience?.setAttribute("data-mode", mode);

  // Hide the flat selfie board — SELFIES mode is the timeline rolodex
  if (selfieGroup) selfieGroup.visible = false;

  if (mode === "timeline") enterTimelineMode();
  else if (mode === "tunnel") enterTunnelMode();
  else enterElevationMode();

  updateModeToggle();
}

function toggleViewMode() {
  const next = VIEW_MODES[(VIEW_MODES.indexOf(viewMode) + 1) % VIEW_MODES.length];
  setViewMode(next);
}

function activeInspectMarkers() {
  return viewMode === "timeline" ? selfieInteractives : interactives;
}

function pickMarkerAt(clientX, clientY) {
  if (!camera || !els.viewport) return null;
  const rect = els.viewport.getBoundingClientRect();
  if (rect.width <= 0 || rect.height <= 0) return null;
  inspectPointer.x = ((clientX - rect.left) / rect.width) * 2 - 1;
  inspectPointer.y = -((clientY - rect.top) / rect.height) * 2 + 1;
  inspectRaycaster.setFromCamera(inspectPointer, camera);

  const meshes = [];
  for (const g of activeInspectMarkers()) {
    if (!g.visible) continue;
    for (const p of g.userData.planes || []) {
      if (p.visible) meshes.push(p);
    }
    const flat = g.userData.flatPlane;
    if (flat?.visible) meshes.push(flat);
  }
  if (!meshes.length) return null;
  const hits = inspectRaycaster.intersectObjects(meshes, false);
  return hits[0]?.object?.userData?.hitGroup || null;
}

function photoPlaneSize(tex, base = 18) {
  const img = tex?.image;
  const aspect = Math.max(0.35, (img?.naturalWidth || img?.width || 4) / (img?.naturalHeight || img?.height || 3));
  if (aspect >= 1) return { w: base, h: base / aspect };
  return { w: base * aspect, h: base };
}

async function ensureSourcePlane(group) {
  if (group.userData.sourcePlane) return group.userData.sourcePlane;
  const item = group.userData.item;
  const url = item?.thumb || item?.path;
  if (!url) return null;
  const facing = group.userData.facing;
  if (!facing) return null;

  const tex = await loadTexture(url);
  const { w, h } = photoPlaneSize(tex);
  const mesh = new THREE.Mesh(
    new THREE.PlaneGeometry(w, h),
    new THREE.MeshBasicMaterial({
      map: tex,
      transparent: true,
      depthWrite: true,
      side: THREE.DoubleSide,
    })
  );
  mesh.position.set(0, 18, 0.2);
  mesh.visible = false;
  mesh.userData.sourcePhoto = true;
  mesh.userData.hitGroup = group;
  facing.add(mesh);
  group.userData.sourcePlane = mesh;
  return mesh;
}

function setInspectVisuals(group, on) {
  const layered = !introActive;
  for (const p of group.userData.planes || []) {
    p.visible = !on && layered;
  }
  if (group.userData.flatPlane) {
    group.userData.flatPlane.visible = !on && !layered;
  }
  if (group.userData.sourcePlane) {
    group.userData.sourcePlane.visible = on;
  }
  setStemVisible(group, !on && viewMode === "elevation" && !introActive);
}

function inspectBackdropColor(group) {
  const avg = group?.userData?.avgColor || group?.userData?.keyColor || {
    r: 140,
    g: 140,
    b: 140,
  };
  // Backdrop = inverted average colour of the held photo
  return {
    r: (255 - clamp(avg.r, 0, 255)) / 255,
    g: (255 - clamp(avg.g, 0, 255)) / 255,
    b: (255 - clamp(avg.b, 0, 255)) / 255,
  };
}

function applyInspectAtmosphere() {
  const bg = inspectBackdropColor(inspectHold.group);
  if (scene?.background) scene.background.setRGB(bg.r, bg.g, bg.b);
  if (scene?.fog) {
    scene.fog.color.setRGB(bg.r, bg.g, bg.b);
    scene.fog.near = 40;
    scene.fog.far = 260;
  }
  if (trackMesh) trackMesh.visible = false;
  const css = `rgb(${Math.round(bg.r * 255)}, ${Math.round(bg.g * 255)}, ${Math.round(bg.b * 255)})`;
  document.documentElement.style.setProperty("--inspect-bg", css);
  const luma = bg.r * 0.299 + bg.g * 0.587 + bg.b * 0.114;
  document.documentElement.style.setProperty(
    "--inspect-ink",
    luma > 0.55 ? "#111111" : "#f2f2f2"
  );
  els.experience?.setAttribute("data-inspect", "true");
  document.documentElement.classList.add("is-inspecting");
}

async function beginInspect(group, pointerId = null) {
  if (!group) return;
  inspectHold.token += 1;
  const token = inspectHold.token;
  inspectHold.active = true;
  inspectHold.group = group;
  inspectHold.pointerId = pointerId;
  applyInspectAtmosphere();

  // Dim everything else immediately
  for (const g of activeInspectMarkers()) {
    if (g === group) {
      g.visible = true;
      g.scale.setScalar(1);
      continue;
    }
    setGroupPresence(g, 0);
  }

  try {
    await ensureSourcePlane(group);
  } catch (err) {
    console.warn("Inspect photo failed", err);
  }
  if (token !== inspectHold.token || !inspectHold.active) return;
  setInspectVisuals(group, true);
  ensureAudioCtx();
}

function endInspect() {
  if (!inspectHold.active && !inspectHold.group) {
    els.experience?.removeAttribute("data-inspect");
    document.documentElement.classList.remove("is-inspecting");
    document.documentElement.style.removeProperty("--inspect-bg");
    document.documentElement.style.removeProperty("--inspect-ink");
    return;
  }
  const group = inspectHold.group;
  inspectHold.active = false;
  inspectHold.group = null;
  inspectHold.pointerId = null;
  inspectHold.token += 1;

  els.experience?.removeAttribute("data-inspect");
  document.documentElement.classList.remove("is-inspecting");
  document.documentElement.style.removeProperty("--inspect-bg");
  document.documentElement.style.removeProperty("--inspect-ink");

  if (group) {
    setInspectVisuals(group, false);
    if (group.userData.sourcePlane) {
      group.userData.sourcePlane.position.set(0, 18, 0.2);
    }
    group.quaternion.identity();
    const home = group.userData.hikePos;
    if (viewMode === "elevation" && home) {
      group.position.copy(home);
      group.rotation.set(0, 0, 0);
      const facing = group.userData.facing;
      if (facing) {
        applyCaptureFacing(facing, headingForItem(group.userData.item));
        facing.position.set(0, 0, 0);
        facing.rotation.x = 0;
        facing.rotation.z = 0;
        facing.scale.setScalar(1);
      }
    }
  }

  if (viewMode === "elevation") {
    if (trackMesh) trackMesh.visible = true;
    restoreJourneyFog();
  } else if (trackMesh) {
    trackMesh.visible = false;
  }
}

function updateInspectFrame() {
  const group = inspectHold.group;
  if (!group || !camera) return;

  applyInspectAtmosphere();

  for (const g of activeInspectMarkers()) {
    if (g === group) {
      g.visible = true;
      g.scale.setScalar(1);
      continue;
    }
    setGroupPresence(g, 0);
  }

  // Hold the original photo dead-center in front of the camera
  _tmp.set(0, 0, -46).applyQuaternion(camera.quaternion).add(camera.position);
  group.position.lerp(_tmp, 0.28);
  group.quaternion.slerp(camera.quaternion, 0.28);
  group.scale.setScalar(1);

  const facing = group.userData.facing;
  if (facing) {
    facing.position.set(0, 0, 0);
    facing.rotation.set(0, 0, 0);
    facing.scale.setScalar(1);
  }
  const src = group.userData.sourcePlane;
  if (src) src.position.set(0, 0, 0.2);
  setInspectVisuals(group, true);

  const item = group.userData.item;
  const progress = group.userData.timeT ?? smoothProgress;
  updateCornerMeta(clamp(progress, 0, 1), item);
  setBrandWeightFromCloseness(0.72, captionForItem(item));
}

function onInspectPointerDown(e) {
  if (e.button != null && e.button !== 0) return;
  if (inspectHold.active) return;
  if (viewMode === "tunnel") return;
  const group = pickMarkerAt(e.clientX, e.clientY);
  if (!group) return;
  e.preventDefault();
  e.stopPropagation();
  try {
    els.viewport?.setPointerCapture?.(e.pointerId);
  } catch {
    /* ignore */
  }
  beginInspect(group, e.pointerId);
}

function onInspectPointerUp(e) {
  if (!inspectHold.active) return;
  if (
    inspectHold.pointerId != null &&
    e.pointerId != null &&
    e.pointerId !== inspectHold.pointerId
  ) {
    return;
  }
  try {
    els.viewport?.releasePointerCapture?.(e.pointerId);
  } catch {
    /* ignore */
  }
  endInspect();
}

function timelineIndexFromPointer(nx) {
  const n = timelineCards().length;
  if (n <= 1) return 0;
  return clamp(nx, 0, 1) * (n - 1);
}

function onTimelinePointer(e) {
  if (viewMode !== "timeline" || !els.viewport || inspectHold.active) return;
  const rect = els.viewport.getBoundingClientRect();
  if (rect.width <= 0) return;
  timelinePointerX = clamp((e.clientX - rect.left) / rect.width, 0, 1);
  timelineFocus = timelineIndexFromPointer(timelinePointerX);
  if (!hintHidden) hideHint();
  ensureAudioCtx();
}

function onTimelineWheel(e) {
  if (viewMode !== "timeline" || inspectHold.active) return;
  e.preventDefault();
  const n = Math.max(timelineCards().length - 1, 1);
  timelineFocus = clamp(timelineFocus + e.deltaY * 0.01, 0, n);
  timelinePointerX = timelineFocus / n;
  if (!hintHidden) hideHint();
  ensureAudioCtx();
}

function onViewportWheel(e) {
  if (inspectHold.active) {
    e.preventDefault();
    return;
  }
  if (viewMode === "timeline") {
    onTimelineWheel(e);
    return;
  }
  // Viewport captures pointer events — forward scroll for hike + tunnel
  e.preventDefault();
  window.scrollBy(0, e.deltaY);
}

function onSelfiePointerDown(e) {
  if (viewMode !== "selfies") return;
  selfieDrag.active = true;
  selfieDrag.x = e.clientX;
  selfieDrag.y = e.clientY;
  els.viewport?.style.setProperty("cursor", "grabbing");
  if (!hintHidden) hideHint();
  ensureAudioCtx();
}

function onSelfiePointerMove(e) {
  if (viewMode !== "selfies" || !selfieDrag.active) return;
  const dx = e.clientX - selfieDrag.x;
  const dy = e.clientY - (selfieDrag.y || e.clientY);
  selfieDrag.x = e.clientX;
  selfieDrag.y = e.clientY;
  selfieDrag.yawT = clamp(selfieDrag.yawT + dx * 0.004, -0.55, 0.55);
  selfieDrag.pitchT = clamp(selfieDrag.pitchT + dy * 0.003, -0.28, 0.28);
}

function onSelfiePointerUp() {
  if (!selfieDrag.active) return;
  selfieDrag.active = false;
  els.viewport?.style.setProperty("cursor", "grab");
}

function updateSelfies(clockSec = 0) {
  if (!camera || !selfieGroup) return;

  selfieDrag.yaw += (selfieDrag.yawT - selfieDrag.yaw) * 0.12;
  selfieDrag.pitch += (selfieDrag.pitchT - selfieDrag.pitch) * 0.12;

  const idleYaw = Math.sin(clockSec * 0.12) * 0.04;
  const idlePitch = Math.cos(clockSec * 0.09) * 0.02;
  selfieGroup.rotation.y = selfieDrag.yaw + idleYaw;
  selfieGroup.rotation.x = selfieDrag.pitch + idlePitch;

  _camPos.set(0, 2, 90);
  _look.set(0, 0, 0);
  camera.position.lerp(_camPos, 0.14);
  camera.lookAt(_look);

  // Soft focus pulse on the nearest-to-center selfie
  let best = null;
  let bestScore = -Infinity;
  selfieGroup.children.forEach((child) => {
    if (!child.isMesh || child.userData.board) return;
    child.getWorldPosition(_tmp);
    // Prefer frames near the view centre
    const score = -(_tmp.x * _tmp.x * 0.02 + _tmp.y * _tmp.y * 0.02);
    const base = child.userData.baseScale || 1;
    const boost = score > bestScore - 0.5 ? 1.04 : 1;
    child.scale.setScalar(base * boost);
    if (score > bestScore) {
      bestScore = score;
      best = child;
    }
  });

  const activeItem = best?.userData?.item || selfieItems[0];
  if (activeItem) {
    const progress =
      activeItem.ts != null ? timeNormTs(activeItem.ts) : smoothProgress;
    updateCornerMeta(clamp(progress, 0, 1), activeItem);
    setBrandWeightFromCloseness(0.55, captionForItem(activeItem));
  }
  applyJourneyAtmosphere(0.5);
}

function updateTunnel() {
  if (!camera || !tunnelPlanes.length) return;
  if (tunnelGroup) tunnelGroup.visible = true;

  tunnelProgress = readScrollProgress();
  smoothTunnelProgress += (tunnelProgress - smoothTunnelProgress) * 0.055;

  const n = tunnelPlanes.length;
  // Drift forward through fixed planes — perspective grows each layer like a cavern
  const startZ = TUNNEL_GAP * 2.2;
  const endZ = -((n - 1) * TUNNEL_GAP) - TUNNEL_GAP * 1.4;
  const camZ = lerp(startZ, endZ, smoothTunnelProgress);

  camera.position.set(0, 0, camZ);
  camera.lookAt(0, 0, camZ - 60);

  // Keep fog in the cavern register (journey atmosphere would bleach it white)
  if (scene?.background) scene.background.setRGB(0.07, 0.07, 0.08);
  if (scene?.fog) {
    scene.fog.color.setRGB(0.07, 0.07, 0.08);
    scene.fog.near = 6;
    scene.fog.far = 48;
  }

  let activeItem = null;
  let bestAhead = Infinity;

  for (let i = 0; i < n; i++) {
    const mesh = tunnelPlanes[i];
    const planeZ = -i * TUNNEL_GAP;
    mesh.position.set(0, 0, planeZ);
    mesh.rotation.set(0, 0, 0);

    const ahead = camZ - planeZ; // distance still in front of the lens
    if (ahead < 0.25 || ahead > TUNNEL_GAP * 9) {
      mesh.visible = false;
      continue;
    }
    mesh.visible = true;

    // Fixed world size + aspect — camera motion supplies the zoom
    const roleScale = mesh.userData.roleScale ?? 1;
    const aspect = mesh.userData.aspect || 1;
    const h = TUNNEL_WORLD_SIZE * roleScale;
    const w = h * aspect;
    mesh.scale.set(w, h, 1);

    // Only soften right as you pass through a cutout; otherwise hold solid
    const pass = ahead < TUNNEL_GAP * 0.85 ? clamp(ahead / (TUNNEL_GAP * 0.55), 0, 1) : 1;
    const depthDim = clamp(1.05 - ahead / (TUNNEL_GAP * 8), 0.55, 1);
    if (mesh.material) mesh.material.opacity = pass * depthDim;

    if (ahead < bestAhead) {
      bestAhead = ahead;
      activeItem = mesh.userData.item;
    }
  }

  const progress = clamp(smoothTunnelProgress, 0, 1);
  updateCornerMeta(progress, activeItem);
  syncSoundPlayback(progress);

  const close = bestAhead < TUNNEL_GAP * 1.2 ? 0.64 : 0.36;
  smoothCloseness += (close - smoothCloseness) * 0.12;
  setBrandWeightFromCloseness(smoothCloseness, captionForItem(activeItem));

  if (!hintHidden && smoothTunnelProgress > 0.02) hideHint();
}

function updateTimeline(clockSec = 0) {
  const cards = timelineCards();
  if (!camera || !cards.length) return;
  if (selfieGroup) selfieGroup.visible = false;
  if (inspectHold.active) {
    // Keep the rolodex camera, then pin the held photo in the middle
    _camPos.set(0, 14, 78);
    _look.set(0, 12, 0);
    camera.position.lerp(_camPos, 0.18);
    camera.lookAt(_look);
    updateInspectFrame();
    return;
  }

  timelineFocusSmooth += (timelineFocus - timelineFocusSmooth) * 0.14;

  const focusIdx = Math.round(clamp(timelineFocusSmooth, 0, cards.length - 1));
  const active = cards[focusIdx];
  const activeItem = active?.userData?.item;
  const progress = active?.userData?.timeT ?? 0;

  // Fixed camera looking into the flat card rail (cards orbit around x=0)
  _camPos.set(0, 14, 78);
  _look.set(0, 12, 0);
  camera.position.lerp(_camPos, 0.18);
  camera.lookAt(_look);

  let closeSum = 0;
  let closeW = 0;

  for (let i = 0; i < cards.length; i++) {
    const g = cards[i];
    const d = i - timelineFocusSmooth;
    const abs = Math.abs(d);
    const x = d * TIMELINE_CARD_GAP;
    const z = -Math.min(abs, 10) * TIMELINE_RECED;
    const y = Math.sin(Math.min(abs, 4) * 0.35) * -1.2;

    g.position.set(x, y, z);
    g.rotation.set(0, 0, 0);

    const facing = g.userData.facing;
    if (facing) {
      const yaw = -Math.sign(d || 1) * Math.min(abs, 4) * TIMELINE_YAW;
      facing.rotation.set(0, abs < 0.02 ? 0 : yaw, 0);
      facing.scale.setScalar(1);
    }

    // Show a local neighbourhood so the deck reads as a rolodex, not a crowd
    const amount = Math.exp((-abs * abs) / (2 * 2.1 * 2.1));
    setGroupPresence(g, amount);
    // Keep facing controlled by the rolodex (sound motion would reset yaw)

    if (amount > 0.05) {
      closeSum += (g.userData.closeness ?? 0.35) * amount;
      closeW += amount;
    }
  }

  updateCornerMeta(clamp(progress, 0, 1), activeItem);
  syncSoundPlayback(clamp(progress, 0, 1));
  applyJourneyAtmosphere(clamp(progress, 0, 1));

  const targetClose = closeW > 0 ? closeSum / closeW : smoothCloseness;
  smoothCloseness += (targetClose - smoothCloseness) * 0.22;
  setBrandWeightFromCloseness(smoothCloseness, captionForItem(activeItem));
}

function readScrollProgress() {
  const max = Math.max(
    1,
    document.documentElement.scrollHeight - window.innerHeight
  );
  return clamp(window.scrollY / max, 0, 1);
}

function hideHint() {
  if (hintHidden) return;
  hintHidden = true;
  els.scrollHint?.classList.add("is-gone");
}

function stripRtfControls(text) {
  return String(text)
    .replace(/\\'[0-9a-fA-F]{2}/g, "")
    .replace(/\\[a-zA-Z]+-?\d* ?/g, "")
    .replace(/[{}]/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

/** Parse lyrics from .rtf (quoted lines), .txt (one per line), or .json array. */
function parseLyricSource(text, path) {
  if (path.endsWith(".json")) {
    try {
      const raw = JSON.parse(text);
      return Array.isArray(raw)
        ? raw.map((line) => String(line).trim()).filter(Boolean)
        : [];
    } catch {
      return [];
    }
  }

  const quoted = [];
  const re = /"([^"]*)"/g;
  let match;
  while ((match = re.exec(text))) {
    const line = stripRtfControls(match[1]);
    if (line) quoted.push(line);
  }
  if (quoted.length) return quoted;

  return text
    .split(/\r?\n/)
    .map((line) => stripRtfControls(line))
    .filter((line) => line && !line.startsWith("{\\rtf"));
}

async function loadLyricLines() {
  const candidates = [
    "data/lyrics.rtf",
    "data/lyrics.txt",
    "data/lyrics.json",
  ];
  for (const path of candidates) {
    try {
      const res = await fetch(path);
      if (!res.ok) continue;
      const lines = parseLyricSource(await res.text(), path);
      if (lines.length) return lines;
    } catch {
      // try next candidate
    }
  }
  return [];
}

/** Slight opening linger, then pace the rest evenly to the end. */
function lyricWindowAtProgress(progress, n) {
  if (n <= 0) return { index: 0, localT: 0 };
  if (n === 1) return { index: 0, localT: clamp(progress, 0, 1) };
  const p = clamp(progress, 0, 0.9999);
  const firstHold = 0.1;
  if (p < firstHold) {
    return { index: 0, localT: firstHold > 0 ? p / firstHold : 1 };
  }
  const rest = (1 - firstHold) / (n - 1);
  const u = p - firstHold;
  const slot = clamp(Math.floor(u / Math.max(rest, 1e-6)), 0, n - 2);
  const index = slot + 1;
  const localT = clamp((u - slot * rest) / Math.max(rest, 1e-6), 0, 1);
  return { index, localT };
}

function clearLyricBubbles() {
  const stack = els.journeyLyrics;
  if (stack) stack.replaceChildren();
  lyricBubbleIndex = -1;
  lyricBubbleEl = null;
  lastLyricKey = "";
}

function trimLyricBubbles(max = 3) {
  const stack = els.journeyLyrics;
  if (!stack) return;
  // Oldest is first in the DOM (sits highest); newest is last (sits at bottom)
  while (stack.children.length > max) {
    stack.removeChild(stack.firstElementChild);
  }
  const bubbles = [...stack.children];
  bubbles.forEach((bubble, i) => {
    bubble.classList.toggle("is-dim", i < bubbles.length - 1);
  });
}

function ensureLyricBubble(index) {
  const stack = els.journeyLyrics;
  if (!stack) return null;
  if (index === lyricBubbleIndex && lyricBubbleEl) return lyricBubbleEl;

  // Scrolling backward: reset the thread so bubbles stay in order
  if (lyricBubbleIndex >= 0 && index < lyricBubbleIndex) {
    stack.replaceChildren();
    lyricBubbleEl = null;
  } else if (lyricBubbleEl) {
    lyricBubbleEl.classList.remove("is-typing");
    lyricBubbleEl.classList.add("is-dim");
  }

  const bubble = document.createElement("p");
  bubble.className = "journey-lyric-bubble";
  stack.appendChild(bubble);
  // Pop-in on next frame
  requestAnimationFrame(() => bubble.classList.add("is-in"));

  lyricBubbleIndex = index;
  lyricBubbleEl = bubble;
  trimLyricBubbles(3);
  return bubble;
}

/** Bottom-left chat bubbles; full lines pop in as you scroll. */
function updateJourneyLyric(progress) {
  const stack = els.journeyLyrics;
  if (!stack) return;

  const show =
    viewMode === "elevation" &&
    !introActive &&
    lyricLines.length > 0 &&
    progress > 0.004;

  stack.classList.toggle("is-visible", show);

  // Lag behind scroll so lines don't race past
  const target = clamp(progress, 0, 1);
  const lag = target >= smoothLyricProgress ? 0.035 : 0.07;
  smoothLyricProgress += (target - smoothLyricProgress) * lag;

  if (!show) {
    if (lastLyricKey !== "") clearLyricBubbles();
    if (!introActive && progress <= 0.004) smoothLyricProgress = 0;
    return;
  }

  const n = lyricLines.length;
  const { index } = lyricWindowAtProgress(smoothLyricProgress, n);
  const line = (lyricLines[index] || "").trim();
  if (!line) return;

  const key = `${index}|${line}`;
  if (key === lastLyricKey) return;
  lastLyricKey = key;

  const bubble = ensureLyricBubble(index);
  if (!bubble) return;
  bubble.classList.remove("is-typing");
  bubble.textContent = line;
}

function trackSampleAtProgress(progress) {
  const track = data?.gpx?.track;
  if (!track?.length) return null;
  const u = clamp(progress, 0, 1);
  const idx = u * (track.length - 1);
  const i0 = Math.floor(idx);
  const i1 = Math.min(track.length - 1, i0 + 1);
  const f = idx - i0;
  const a = track[i0];
  const b = track[i1];
  return {
    t: a.t * (1 - f) + b.t * f,
    ele:
      a.ele != null && b.ele != null
        ? a.ele * (1 - f) + b.ele * f
        : a.ele ?? b.ele ?? null,
    lat: a.lat * (1 - f) + b.lat * f,
    lon: a.lon * (1 - f) + b.lon * f,
  };
}

function formatCoord(value, posHem, negHem, digits = 5) {
  if (value == null || !Number.isFinite(value)) return "";
  const hem = value >= 0 ? posHem : negHem;
  return `${Math.abs(value).toFixed(digits)}°${hem}`;
}

function haversineM(lat1, lon1, lat2, lon2) {
  const R = 6371000;
  const φ1 = (lat1 * Math.PI) / 180;
  const φ2 = (lat2 * Math.PI) / 180;
  const dφ = ((lat2 - lat1) * Math.PI) / 180;
  const dλ = ((lon2 - lon1) * Math.PI) / 180;
  const a =
    Math.sin(dφ / 2) ** 2 +
    Math.cos(φ1) * Math.cos(φ2) * Math.sin(dλ / 2) ** 2;
  return 2 * R * Math.asin(Math.min(1, Math.sqrt(a)));
}

function buildTrackDistances(track) {
  if (!track?.length) return [];
  const dist = new Float64Array(track.length);
  dist[0] = 0;
  for (let i = 1; i < track.length; i++) {
    const a = track[i - 1];
    const b = track[i];
    const flat = haversineM(a.lat, a.lon, b.lat, b.lon);
    const dEle =
      a.ele != null && b.ele != null ? b.ele - a.ele : 0;
    dist[i] = dist[i - 1] + Math.hypot(flat, dEle);
  }
  return dist;
}

function distanceAtProgress(progress) {
  if (!trackDistances.length) return 0;
  const u = clamp(progress, 0, 1);
  const idx = u * (trackDistances.length - 1);
  const i0 = Math.floor(idx);
  const i1 = Math.min(trackDistances.length - 1, i0 + 1);
  const f = idx - i0;
  return trackDistances[i0] * (1 - f) + trackDistances[i1] * f;
}

function stepsAtProgress(progress) {
  return Math.max(0, Math.round(distanceAtProgress(progress) / STEP_STRIDE_M));
}

function updateCornerMeta(progress, activeItem) {
  let ts = null;
  let ele = null;
  let lat = null;
  let lon = null;

  if (
    activeItem &&
    !activeItem.beyond &&
    activeItem.ts != null &&
    Math.abs(timeTForItem(activeItem) - progress) < TIME_WINDOW * 1.8
  ) {
    ts = activeItem.ts;
    ele = activeItem.ele;
    lat = activeItem.lat;
    lon = activeItem.lon;
  } else {
    const sample = trackSampleAtProgress(progress);
    if (sample) {
      ts = sample.t;
      ele = sample.ele;
      lat = sample.lat;
      lon = sample.lon;
    }
  }

  const timeVal = ts != null ? fmtMetaTime.format(new Date(ts * 1000)) : "";
  const eleVal = ele != null ? `${Math.round(ele)} m` : "";
  const latVal = formatCoord(lat, "N", "S");
  const lonVal = formatCoord(lon, "E", "W");
  const locVal =
    latVal && lonVal ? `${latVal}  ${lonVal}` : latVal || lonVal || "";
  const stepsVal = stepsAtProgress(progress).toLocaleString();

  if (els.metaTime) {
    els.metaTime.textContent = metaLabelsVisible
      ? timeVal
        ? `TIME ${timeVal}`
        : "TIME"
      : timeVal || "—";
  }
  if (els.metaAltitude) {
    els.metaAltitude.textContent = metaLabelsVisible
      ? eleVal
        ? `ELEVATION ${eleVal}`
        : "ELEVATION"
      : eleVal || "—";
  }
  if (els.metaLocation) {
    els.metaLocation.textContent = metaLabelsVisible
      ? latVal && lonVal
        ? `LAT ${latVal}  LON ${lonVal}`
        : "LAT LON"
      : locVal || "—";
  }
  if (els.metaSteps) {
    els.metaSteps.textContent = `${stepsVal} STEPS`;
  }
}

function updateJourney(progress, clockSec = 0) {
  if (viewMode !== "elevation") return;
  if (!trackCurve || !camera) return;
  if (selfieGroup) selfieGroup.visible = false;
  if (inspectHold.active) {
    updateInspectFrame();
    return;
  }

  const u = clamp(progress, 0, 0.999);
  const pos = trackCurve.getPointAt(u);
  const tangent = trackCurve.getTangentAt(u).normalize();
  _side.crossVectors(tangent, _up);
  if (_side.lengthSq() < 1e-6) _side.set(1, 0, 0);
  else _side.normalize();

  // Default: ride beside the path, looking ahead
  _camPos
    .copy(pos)
    .addScaledVector(_side, 95)
    .addScaledVector(_up, 55)
    .addScaledVector(tangent, -55);
  _look.copy(pos).addScaledVector(tangent, 70).addScaledVector(_up, 18);

  // When a capture plane is near, drift toward viewing it from its capture side
  let best = null;
  let bestD = Infinity;
  for (const g of interactives) {
    const d = Math.abs(g.userData.timeT - progress);
    if (d < bestD) {
      bestD = d;
      best = g;
    }
  }

  const activeItem = best?.userData?.item;
  const activeCaption = captionForItem(activeItem);
  updateCornerMeta(progress, activeItem);

  let focusEase = 0;
  if (best && bestD < TIME_WINDOW * 1.8) {
    const blend = clamp(1 - bestD / (TIME_WINDOW * 1.8), 0, 1);
    focusEase = blend * blend * (3 - 2 * blend);
    const heading = headingForItem(best.userData.item);
    const θ = THREE.MathUtils.degToRad(heading);
    // Stand on the capture axis, looking straight at the plane centre
    const face = _tmp.set(Math.sin(θ), 0, -Math.cos(θ)).normalize();
    const planeCenter = best.position.clone().addScaledVector(_up, 18);
    const viewFrom = planeCenter.clone().addScaledVector(face, -52);
    _camPos.lerp(viewFrom, focusEase * 0.95);
    _look.lerp(planeCenter, focusEase * 0.98);
  }

  camera.position.lerp(_camPos, 0.12);
  camera.lookAt(_look);

  let closeSum = 0;
  let closeW = 0;
  for (const g of interactives) {
    const d = Math.abs(g.userData.timeT - progress);
    const amount = Math.exp((-d * d) / (2 * TIME_WINDOW * TIME_WINDOW));
    setGroupPresence(g, amount);
    const sound = soundEnergyForMarker(g, progress, clockSec) * amount;
    applySoundMotion(g, sound, clockSec);
    if (amount > 0.04) {
      closeSum += (g.userData.closeness ?? 0.35) * amount;
      closeW += amount;
    }
  }

  // Keep the focused card page-centred and facing the viewer
  if (best && focusEase > 0.02) {
    const facing = best.userData.facing;
    if (facing) {
      const px = best.position.x;
      const pz = best.position.z;
      const dx = camera.position.x - px;
      const dz = camera.position.z - pz;
      if (dx * dx + dz * dz > 1e-6) {
        const billboardYaw = Math.atan2(dx, dz);
        const heading = headingForItem(best.userData.item);
        const θ = THREE.MathUtils.degToRad(heading);
        const captureYaw = Math.atan2(Math.sin(θ), -Math.cos(θ));
        facing.rotation.y = lerp(captureYaw, billboardYaw, focusEase);
      }
    }
  }

  syncSoundPlayback(progress);
  applyJourneyAtmosphere(progress);
  updateJourneyLyric(progress);

  const targetClose = closeW > 0 ? closeSum / closeW : smoothCloseness;
  // Snappier follow so weight tracks the scroll, not a slow average
  smoothCloseness += (targetClose - smoothCloseness) * 0.22;
  setBrandWeightFromCloseness(smoothCloseness, activeCaption);
}

function initScene() {
  const w = els.viewport.clientWidth;
  const h = els.viewport.clientHeight;

  renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.setSize(w, h);
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  els.viewport.appendChild(renderer.domElement);

  scene = new THREE.Scene();
  scene.background = new THREE.Color(0xffffff);
  scene.fog = new THREE.Fog(0xffffff, 500, 3200);

  camera = new THREE.PerspectiveCamera(42, w / h, 0.1, 20000);

  scene.add(new THREE.AmbientLight(0xffffff, 0.9));
  const sun = new THREE.DirectionalLight(0xffffff, 0.75);
  sun.position.set(400, 800, 200);
  scene.add(sun);
  const fill = new THREE.DirectionalLight(0xffffff, 0.3);
  fill.position.set(-300, 200, -400);
  scene.add(fill);

  setBrandWeightFromCloseness(smoothCloseness, titleText);
}

async function buildWorld() {
  const gpx = data.gpx;
  const eles = gpx.track.map((p) => p.ele).filter((e) => e != null);
  eleMin = Math.min(...eles);
  eleMax = Math.max(...eles);
  altitudeTemplate = buildAltitudeTemplate(gpx.track, 64);
  const { project } = toLocalFrame(gpx.track);
  trackPoints = gpx.track.map((p) => project(p.lat, p.lon, p.ele));
  trackDistances = buildTrackDistances(gpx.track);

  const built = makeTrackMesh(trackPoints);
  trackMesh = built.mesh;
  trackCurve = built.curve;
  scene.add(trackMesh);

  // Resolve SELFIES first so blank / non-human frames never enter the rolodex
  const selfieSamples = await resolveSelfieMedia(data.media, gpx);
  const selfiePaths = new Set(selfieSamples.map((m) => m.path));

  const samples = sampleMedia(
    data.media.filter((m) => !selfiePaths.has(m.path)),
    gpx
  );
  interactives = [];
  await Promise.all(
    samples.map(async (item) => {
      const pos = positionForItem(item, project, trackPoints, trackCurve);
      const marker = await makeMediaMarker(item, pos);
      scene.add(marker);
      interactives.push(marker);
    })
  );

  interactives.sort((a, b) => a.userData.timeT - b.userData.timeT);
  calibrateClosenessExtent(interactives);

  selfieInteractives = [];
  await Promise.all(
    selfieSamples.map(async (item) => {
      const pos = positionForItem(item, project, trackPoints, trackCurve);
      const marker = await makeMediaMarker(item, pos);
      if (!(marker.userData.planes || []).length) {
        marker.traverse((obj) => disposeObject3D(obj));
        return;
      }
      marker.visible = false;
      setGroupPresence(marker, 0);
      scene.add(marker);
      selfieInteractives.push(marker);
    })
  );
  selfieInteractives.sort((a, b) => a.userData.timeT - b.userData.timeT);

  journeyColors = buildJourneyColorField(
    interactives.filter((g) => !g.userData.item?.beyond)
  );
  if (journeyColors.length) {
    smoothJourneyColor = { ...sampleJourneyColor(journeyColors, 0) };
  }

  // Sound envelopes for motion (non-blocking if a clip fails)
  await loadSoundClips(data.media);

  beginAtTimelineStart();
  updateModeToggle();
}

function computeOverviewBounds() {
  const box = new THREE.Box3();
  for (const p of trackPoints) box.expandByPoint(p);
  for (const g of interactives) {
    const home = g.userData.hikePos || g.position;
    box.expandByPoint(home);
  }
  if (box.isEmpty()) {
    overviewCenter.set(0, 80, 0);
    overviewRadius = 400;
    return;
  }
  box.getCenter(overviewCenter);
  const size = box.getSize(_tmp);
  overviewRadius = Math.max(size.length() * 0.42, 180);
}

/** Slow orbit of the full path + media constellation before the hike begins. */
function updateOverview(clockSec) {
  if (!camera) return;
  if (selfieGroup) selfieGroup.visible = false;

  if (scene?.fog) {
    scene.fog.near = overviewRadius * 0.9;
    scene.fog.far = overviewRadius * 4.2;
  }

  const angle = clockSec * 0.11;
  const elev = 0.4;
  const r = overviewRadius * 1.45;
  const cosE = Math.cos(elev);
  _camPos.set(
    overviewCenter.x + Math.cos(angle) * r * cosE,
    overviewCenter.y + r * Math.sin(elev) + overviewRadius * 0.1,
    overviewCenter.z + Math.sin(angle) * r * cosE
  );
  _look.copy(overviewCenter).addScaledVector(_up, overviewRadius * 0.06);

  camera.position.lerp(_camPos, 0.045);
  camera.lookAt(_look);

  for (const g of interactives) {
    const home = g.userData.hikePos;
    if (home) g.position.copy(home);
    setStemVisible(g, true);
    setGroupPresence(g, 0.48);
    applySoundMotion(g, 0, clockSec);
  }
  if (trackMesh) trackMesh.visible = true;

  updateCornerMeta(0, null);
  applyJourneyAtmosphere(0.45);
  setBrandWeightFromCloseness(0.35, TITLE_FALLBACK);
}

function restoreJourneyFog() {
  if (!scene?.fog) return;
  scene.fog.near = 500;
  scene.fog.far = 3200;
}

function endIntro({ keepHint = false } = {}) {
  if (!introActive) return;
  introActive = false;
  metaLabelsVisible = false;
  restoreJourneyFog();
  setAllMarkersVisualMode("layers");
  if (!keepHint) hideHint();
}

/** Open in overview orbit — scroll ends the intro and starts the journey. */
function beginAtTimelineStart() {
  if ("scrollRestoration" in history) {
    history.scrollRestoration = "manual";
  }
  window.scrollTo(0, 0);
  scrollProgress = 0;
  smoothProgress = 0;
  smoothLyricProgress = 0;
  clearLyricBubbles();
  introActive = true;
  metaLabelsVisible = true;
  titleText = TITLE_FALLBACK;
  computeOverviewBounds();
  setAllMarkersVisualMode("flat");

  const clockSec = performance.now() * 0.001;
  updateOverview(clockSec);
  if (camera) {
    camera.position.copy(_camPos);
    camera.lookAt(_look);
  }
  setBrandWeightFromCloseness(0.35, titleText);

  if (els.scrollHint) {
    els.scrollHint.textContent = "SCROLL TO BEGIN THE PASSAGE";
    els.scrollHint.classList.remove("is-gone");
    hintHidden = false;
  }

  // Re-assert after layout (fonts / scroll-rail height) settles
  requestAnimationFrame(() => {
    window.scrollTo(0, 0);
    scrollProgress = 0;
    smoothProgress = 0;
  });
}

function animate() {
  frameId = requestAnimationFrame(animate);
  const clockSec = performance.now() * 0.001;
  if (viewMode === "timeline") {
    updateTimeline(clockSec);
  } else if (viewMode === "tunnel") {
    updateTunnel();
  } else if (inspectHold.active) {
    if (introActive) {
      updateOverview(clockSec);
    } else {
      // Keep camera on the trail while the held photo centers itself
      smoothProgress += (scrollProgress - smoothProgress) * 0.085;
      const u = clamp(smoothProgress, 0, 0.999);
      if (trackCurve) {
        const pos = trackCurve.getPointAt(u);
        const tangent = trackCurve.getTangentAt(u).normalize();
        _side.crossVectors(tangent, _up);
        if (_side.lengthSq() < 1e-6) _side.set(1, 0, 0);
        else _side.normalize();
        _camPos.copy(pos).addScaledVector(_side, 95).addScaledVector(_up, 55);
        _look.copy(pos).addScaledVector(tangent, 90).addScaledVector(_up, 18);
        camera.position.lerp(_camPos, 0.12);
        camera.lookAt(_look);
      }
    }
    updateInspectFrame();
  } else if (introActive) {
    updateOverview(clockSec);
    updateJourneyLyric(0);
  } else {
    smoothProgress += (scrollProgress - smoothProgress) * 0.085;
    updateJourney(smoothProgress, clockSec);
  }
  renderer.render(scene, camera);
}

function onResize() {
  if (!renderer || !camera) return;
  const w = els.viewport.clientWidth;
  const h = els.viewport.clientHeight;
  camera.aspect = w / h;
  camera.updateProjectionMatrix();
  renderer.setSize(w, h);
}

function onScroll() {
  if (viewMode === "tunnel") {
    tunnelProgress = readScrollProgress();
    if (tunnelProgress > 0.01) hideHint();
    ensureAudioCtx();
    return;
  }
  if (viewMode !== "elevation") return;
  scrollProgress = readScrollProgress();
  if (introActive && scrollProgress > 0.004) {
    endIntro();
  }
  if (scrollProgress > 0.01) {
    hideHint();
    if (metaLabelsVisible) metaLabelsVisible = false;
  }
  ensureAudioCtx();
}

function bindModeControls() {
  els.modeToggle?.addEventListener("click", () => {
    ensureAudioCtx();
    toggleViewMode();
  });
  els.viewport?.addEventListener("pointermove", onTimelinePointer, {
    passive: true,
  });
  els.viewport?.addEventListener("wheel", onViewportWheel, { passive: false });
  els.viewport?.addEventListener("pointerdown", onInspectPointerDown);
  window.addEventListener("pointerup", onInspectPointerUp);
  window.addEventListener("pointercancel", onInspectPointerUp);
  window.addEventListener("blur", endInspect);
}

async function boot() {
  if ("scrollRestoration" in history) {
    history.scrollRestoration = "manual";
  }
  window.scrollTo(0, 0);

  const res = await fetch("data/timeline.json");
  if (!res.ok) {
    if (els.scrollHint) els.scrollHint.textContent = "Missing trail data";
    return;
  }
  data = await res.json();

  try {
    const capRes = await fetch("data/captions.json");
    if (capRes.ok) captionsById = await capRes.json();
  } catch {
    captionsById = {};
  }

  lyricLines = await loadLyricLines();

  await loadBrandFonts();
  initScene();
  await buildWorld();
  bindModeControls();
  animate();
  window.addEventListener("resize", onResize);
  window.addEventListener("scroll", onScroll, { passive: true });
}

boot().catch((err) => {
  console.error(err);
  if (els.scrollHint) els.scrollHint.textContent = "Could not load";
});
