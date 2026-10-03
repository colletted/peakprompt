import * as THREE from "three";

const els = {
  viewport: document.getElementById("viewport"),
  scrollRail: document.getElementById("scroll-rail"),
  scrollHint: document.getElementById("scroll-hint"),
  pageTitle: document.getElementById("page-title"),
};

const BRAND_WEIGHTS = [300, 400, 500, 700, 800, 900];
const TITLE_FALLBACK = "quiet winding trail";

const VERTICAL_EXAGGERATION = 1.8;
const MEDIA_SAMPLE = 72;
const TIME_WINDOW = 0.07;
const AUDIO_TIME_SIGMA = 100; // seconds — images near a recording
const AUDIO_SCROLL_SIGMA = 0.04;

let data = null;
let renderer, scene, camera;
let interactives = [];
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
let audioCtx = null;
let audioUnlocked = false;
let lastTitleKey = "";
let titleText = TITLE_FALLBACK;
let captionsById = {};

const thresholdResponse = 0.8;
const layerResponse = 0.8;
let altitudeTemplate = null;
let eleMin = 2100;
let eleMax = 2700;

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

function sampleMedia(media, gpx) {
  const onTrack = media.filter(
    (m) => m.onTrack && (m.kind === "image" || m.kind === "video") && m.thumb
  );
  const picks = [];
  if (onTrack.length) {
    const n = Math.min(MEDIA_SAMPLE, onTrack.length);
    for (let i = 0; i < n; i++) {
      const idx = Math.round((i / Math.max(n - 1, 1)) * (onTrack.length - 1));
      picks.push(onTrack[idx]);
    }
  }
  const seen = new Set();
  const unique = [];
  for (const m of picks) {
    if (seen.has(m.path)) continue;
    seen.add(m.path);
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

function makeTrackMesh(points) {
  const curve = new THREE.CatmullRomCurve3(points, false, "catmullrom", 0.15);
  const segs = Math.max(points.length * 2, 64);
  const sampled = curve.getPoints(segs);
  const geo = new THREE.BufferGeometry().setFromPoints(sampled);
  const mat = new THREE.LineBasicMaterial({
    color: 0x9a9a9a,
    linewidth: 1, // most platforms ignore >1; keep as a hairline stroke
  });
  const line = new THREE.Line(geo, mat);
  line.frustumCulled = false;
  return { mesh: line, curve };
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
  const entry = {
    width: w,
    height: h,
    gray,
    stretched,
    meanLum,
    cutA,
    cutB,
    palette,
    keyColor: palette.mid,
    closeness: estimateCloseness(gray, w, h),
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
  const phrase =
    captionsById[item.id] || captionsById[item.name] || TITLE_FALLBACK;
  return String(phrase).toLowerCase();
}

/** Update accessible title: fixed scale, exclusion blend, variable weight. */
function setBrandWeightFromCloseness(closeness, text = titleText) {
  const el = els.pageTitle;
  if (!el) return;
  const dramatized = dramaticCloseness(closeness);
  const idx = Math.round(dramatized * (BRAND_WEIGHTS.length - 1));
  const weight = BRAND_WEIGHTS[clamp(idx, 0, BRAND_WEIGHTS.length - 1)];
  const phrase = (text || TITLE_FALLBACK).trim() || TITLE_FALLBACK;
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
    if (!obj.isMesh || !obj.material) return;
    const mats = Array.isArray(obj.material) ? obj.material : [obj.material];
    mats.forEach((m) => {
      m.transparent = true;
      m.opacity = a;
      m.depthWrite = a > 0.55;
    });
  });
}

async function rebuildMarkerVisuals(group) {
  const item = group.userData.item;
  if (!item) return;

  clearMarkerVisuals(group);

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
  try {
    const gray = await getGrayBuffer(url);
    closeness = gray.closeness ?? 0.35;
    keyColor = gray.keyColor || keyColor;
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
      plane.scale.set(layout.scale, layout.scale, 1);
      facing.add(plane);
      planes.push(plane);
    });
  } catch {
    // leave empty if silhouette fails
  }

  group.userData.planes = planes;
  group.userData.timeT = timeNorm(item);
  group.userData.closeness = closeness;
  group.userData.keyColor = keyColor;
}

async function makeMediaMarker(item, position) {
  const group = new THREE.Group();
  group.position.copy(position);
  group.userData = { item, timeT: timeNorm(item) };

  const pin = new THREE.Mesh(
    new THREE.CylinderGeometry(0.55, 0.55, 12, 8),
    new THREE.MeshStandardMaterial({
      color: 0xb0b0b0,
      transparent: true,
    })
  );
  pin.position.y = 6;
  pin.userData.keep = true;
  group.add(pin);

  await rebuildMarkerVisuals(group);
  return group;
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

function updateJourney(progress, clockSec = 0) {
  if (!trackCurve || !camera) return;

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

  const activeCaption = captionForItem(best?.userData?.item);

  if (best && bestD < TIME_WINDOW * 1.8) {
    const blend = clamp(1 - bestD / (TIME_WINDOW * 1.8), 0, 1);
    const ease = blend * blend * (3 - 2 * blend);
    const heading = headingForItem(best.userData.item);
    const θ = THREE.MathUtils.degToRad(heading);
    // Stand where the photographer stood: behind the plane along -look
    const face = _tmp.set(Math.sin(θ), 0, -Math.cos(θ));
    const planeCenter = best.position.clone().addScaledVector(_up, 18);
    const viewFrom = planeCenter
      .clone()
      .addScaledVector(face, -48)
      .addScaledVector(_up, 10);
    _camPos.lerp(viewFrom, ease * 0.85);
    _look.lerp(planeCenter.clone().addScaledVector(face, 12), ease * 0.9);
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

  syncSoundPlayback(progress);
  applyJourneyAtmosphere(progress);

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

  const built = makeTrackMesh(trackPoints);
  trackMesh = built.mesh;
  trackCurve = built.curve;
  scene.add(trackMesh);

  const samples = sampleMedia(data.media, gpx);
  interactives = [];
  await Promise.all(
    samples.map(async (item) => {
      const pos = project(item.lat, item.lon, item.ele);
      const marker = await makeMediaMarker(item, pos);
      scene.add(marker);
      interactives.push(marker);
    })
  );

  interactives.sort((a, b) => a.userData.timeT - b.userData.timeT);
  calibrateClosenessExtent(interactives);

  journeyColors = buildJourneyColorField(interactives);
  if (journeyColors.length) {
    smoothJourneyColor = { ...sampleJourneyColor(journeyColors, 0) };
  }

  // Sound envelopes for motion (non-blocking if a clip fails)
  await loadSoundClips(data.media);

  beginAtTimelineStart();
}

/** Always open at the trailhead — ignore restored scroll position. */
function beginAtTimelineStart() {
  if ("scrollRestoration" in history) {
    history.scrollRestoration = "manual";
  }
  window.scrollTo(0, 0);
  scrollProgress = 0;
  smoothProgress = 0;
  const startItem = interactives[0]?.userData?.item;
  titleText = captionForItem(startItem);
  updateJourney(0, performance.now() * 0.001);
  if (camera) {
    camera.position.copy(_camPos);
    camera.lookAt(_look);
  }
  setBrandWeightFromCloseness(smoothCloseness, titleText);
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
  smoothProgress += (scrollProgress - smoothProgress) * 0.085;
  updateJourney(smoothProgress, clockSec);
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
  scrollProgress = readScrollProgress();
  if (scrollProgress > 0.01) hideHint();
  ensureAudioCtx();
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

  await loadBrandFonts();
  initScene();
  await buildWorld();
  animate();
  window.addEventListener("resize", onResize);
  window.addEventListener("scroll", onScroll, { passive: true });
}

boot().catch((err) => {
  console.error(err);
  if (els.scrollHint) els.scrollHint.textContent = "Could not load";
});
