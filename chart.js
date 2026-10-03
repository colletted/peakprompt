const els = {
  trailName: document.getElementById("trail-name"),
  trailMeta: document.getElementById("trail-meta"),
  canvas: document.getElementById("chart"),
  axisX: document.getElementById("axis-x"),
  axisY: document.getElementById("axis-y"),
  labelX: document.getElementById("label-x"),
  labelY: document.getElementById("label-y"),
  hud: document.getElementById("hud"),
  hudTitle: document.getElementById("hud-title"),
  hudMeta: document.getElementById("hud-meta"),
  hudOpen: document.getElementById("hud-open"),
  lightbox: document.getElementById("lightbox"),
  lightboxMedia: document.getElementById("lightbox-media"),
  lightboxCaption: document.getElementById("lightbox-caption"),
  lightboxClose: document.getElementById("lightbox-close"),
};

const fmtFull = new Intl.DateTimeFormat(undefined, {
  dateStyle: "medium",
  timeStyle: "short",
});

const fmtTime = new Intl.DateTimeFormat(undefined, {
  hour: "2-digit",
  minute: "2-digit",
  hour12: false,
});

const AXIS_LABELS = {
  time: "Time",
  ele: "Altitude",
  lat: "Latitude",
  lon: "Longitude",
  progress: "Track progress",
};

let data = null;
let points = []; // plotted media + track samples
let trackSeries = [];
let selected = null;

/** View transform in data space → screen via pan/zoom (not altitude-path scrolling). */
const view = {
  scale: 1,
  // Camera center in normalized 0..1 data space
  cx: 0.5,
  cy: 0.5,
};

const pad = { top: 110, right: 48, bottom: 64, left: 72 };
let dragging = null;
let hoverIndex = -1;

const thumbCache = new Map();

function clamp(v, a, b) {
  return Math.min(b, Math.max(a, v));
}

function valueFor(axis, item, gpx) {
  if (axis === "time") return item.ts;
  if (axis === "ele") return item.ele;
  if (axis === "lat") return item.lat;
  if (axis === "lon") return item.lon;
  if (axis === "progress") {
    const span = Math.max(gpx.endTs - gpx.startTs, 1);
    return (item.ts - gpx.startTs) / span;
  }
  return 0;
}

function boundsFor(axis, items, track) {
  const vals = [];
  for (const it of items) {
    const v = valueFor(axis, it, data.gpx);
    if (v != null && Number.isFinite(v)) vals.push(v);
  }
  for (const p of track) {
    const v = valueFor(axis, p, data.gpx);
    if (v != null && Number.isFinite(v)) vals.push(v);
  }
  let min = Math.min(...vals);
  let max = Math.max(...vals);
  if (min === max) {
    min -= 1;
    max += 1;
  }
  // Small padding in data space
  const padAmt = (max - min) * 0.06;
  return { min: min - padAmt, max: max + padAmt };
}

function buildDataset() {
  const gpx = data.gpx;
  const media = data.media.filter(
    (m) =>
      m.onTrack &&
      m.kind !== "audio" &&
      m.ele != null &&
      m.lat != null &&
      m.lon != null &&
      (m.thumb || m.kind === "image")
  );

  // Decimate for readability while keeping spread across the hike
  const maxPins = 160;
  const sampled = [];
  if (media.length <= maxPins) {
    sampled.push(...media);
  } else {
    for (let i = 0; i < maxPins; i++) {
      sampled.push(media[Math.round((i / (maxPins - 1)) * (media.length - 1))]);
    }
  }

  trackSeries = gpx.track.map((p) => ({
    ts: p.t,
    ele: p.ele,
    lat: p.lat,
    lon: p.lon,
    kind: "track",
  }));

  points = sampled.map((m) => ({
    ...m,
    kind: "media",
  }));

  return { mediaCount: sampled.length };
}

function dataToScreen(nx, ny, w, h) {
  // nx, ny in 0..1 normalized data space
  const plotW = w - pad.left - pad.right;
  const plotH = h - pad.top - pad.bottom;
  const x = pad.left + (0.5 + (nx - view.cx) * view.scale) * plotW;
  const y = pad.top + (0.5 - (ny - view.cy) * view.scale) * plotH;
  return { x, y };
}

function screenToData(sx, sy, w, h) {
  const plotW = w - pad.left - pad.right;
  const plotH = h - pad.top - pad.bottom;
  const nx = view.cx + (sx - pad.left) / plotW / view.scale - 0.5 / view.scale;
  const ny = view.cy - ((sy - pad.top) / plotH / view.scale - 0.5 / view.scale);
  return { nx, ny };
}

function normalize(v, b) {
  return (v - b.min) / (b.max - b.min);
}

function denormalize(n, b) {
  return b.min + n * (b.max - b.min);
}

function formatTick(axis, v) {
  if (axis === "time") return fmtTime.format(new Date(v * 1000));
  if (axis === "ele") return `${Math.round(v)} m`;
  if (axis === "progress") return `${Math.round(v * 100)}%`;
  if (axis === "lat" || axis === "lon") return v.toFixed(3);
  return String(Math.round(v * 100) / 100);
}

function loadThumb(url) {
  const existing = thumbCache.get(url);
  if (existing instanceof HTMLImageElement) return Promise.resolve(existing);
  if (existing instanceof Promise) return existing;
  const img = new Image();
  img.decoding = "async";
  const p = new Promise((resolve) => {
    img.onload = () => {
      thumbCache.set(url, img);
      resolve(img);
    };
    img.onerror = () => {
      thumbCache.delete(url);
      resolve(null);
    };
    img.src = url;
  });
  thumbCache.set(url, p);
  return p;
}

function draw() {
  const canvas = els.canvas;
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const w = canvas.clientWidth;
  const h = canvas.clientHeight;
  canvas.width = Math.floor(w * dpr);
  canvas.height = Math.floor(h * dpr);
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, w, h);
  ctx.fillStyle = "#f4f4f4";
  ctx.fillRect(0, 0, w, h);

  if (!data) return;

  const axisX = els.axisX.value;
  const axisY = els.axisY.value;
  const bx = boundsFor(axisX, points, trackSeries);
  const by = boundsFor(axisY, points, trackSeries);

  const plotW = w - pad.left - pad.right;
  const plotH = h - pad.top - pad.bottom;

  // Plot background
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(pad.left, pad.top, plotW, plotH);
  ctx.strokeStyle = "#d0d0d0";
  ctx.strokeRect(pad.left + 0.5, pad.top + 0.5, plotW - 1, plotH - 1);

  // Clip to plot
  ctx.save();
  ctx.beginPath();
  ctx.rect(pad.left, pad.top, plotW, plotH);
  ctx.clip();

  // Grid + cross axes at mid of visible data (classic XY cross chart)
  const mid = dataToScreen(0.5, 0.5, w, h);
  ctx.strokeStyle = "#ececec";
  ctx.lineWidth = 1;
  for (let i = 1; i < 8; i++) {
    const gx = pad.left + (plotW * i) / 8;
    const gy = pad.top + (plotH * i) / 8;
    ctx.beginPath();
    ctx.moveTo(gx, pad.top);
    ctx.lineTo(gx, pad.top + plotH);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(pad.left, gy);
    ctx.lineTo(pad.left + plotW, gy);
    ctx.stroke();
  }

  // Bold cross through chart center
  ctx.strokeStyle = "#111111";
  ctx.lineWidth = 1.25;
  ctx.beginPath();
  ctx.moveTo(pad.left, mid.y);
  ctx.lineTo(pad.left + plotW, mid.y);
  ctx.moveTo(mid.x, pad.top);
  ctx.lineTo(mid.x, pad.top + plotH);
  ctx.stroke();

  // GPX track polyline in XY space
  ctx.strokeStyle = "rgba(17,17,17,0.55)";
  ctx.lineWidth = 2;
  ctx.beginPath();
  let started = false;
  for (const p of trackSeries) {
    const vx = valueFor(axisX, p, data.gpx);
    const vy = valueFor(axisY, p, data.gpx);
    if (vx == null || vy == null) continue;
    const s = dataToScreen(normalize(vx, bx), normalize(vy, by), w, h);
    if (!started) {
      ctx.moveTo(s.x, s.y);
      started = true;
    } else {
      ctx.lineTo(s.x, s.y);
    }
  }
  ctx.stroke();

  // Media points
  points.forEach((item, index) => {
    const vx = valueFor(axisX, item, data.gpx);
    const vy = valueFor(axisY, item, data.gpx);
    if (vx == null || vy == null) return;
    const s = dataToScreen(normalize(vx, bx), normalize(vy, by), w, h);
    const size = index === hoverIndex || selected?.path === item.path ? 34 : 22;
    const thumbUrl = item.thumb || item.path;
    const cached = thumbCache.get(thumbUrl);

    if (cached instanceof HTMLImageElement && cached.complete) {
      ctx.save();
      ctx.beginPath();
      ctx.rect(s.x - size / 2, s.y - size / 2, size, size);
      ctx.clip();
      ctx.drawImage(cached, s.x - size / 2, s.y - size / 2, size, size);
      ctx.restore();
      ctx.strokeStyle = index === hoverIndex ? "#111" : "rgba(17,17,17,0.55)";
      ctx.lineWidth = index === hoverIndex ? 1.5 : 1;
      ctx.strokeRect(s.x - size / 2 + 0.5, s.y - size / 2 + 0.5, size - 1, size - 1);
    } else {
      if (!(cached instanceof Promise)) loadThumb(thumbUrl).then(() => requestDraw());
      ctx.fillStyle = "#111";
      ctx.beginPath();
      ctx.arc(s.x, s.y, 2.5, 0, Math.PI * 2);
      ctx.fill();
    }

    item._sx = s.x;
    item._sy = s.y;
    item._size = size;
  });

  ctx.restore();

  // Axis ticks outside clip
  ctx.fillStyle = "#6a6a6a";
  ctx.font = "11px Helvetica Neue, Helvetica, Arial, sans-serif";
  ctx.textAlign = "center";
  ctx.textBaseline = "top";
  for (let i = 0; i <= 4; i++) {
    const n = i / 4;
    // ticks along visible bottom corresponding to data under current view
    const sx = pad.left + n * plotW;
    const dataPt = screenToData(sx, pad.top + plotH / 2, w, h);
    const xv = denormalize(clamp(dataPt.nx, 0, 1), bx);
    ctx.fillText(formatTick(axisX, xv), sx, pad.top + plotH + 10);
  }
  ctx.textAlign = "right";
  ctx.textBaseline = "middle";
  for (let i = 0; i <= 4; i++) {
    const n = i / 4;
    const sy = pad.top + (1 - n) * plotH;
    const dataPt = screenToData(pad.left + plotW / 2, sy, w, h);
    const yv = denormalize(clamp(dataPt.ny, 0, 1), by);
    ctx.fillText(formatTick(axisY, yv), pad.left - 10, sy);
  }
}

let raf = 0;
function requestDraw() {
  if (raf) return;
  raf = requestAnimationFrame(() => {
    raf = 0;
    draw();
  });
}

function hitTest(sx, sy) {
  let best = -1;
  let bestD = 18;
  points.forEach((item, i) => {
    if (item._sx == null) return;
    const d = Math.hypot(item._sx - sx, item._sy - sy);
    const r = (item._size || 22) * 0.65;
    if (d < r && d < bestD) {
      best = i;
      bestD = d;
    }
  });
  return best;
}

function openLightbox(item) {
  els.lightboxMedia.replaceChildren();
  if (item.kind === "video") {
    const video = document.createElement("video");
    video.src = item.path;
    video.controls = true;
    video.autoplay = true;
    els.lightboxMedia.appendChild(video);
  } else {
    const img = document.createElement("img");
    img.src = item.path;
    img.alt = item.name;
    els.lightboxMedia.appendChild(img);
  }
  const ele = item.ele != null ? ` · ${Math.round(item.ele)} m` : "";
  els.lightboxCaption.textContent = `${item.name} · ${item.source} · ${fmtFull.format(
    new Date(item.time)
  )}${ele}`;
  if (typeof els.lightbox.showModal === "function") els.lightbox.showModal();
}

function showHud(item) {
  selected = item;
  els.hud.hidden = false;
  els.hudTitle.textContent = item.name;
  els.hudMeta.textContent = `${item.source} · ${fmtFull.format(new Date(item.time))}\n${
    item.ele != null ? `${Math.round(item.ele)} m` : "—"
  } · ${item.lat?.toFixed(5)}, ${item.lon?.toFixed(5)}`;
  requestDraw();
}

function updateAxisLabels() {
  els.labelX.textContent = `${AXIS_LABELS[els.axisX.value]} →`;
  els.labelY.textContent = `↑ ${AXIS_LABELS[els.axisY.value]}`;
}

function onWheel(e) {
  e.preventDefault();
  const rect = els.canvas.getBoundingClientRect();
  const sx = e.clientX - rect.left;
  const sy = e.clientY - rect.top;
  const before = screenToData(sx, sy, rect.width, rect.height);
  const factor = e.deltaY < 0 ? 1.12 : 1 / 1.12;
  view.scale = clamp(view.scale * factor, 0.6, 18);
  const after = screenToData(sx, sy, rect.width, rect.height);
  // Keep point under cursor stable
  view.cx += before.nx - after.nx;
  view.cy += before.ny - after.ny;
  view.cx = clamp(view.cx, -0.2, 1.2);
  view.cy = clamp(view.cy, -0.2, 1.2);
  requestDraw();
}

function onPointerDown(e) {
  els.canvas.setPointerCapture(e.pointerId);
  dragging = {
    x: e.clientX,
    y: e.clientY,
    cx: view.cx,
    cy: view.cy,
    moved: false,
  };
}

function onPointerMove(e) {
  const rect = els.canvas.getBoundingClientRect();
  const sx = e.clientX - rect.left;
  const sy = e.clientY - rect.top;

  if (dragging) {
    const plotW = rect.width - pad.left - pad.right;
    const plotH = rect.height - pad.top - pad.bottom;
    const dx = e.clientX - dragging.x;
    const dy = e.clientY - dragging.y;
    if (Math.hypot(dx, dy) > 3) dragging.moved = true;
    view.cx = dragging.cx - dx / plotW / view.scale;
    view.cy = dragging.cy + dy / plotH / view.scale;
    requestDraw();
    return;
  }

  const idx = hitTest(sx, sy);
  if (idx !== hoverIndex) {
    hoverIndex = idx;
    els.canvas.style.cursor = idx >= 0 ? "pointer" : "grab";
    requestDraw();
  }
}

function onPointerUp(e) {
  if (!dragging) return;
  const wasDrag = dragging.moved;
  dragging = null;
  if (wasDrag) return;
  const rect = els.canvas.getBoundingClientRect();
  const idx = hitTest(e.clientX - rect.left, e.clientY - rect.top);
  if (idx >= 0) showHud(points[idx]);
}

async function boot() {
  const res = await fetch("data/timeline.json");
  if (!res.ok) {
    els.trailName.textContent = "Missing timeline data";
    return;
  }
  data = await res.json();
  const { mediaCount } = buildDataset();
  els.trailName.textContent = data.gpx.name.replace(/\s*-\s*Wikiloc\s*$/i, "");
  els.trailMeta.textContent = `X·Y cross chart · ${mediaCount} media · scroll zooms, drag pans`;
  updateAxisLabels();
  requestDraw();
  await Promise.all(points.map((p) => loadThumb(p.thumb || p.path)));
  requestDraw();
}

els.canvas.addEventListener("wheel", onWheel, { passive: false });
els.canvas.addEventListener("pointerdown", onPointerDown);
els.canvas.addEventListener("pointermove", onPointerMove);
els.canvas.addEventListener("pointerup", onPointerUp);
els.canvas.addEventListener("pointercancel", () => {
  dragging = null;
});

els.axisX.addEventListener("change", () => {
  view.scale = 1;
  view.cx = 0.5;
  view.cy = 0.5;
  updateAxisLabels();
  requestDraw();
});
els.axisY.addEventListener("change", () => {
  view.scale = 1;
  view.cx = 0.5;
  view.cy = 0.5;
  updateAxisLabels();
  requestDraw();
});

window.addEventListener("resize", requestDraw);

els.hudOpen.addEventListener("click", () => {
  if (selected) openLightbox(selected);
});
els.lightboxClose.addEventListener("click", () => els.lightbox.close());
els.lightbox.addEventListener("click", (e) => {
  if (e.target === els.lightbox) els.lightbox.close();
});

boot().catch((err) => {
  console.error(err);
  els.trailMeta.textContent = err.message;
});
