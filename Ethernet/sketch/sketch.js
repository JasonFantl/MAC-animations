// Classic Ethernet (CSMA/CD) bus simulation
// Three computers share a coaxial bus. Signals propagate bidirectionally.
// A computer detects a collision when it hears a foreign signal while transmitting.

const WIRE_Y       = 90;
const WIRE_L       = 60;
const WIRE_R       = 480;
const COMP_Y       = 50;

const SIGNAL_SPEED = 600;  // px/s
const TX_DURATION  = 1.2;  // s — must be ≥ round-trip (2×max_prop = 2×300/600 = 1.0s)
const BACKOFF_SLOT  = 0.4;  // s — base backoff quantum
const BACKOFF_MAX_N = 4;    // exponent cap: max window = 2^4 * BACKOFF_SLOT = 6.4s
const FLASH_DUR    = 0.4;  // s — red flash on collision detect
const DOT_R        = 4;    // signal dot radius
const DOT_SP       = 11;   // spacing between signal dots (px)

// Timeline
const TL_WIN   = 18;
const TL_Y     = 118;
const TL_ANN_H = 16;
const TL_ROW   = 28;
const TL_GAP   = 9;
const TL_LX    = 50;
const TL_W     = 460;


// B starts at 5.0, C at 5.1 (both within the 0.3s propagation window → collision)
// C detects B's signal at t=5.0+0.3=5.3 (after 0.2s of transmitting)
// B detects C's signal at t=5.1+0.3=5.4 (after 0.4s — before TX_DURATION=1.0s is up)
const MESSAGE_SCHEDULE = [
  { time: 1.0,  compId: 0 },  // A alone — succeeds
  { time: 4.5,  compId: 1 },  // B alone — succeeds
  { time: 8.0,  compId: 1 },  // B starts
  { time: 8.1,  compId: 2 },  // C starts 0.1s later → collision
  { time: 17,  compId: 2 },  // C starts 0.1s later → collision
  { time: 17.2,  compId: 1 },  // C starts 0.1s later → collision
  { time: 17.3,  compId: 0 },  // C starts 0.1s later → collision
];
const SCHEDULE_PERIOD = 40;

const ANNOTATIONS = [
  { label: 'Node A', start: 0.9, end: 3 },
  { label: 'Node B', start: 4.4, end: 6.5 },
  { label: 'B and C collide', start: 7.9, end: 12 },
  { label: 'All nodes collide', start: 16.9, end: 31 },
];

const RAND_SEED = 42;

// Computers: red (A, left), green (B, center), blue (C, right)
// Prop times: A-B = 150/600 = 0.25s, B-C = 150/600 = 0.25s, A-C = 300/600 = 0.5s
// Round-trip (A↔C) = 1.0s; TX_DURATION=1.2s satisfies Ethernet minimum frame constraint
const COMP_CFGS = [
  { x: 120, col: [195, 105, 170], label: 'A' },
  { x: 270, col: [145, 205,  40], label: 'B' },
  { x: 420, col: [ 40, 185, 185], label: 'C' },
];

let signals   = [];
let computers = [];
let compImg;
let globalTime, prevMillis;
let scheduleIdx, periodStart;


// ── Signal ──────────────────────────────────────────────────────────────────

class Signal {
  constructor(sourceId, tapX, t0, col) {
    this.sourceId  = sourceId;
    this.tapX      = tapX;
    this.startTime = t0;
    this.endTime   = null;
    this.ruined    = false;
    this.col       = col;
    this.yOff      = 0;
  }

  stop(t) { this.endTime = t; }

  // True if this signal is physically present at wire position x at time t
  isAt(x, t) {
    let d = abs(x - this.tapX);
    let arrive = this.startTime + d / SIGNAL_SPEED;
    if (t < arrive) return false;
    if (this.endTime === null) return true;
    return t < this.endTime + d / SIGNAL_SPEED;
  }

  // True once the signal has fully left the wire AND scrolled off the timeline
  isDone(t) {
    if (this.endTime === null) return false;
    let maxD = max(abs(WIRE_L - this.tapX), abs(WIRE_R - this.tapX));
    return t > this.endTime + maxD / SIGNAL_SPEED + TL_WIN + 2;
  }

  draw(t) {
    let age = t - this.startTime;
    if (age <= 0) return;
    let [r, g, b] = this.col;
    let leadL = this.tapX - age * SIGNAL_SPEED;
    let leadR = this.tapX + age * SIGNAL_SPEED;

    push();
    fill(r, g, b, 220);
    noStroke();

    if (this.endTime === null) {
      // Continuous band from tapX outward in both directions
      this._drawBand(max(WIRE_L, leadL), this.tapX);
      this._drawBand(this.tapX, min(WIRE_R, leadR));
    } else {
      // Two separate bands moving away once transmission stopped
      let trailAge = t - this.endTime;
      let trailL   = this.tapX - trailAge * SIGNAL_SPEED;
      let trailR   = this.tapX + trailAge * SIGNAL_SPEED;
      this._drawBand(max(WIRE_L, leadL),  min(WIRE_R, trailL));
      this._drawBand(max(WIRE_L, trailR), min(WIRE_R, leadR));
    }
    pop();
  }

  // Draw dots at fixed grid positions within [x1, x2].
  // Grid is anchored to WIRE_L so dots never appear to move.
  _drawBand(x1, x2) {
    if (x2 <= x1) return;
    let first = WIRE_L + ceil((x1 - WIRE_L) / DOT_SP) * DOT_SP;
    for (let x = first; x <= x2; x += DOT_SP)
      circle(x, WIRE_Y + this.yOff, DOT_R * 2);
  }
}


// ── Computer ─────────────────────────────────────────────────────────────────

class Computer {
  constructor(cfg, id) {
    this.id    = id;
    this.x     = cfg.x;
    this.col   = cfg.col;
    this.label = cfg.label;

    this.state           = 'IDLE';
    this.txTimer         = 0;
    this.flashTimer      = 0;
    this.backoffTimer    = 0;
    this.backoffMax      = 1;
    this.collisionCount  = 0;       // successive collisions; resets on successful TX
    this.backoffWireBusy  = false;  // tracks previous frame's wire state for transition detection
    this.hasMessage       = false;
    this.currentSig       = null;
    this.backoffHist      = [];  // [{start, end}] for timeline backoff bars
    this.collisionHist    = [];  // [time] collision moments for timeline X markers
  }

  triggerMessage() {
    if (this.hasMessage) return;
    this.hasMessage = true;
    if (this.state === 'IDLE') this._try();
  }

  _busy() {
    return signals.some(s => s.sourceId !== this.id && s.isAt(this.x, globalTime));
  }

  _try() {
    if (this._busy()) { this.state = 'SENSING'; }
    else { this._beginTx(); }
  }

  _beginTx() {
    this.state   = 'TRANSMITTING';
    this.txTimer = TX_DURATION;
    let sig = new Signal(this.id, this.x, globalTime, this.col);
    signals.push(sig);
    this.currentSig = sig;
  }

  // Sample a backoff duration for the current collision count.
  _sampleBackoff() {
    let window = BACKOFF_SLOT * pow(2, min(this.collisionCount, BACKOFF_MAX_N));
    return random(BACKOFF_SLOT, window);
  }

  _collide() {
    this.currentSig.ruined = true;
    this.currentSig.stop(globalTime);
    this.currentSig      = null;
    this.flashTimer      = FLASH_DUR;
    this.collisionCount++;
    this.backoffWireBusy = false;
    let bo = this._sampleBackoff();
    this.backoffMax   = bo;
    this.backoffTimer = bo;
    this.backoffHist.push({ start: globalTime, end: null });
    this.collisionHist.push(globalTime);
    this.state = 'FLASH';
  }

  update(dt) {
    this.backoffHist   = this.backoffHist.filter(
      b => b.end === null || b.end > globalTime - TL_WIN - 2
    );
    this.collisionHist = this.collisionHist.filter(t => t > globalTime - TL_WIN - 2);

    if (this.state === 'SENSING') {
      if (!this._busy()) this._beginTx();

    } else if (this.state === 'TRANSMITTING') {
      if (this._busy()) {
        this._collide();
      } else {
        this.txTimer -= dt;
        if (this.txTimer <= 0) {
          this.currentSig.stop(globalTime);
          this.currentSig     = null;
          this.hasMessage     = false;
          this.collisionCount = 0;
          this.state = 'IDLE';
        }
      }

    } else if (this.state === 'FLASH') {
      this.flashTimer -= dt;
      if (this.flashTimer <= 0) this.state = 'BACKOFF';

    } else if (this.state === 'BACKOFF') {
      let busy = this._busy();
      if (busy && !this.backoffWireBusy) {
        // Wire just became busy — re-sample using current collision count
        let bo = this._sampleBackoff();
        this.backoffMax   = bo;
        this.backoffTimer = bo;
      } else if (!busy) {
        this.backoffTimer -= dt;
        if (this.backoffTimer <= 0) {
          let last = this.backoffHist[this.backoffHist.length - 1];
          if (last && last.end === null) last.end = globalTime;
          this._try();
        }
      }
      this.backoffWireBusy = busy;
    }
  }

  draw() {
    let [r, g, b] = this.col;

    // Tap line background
    push(); stroke(80); strokeWeight(2);
    line(this.x, COMP_Y + 16, this.x, WIRE_Y); pop();

    // Signal dots on the tap — static, shown whenever any signal is at this position
    push(); noStroke();
    for (let s of signals) {
      if (!s.isAt(this.x, globalTime)) continue;
      let [sr, sg, sb] = s.col;
      fill(sr, sg, sb, 220);
      for (let y = COMP_Y + 16 + DOT_SP; y < WIRE_Y; y += DOT_SP)
        circle(this.x, y, DOT_R * 2);
    }
    pop();

    // Collision flash: red glow behind icon
    if (this.state === 'FLASH') {
      push(); noStroke();
      fill(255, 50, 50, map(this.flashTimer, 0, FLASH_DUR, 60, 210));
      ellipse(this.x, COMP_Y, 58, 54); pop();
    }

    // Computer icon (JPEG with white bg — MULTIPLY makes white transparent)
    blendMode(MULTIPLY);
    imageMode(CENTER);
    image(compImg, this.x, COMP_Y, 38, 32);
    imageMode(CORNER);
    blendMode(BLEND);

    // Colored label
    push(); textAlign(CENTER, BOTTOM); textSize(12); noStroke();
    fill(r, g, b); text(this.label, this.x, COMP_Y - 20); pop();

    // Transmit progress dial (computer's color, fills as frame goes out)
    if (this.state === 'TRANSMITTING') {
      let frac = max(0, 1 - this.txTimer / TX_DURATION);
      push(); noFill(); stroke(r, g, b); strokeWeight(2.5);
      arc(this.x, COMP_Y, 52, 52, -HALF_PI, -HALF_PI + TWO_PI * frac); pop();
    }

    // Backoff countdown arc (red, empties as backoff expires)
    if (this.state === 'BACKOFF') {
      let frac = max(0, this.backoffTimer / this.backoffMax);
      push(); noFill(); stroke(210, 70, 70); strokeWeight(2.5);
      arc(this.x, COMP_Y, 52, 52, -HALF_PI, -HALF_PI + TWO_PI * frac); pop();
    }
  }
}


// ── p5 lifecycle ─────────────────────────────────────────────────────────────

function preload() { compImg = loadImage('./computer.png'); }

function initSim() {
  randomSeed(RAND_SEED);
  globalTime  = 0;
  prevMillis  = millis();
  scheduleIdx = 0;
  periodStart = 0;
  signals     = [];
  computers   = COMP_CFGS.map((cfg, i) => new Computer(cfg, i));
}

function setup() {
  createCanvas(540, 270);
  frameRate(30);
  initSim();
  P5Capture.getInstance().start({ format: 'webm' });
}

function keyPressed() { if (key === 'r' || key === 'R') initSim(); }

function draw() {
  let now = millis();
  let dt  = min((now - prevMillis) / 1000, 0.05);
  prevMillis = now;
  globalTime += dt;

  background(255);

  for (let c of computers) c.update(dt);
  signals = signals.filter(s => !s.isDone(globalTime));

  // Fire scheduled messages
  while (scheduleIdx < MESSAGE_SCHEDULE.length) {
    let m = MESSAGE_SCHEDULE[scheduleIdx];
    if (globalTime < periodStart + m.time) break;
    computers[m.compId].triggerMessage();
    scheduleIdx++;
  }
  if (scheduleIdx >= MESSAGE_SCHEDULE.length) {
    scheduleIdx = 0;
    periodStart += SCHEDULE_PERIOD;
  }

  // Wire with terminator caps
  push();
  stroke(80); strokeWeight(3);
  line(WIRE_L, WIRE_Y - 9, WIRE_L, WIRE_Y + 9);
  line(WIRE_R, WIRE_Y - 9, WIRE_R, WIRE_Y + 9);
  strokeWeight(4);
  line(WIRE_L, WIRE_Y, WIRE_R, WIRE_Y);
  pop();

  for (let s of signals) s.draw(globalTime);
  for (let c of computers) c.draw();

  drawTimeline();
}


// ── Timeline helpers ──────────────────────────────────────────────────────────

function signalXRange(sig, propDelay, tStart, tEnd) {
  let arrive = sig.startTime + propDelay;
  let depart = sig.endTime === null ? Infinity : sig.endTime + propDelay;
  if (arrive > tEnd || depart < tStart) return null;
  let x1 = map(max(arrive, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
  let x2 = map(min(depart, globalTime, tEnd), tStart, tEnd, TL_LX, TL_LX + TL_W);
  return x2 > x1 ? { x1, x2 } : null;
}

function drawTLBar(x1, x2, y, h, col, alpha, inProgress) {
  fill(col[0], col[1], col[2], alpha);
  stroke(col[0] * 0.6, col[1] * 0.6, col[2] * 0.6);
  strokeWeight(1);
  rect(x1, y, x2 - x1, h);
  if (inProgress) addStripes(x1, y, x2 - x1, h);
}

function addStripes(x, y, w, h) {
  if (w <= 0 || h <= 0) return;
  drawingContext.save();
  drawingContext.beginPath();
  drawingContext.rect(x, y, w, h);
  drawingContext.clip();
  drawingContext.strokeStyle = 'rgba(255, 255, 255, 0.55)';
  drawingContext.lineWidth = 1.5;
  drawingContext.beginPath();
  const step = 5;
  for (let d = -h; d < w + h; d += step) {
    drawingContext.moveTo(x + d, y + h);
    drawingContext.lineTo(x + d + h, y);
  }
  drawingContext.stroke();
  drawingContext.restore();
}


// ── Timeline ──────────────────────────────────────────────────────────────────

function drawTimeline() {
  let tEnd   = max(TL_WIN, globalTime);
  let tStart = tEnd - TL_WIN;
  let rows   = computers.length;

  push();
  fill(245); noStroke();
  rect(0, TL_Y - 8, width, height - (TL_Y - 8));
  stroke(190); strokeWeight(1);
  line(0, TL_Y - 9, width, TL_Y - 9);
  pop();

  push();
  textSize(10);

  // Annotation lane
  let annLineY = TL_Y + 8;
  let tickH    = 4;
  for (let ann of ANNOTATIONS) {
    if (globalTime < ann.start) continue;
    if (ann.end < tStart || ann.start > tEnd) continue;
    let visEnd = min(ann.end, globalTime);
    let ax1    = map(max(ann.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
    let ax2    = map(min(visEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
    let ax1raw = map(ann.start, tStart, tEnd, TL_LX, TL_LX + TL_W);
    stroke(0); strokeWeight(1); noFill();
    line(ax1, annLineY, ax2, annLineY);
    if (ann.start >= tStart)                     { line(ax1, annLineY - tickH, ax1, annLineY + tickH); }
    if (ann.end <= globalTime && visEnd <= tEnd) { line(ax2, annLineY - tickH, ax2, annLineY + tickH); }
    let nowX = map(globalTime, tStart, tEnd, TL_LX, TL_LX + TL_W);
    drawingContext.save();
    drawingContext.beginPath();
    drawingContext.rect(TL_LX, TL_Y - 12, nowX - TL_LX, TL_ANN_H + 12);
    drawingContext.clip();
    fill(0); noStroke(); textAlign(LEFT, BOTTOM);
    text(ann.label, ax1raw + 2, annLineY - 2);
    drawingContext.restore();
  }

  for (let i = 0; i < rows; i++) {
    let c      = computers[i];
    let ry     = TL_Y + TL_ANN_H + i * (TL_ROW + TL_GAP);
    let [r, g, b] = c.col;
    let h2     = TL_ROW / 2;
    let y2     = ry + h2 / 2;

    fill(228); noStroke(); rect(TL_LX, ry, TL_W, TL_ROW);

    // Received signals — half height, sender color, stripes until last bit arrives or if ruined
    for (let s of signals) {
      if (s.sourceId === i) continue;
      let prop   = abs(c.x - s.tapX) / SIGNAL_SPEED;
      let xr     = signalXRange(s, prop, tStart, tEnd);
      if (!xr) continue;
      let depart = s.endTime === null ? Infinity : s.endTime + prop;
      let bad    = s.ruined || globalTime < depart;
      drawTLBar(xr.x1, xr.x2, y2, h2, s.col, bad ? 130 : 160, bad);
    }

    // Own transmission — full height, stripes if in-progress or ruined
    for (let s of signals) {
      if (s.sourceId !== i) continue;
      let xr = signalXRange(s, 0, tStart, tEnd);
      if (!xr) continue;
      let bad = s.endTime === null || s.ruined;
      drawTLBar(xr.x1, xr.x2, ry, TL_ROW, s.col, bad ? 130 : 220, bad);
    }

    // Backoff line
    for (let bk of c.backoffHist) {
      let bEnd = bk.end === null ? globalTime : bk.end;
      if (bEnd < tStart || bk.start > tEnd) continue;
      let x1 = map(max(bk.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(bEnd, tEnd),       tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      stroke(210, 70, 70); strokeWeight(1.5); noFill();
      line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
    }

    // Collision X markers
    for (let ct of c.collisionHist) {
      if (ct < tStart || ct > tEnd) continue;
      let cx = map(ct, tStart, tEnd, TL_LX, TL_LX + TL_W);
      let cy = ry + TL_ROW / 2;
      let arm = 4;
      stroke(210, 40, 40); strokeWeight(2); noFill();
      line(cx - arm, cy - arm, cx + arm, cy + arm);
      line(cx + arm, cy - arm, cx - arm, cy + arm);
    }

    // Row label in computer color
    noStroke(); fill(r, g, b); textAlign(RIGHT, CENTER);
    text(c.label, TL_LX - 4, ry + TL_ROW / 2);
  }

  // Now-marker
  let nowX = map(globalTime, tStart, tEnd, TL_LX, TL_LX + TL_W);
  stroke(140); strokeWeight(1);
  line(nowX, TL_Y + TL_ANN_H, nowX, TL_Y + TL_ANN_H + rows * (TL_ROW + TL_GAP) - TL_GAP);

  // Time axis
  let axY = TL_Y + TL_ANN_H + rows * (TL_ROW + TL_GAP) - TL_GAP + 14;
  stroke(160); strokeWeight(1);
  line(TL_LX, axY - 8, TL_LX + TL_W, axY - 8);
  noStroke(); fill(80); textAlign(CENTER, TOP);
  for (let ts = ceil(tStart / 5) * 5; ts <= tEnd; ts += 5) {
    let tx = map(ts, tStart, tEnd, TL_LX, TL_LX + TL_W);
    stroke(160); strokeWeight(1); line(tx, axY - 8, tx, axY - 4); noStroke();
    text(nf(ts, 1, 0) + 's', tx, axY - 3);
  }

  pop();
}

