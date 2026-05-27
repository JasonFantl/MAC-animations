// Pure ALOHA simulation on a Hawaii map
// Stations transmit immediately without carrier sensing.
// Collisions are detected when transmission windows overlap at the base station.

const PACKET_SPEED     = 110;   // px/s — travel time drives network timing
const SIFS             = 0.1;   // s — Short Inter-Frame Space before ACK
const ACK_DELAY        = 0.4;   // s — total: SIFS (0.1) + ACK frame (0.3)
const RANGE_RADIUS     = 220;   // px — visual radio range circle
const RAND_SEED        = 43;
const BACKOFF_MEAN_SEC = 1.5;   // mean of exponential backoff distribution (s)

const MAP_X = 55, MAP_Y = -15;
const BASE_MAP_POS     = { x: 215, y: 145 };
const ISLAND_POSITIONS = [
  { x:  91, y:  70, label: 'A', col: [220,  55,  55] },
  { x: 306, y: 195, label: 'B', col: [ 55, 175,  75] },
  { x: 356, y: 235, label: 'C', col: [ 55, 110, 215] },
];

// Timeline — matching WiFi/WiFi-RTS dimensions
const TL_WIN   = 20;
const TL_Y     = 257;
const TL_ANN_H = 16;
const TL_ROW   = 28;
const TL_GAP   = 9;
const TL_LX    = 50;
const TL_W     = 460;

const TX_COL = [100, 160, 255];

const MESSAGE_SCHEDULE = [
  { time: 1.0,  stationId: 0 },

  { time: 5.0,  stationId: 1 },
  
  { time: 8,  stationId: 2 },
  { time: 8.9,  stationId: 1 },
  
  { time: 21,  stationId: 1 },
  { time: 21.5, stationId: 0 },
  { time: 22, stationId: 2 },
];
const SCHEDULE_PERIOD = 50;

const ANNOTATIONS = [
  { label: 'Node A', start: 0.9, end: 3 },
  { label: 'Node B', start: 4.9, end: 6.5 },
  { label: 'B and C collide', start: 7.9, end: 19 },
  { label: 'All nodes', start: 20.9, end: 39.5 },
];

function expRandom(mean) {
  return -Math.log(max(1e-6, random())) * mean;
}

let mapImg, towerImg;
let network, baseStation, stations, globalTime, prevMillis;
let scheduleIndex, schedulePeriodStart;

function preload() {
  mapImg   = loadImage('./hawaiian-island-map-outline-vector-55378863.webp');
  towerImg = loadImage('./cell-tower-icon.jpg');
}


// ---- Network ----------------------------------------------------------------
// Tracks uplink transmissions only. ACKs travel on a separate downlink channel
// and are never registered here — they cannot collide with uplink traffic.

class Network {
  constructor() { this.transmissions = []; }

  register(id, startTime, duration) {
    let tx = { id, startTime, endTime: startTime + duration, ruined: false };
    for (let other of this.transmissions) {
      if (other.startTime < tx.endTime && other.endTime > tx.startTime) {
        other.ruined = true;
        tx.ruined    = true;
      }
    }
    this.transmissions.push(tx);
    return tx;
  }

  prune(time) {
    this.transmissions = this.transmissions.filter(t => t.endTime > time - BACKOFF_MEAN_SEC * 2 - 2);
  }
}


// ---- Station ----------------------------------------------------------------
// State machine: IDLE → TRANSMITTING → BACKOFF → IDLE (via ACK)
// No carrier sensing — stations transmit immediately when triggered.

class Station {
  constructor(pos, id) {
    this.x     = MAP_X + pos.x;
    this.y     = MAP_Y + pos.y;
    this.id    = id;
    this.label = pos.label;
    this.col   = pos.col;

    this.state            = 'IDLE';
    this.backoffTimer     = 0;
    this.backoffMax       = 1;
    this.transmitTimer    = 0;
    this.transmitDuration = 0;
    this.networkTx        = null;
    this.history          = [];
    this.ackHistory       = [];
  }

  _setState(newState) {
    if (this.history.length > 0) {
      let last = this.history[this.history.length - 1];
      if (last.end === null) {
        last.end = globalTime;
        if (this.networkTx && last.state === 'TRANSMITTING') {
          last.ruined = this.networkTx.ruined;
        }
      }
    }
    this.state = newState;
    const tracked = ['TRANSMITTING', 'BACKOFF'];
    if (tracked.includes(newState)) {
      this.history.push({ state: newState, start: globalTime, end: null });
    }
  }

  _beginTransmit() {
    this._setState('TRANSMITTING');
    let travelTime        = dist(this.x, this.y, baseStation.x, baseStation.y) / PACKET_SPEED;
    this.networkTx        = network.register(this.id, globalTime, travelTime);
    this.transmitTimer    = travelTime;
    this.transmitDuration = travelTime;
  }

  noteAckSent() {
    this.ackHistory.push({ start: globalTime + SIFS, end: null });
  }

  receiveAck() {
    if (this.state === 'BACKOFF') {
      closeOpen(this.ackHistory);
      this._setState('IDLE');
    }
  }

  update(dt) {
    this.history    = this.history.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.ackHistory = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);

    if (this.state === 'TRANSMITTING') {
      this.transmitTimer -= dt;
      if (this.transmitTimer <= 0) {
        if (!this.networkTx.ruined) baseStation.receivePacket(this);
        let bo = max(ACK_DELAY, expRandom(BACKOFF_MEAN_SEC));
        this.backoffMax   = bo;
        this.backoffTimer = bo;
        this._setState('BACKOFF');
      }

    } else if (this.state === 'BACKOFF') {
      this.backoffTimer -= dt;
      if (this.backoffTimer <= 0) this._beginTransmit();
    }
  }

  draw() {
    drawRangeCircle(this.x, this.y);
    if (this.state === 'TRANSMITTING') {
      drawGlowRing(this.x, this.y, ...TX_COL);
      drawArrow(this.x, this.y, baseStation.x, baseStation.y, ...TX_COL);
    }

    blendMode(MULTIPLY);
    image(towerImg, this.x - 12, this.y - 20, 24, 30);
    blendMode(BLEND);

    push();
    textAlign(CENTER, BOTTOM); textSize(10); noStroke();
    fill(30);
    text(this.label, this.x, this.y - 22);
    pop();

    if (this.state === 'TRANSMITTING') {
      let frac = max(0, 1 - this.transmitTimer / this.transmitDuration);
      push(); noFill(); stroke(...TX_COL); strokeWeight(2.5);
      arc(this.x, this.y, 48, 48, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    if (this.state === 'BACKOFF') {
      let frac = this.backoffTimer / this.backoffMax;
      push(); noFill(); stroke(210, 70, 70); strokeWeight(2.5);
      arc(this.x, this.y, 48, 48, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }
  }
}


// ---- BaseStation ------------------------------------------------------------

class BaseStation {
  constructor(mapX, mapY) {
    this.x = MAP_X + mapX;
    this.y = MAP_Y + mapY;
    this.pendingAcks = [];
    this.ackHistory  = [];
  }

  receivePacket(station) {
    station.noteAckSent();
    this.ackHistory.push({ start: globalTime + SIFS, end: null, stationId: station.id });
    this.pendingAcks.push({ stationId: station.id, timer: ACK_DELAY });
  }

  update(dt) {
    this.ackHistory = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    for (let ack of this.pendingAcks) {
      ack.timer -= dt;
      if (ack.timer <= 0) {
        closeOpen(this.ackHistory);
        let s = stations.find(st => st.id === ack.stationId);
        if (s) s.receiveAck();
      }
    }
    this.pendingAcks = this.pendingAcks.filter(a => a.timer > 0);
  }

  draw() {
    let sendingACK = this.pendingAcks.length > 0;
    if (sendingACK) {
      drawGlowRing(this.x, this.y, 60, 190, 90);
      let target = stations.find(st => st.id === this.pendingAcks[0].stationId);
      if (target) drawArrow(this.x, this.y, target.x, target.y, 60, 190, 90);
    }
    drawRangeCircle(this.x, this.y);

    blendMode(MULTIPLY);
    image(towerImg, this.x - 22, this.y - 40, 44, 54);
    blendMode(BLEND);

    push();
    textAlign(CENTER, BOTTOM); textSize(10); noStroke();
    fill(30);
    text('Base Station', this.x, this.y - 44);
    pop();

    if (sendingACK) {
      let most = this.pendingAcks.reduce((best, a) => a.timer < best.timer ? a : best);
      let frac = max(0, 1 - most.timer / ACK_DELAY);
      push(); noFill(); stroke(60, 190, 90); strokeWeight(2.5);
      arc(this.x, this.y, 64, 64, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }
  }
}


// ---- Helpers ----------------------------------------------------------------

function closeOpen(arr) {
  let open = arr.findLast(s => s.end === null);
  if (open) open.end = globalTime;
}

function drawRangeCircle(x, y) {
  push();
  noFill(); stroke(180, 180, 200, 80); strokeWeight(1);
  drawingContext.setLineDash([4, 6]);
  ellipse(x, y, RANGE_RADIUS * 2, RANGE_RADIUS * 2);
  drawingContext.setLineDash([]);
  pop();
}

function drawGlowRing(x, y, r, g, b) {
  push();
  noStroke(); fill(r, g, b, 35);
  ellipse(x, y, RANGE_RADIUS * 2, RANGE_RADIUS * 2);
  noFill(); stroke(r, g, b, 100); strokeWeight(1.5);
  ellipse(x, y, RANGE_RADIUS * 2, RANGE_RADIUS * 2);
  pop();
}

function drawArrow(x1, y1, x2, y2, r, g, b) {
  let dx = x2 - x1, dy = y2 - y1;
  let d  = sqrt(dx * dx + dy * dy);
  if (d < 1) return;
  let nx = dx / d, ny = dy / d;
  let sx = x1 + nx * 20, sy = y1 + ny * 20;
  let ex = x2 - nx * 25, ey = y2 - ny * 25;
  push();
  stroke(r, g, b, 210); strokeWeight(2);
  line(sx, sy, ex - nx * 11, ey - ny * 11);
  fill(r, g, b, 210); noStroke();
  push();
  translate(ex, ey);
  rotate(atan2(dy, dx));
  triangle(0, 0, -13, -5, -13, 5);
  pop();
  pop();
}


// ---- p5 lifecycle -----------------------------------------------------------

function initSim() {
  randomSeed(RAND_SEED);
  globalTime          = 0;
  prevMillis          = millis();
  scheduleIndex       = 0;
  schedulePeriodStart = 0;
  network     = new Network();
  baseStation = new BaseStation(BASE_MAP_POS.x, BASE_MAP_POS.y);
  stations    = ISLAND_POSITIONS.map((pos, i) => new Station(pos, i));
}

function setup() {
  createCanvas(520, 440);
  frameRate(30);
  initSim();
  P5Capture.getInstance().start({ format: 'webm' });
}

function keyPressed() {
  if (key === 'r' || key === 'R') initSim();
}

function draw() {
  let now = millis();
  let dt  = min((now - prevMillis) / 1000, 0.05);
  prevMillis = now;
  globalTime += dt;

  background(255);
  image(mapImg, MAP_X, MAP_Y, 500, 500);

  network.prune(globalTime);
  baseStation.update(dt);
  for (let s of stations) s.update(dt);

  while (scheduleIndex < MESSAGE_SCHEDULE.length) {
    let msg      = MESSAGE_SCHEDULE[scheduleIndex];
    let fireTime = schedulePeriodStart + msg.time;
    if (globalTime < fireTime) break;
    let s = stations[msg.stationId];
    if (s.state === 'IDLE') s._beginTransmit();
    scheduleIndex++;
  }
  if (scheduleIndex >= MESSAGE_SCHEDULE.length) {
    scheduleIndex       = 0;
    schedulePeriodStart += SCHEDULE_PERIOD;
  }

  for (let s of stations) s.draw();
  baseStation.draw();
  drawTimeline();

  // Legend — bottom-left rounded box
  push();
  textSize(10); textAlign(LEFT, CENTER);
  let lx = 7;
  const lh = 16;
  const legendBoxH = 52;
  const legendBoxY = floor((TL_Y - legendBoxH) / 2);
  let ly = legendBoxY + 6;
  let [tr, tg, tb] = TX_COL;

  fill(240, 240, 240, 210); stroke(90, 90, 90); strokeWeight(0.8);
  rect(2, legendBoxY, 90, legendBoxH, 6);

  fill(tr, tg, tb, 160); noStroke(); rect(lx, ly,           10, 10);
  fill(30); text('Data (λ1)',    lx + 14, ly + 5);
  fill(60, 190, 90);  noStroke(); rect(lx, ly + lh,         10, 10);
  fill(30); text('ACK (λ2)',     lx + 14, ly + lh   + 5);
  stroke(210, 70, 70); strokeWeight(2); line(lx, ly + lh*2 + 5, lx + 10, ly + lh*2 + 5);
  fill(30); noStroke(); text('Backoff', lx + 14, ly + lh*2 + 5);
  pop();
}


// ---- Timeline ---------------------------------------------------------------

function segToXRange(seg, tStart, tEnd) {
  let segEnd = seg.end === null ? globalTime : seg.end;
  if (segEnd < tStart) return null;
  let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
  let x2 = map(min(segEnd,   tEnd),    tStart, tEnd, TL_LX, TL_LX + TL_W);
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

function drawTimeline() {
  let tEnd   = max(TL_WIN, globalTime);
  let tStart = tEnd - TL_WIN;
  let rows   = stations.length + 1;
  let totalH = TL_ANN_H + rows * (TL_ROW + TL_GAP) + 18;

  push();
  fill(245); noStroke();
  rect(0, TL_Y - 8, width, totalH + 8);
  stroke(190); strokeWeight(1);
  line(0, TL_Y - 9, width, TL_Y - 9);
  pop();

  push();
  textSize(10);

  let [tr, tg, tb] = TX_COL;

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

  for (let i = 0; i < stations.length; i++) {
    let s  = stations[i];
    let ry = TL_Y + TL_ANN_H + i * (TL_ROW + TL_GAP);
    let h2 = TL_ROW / 2;
    let y2 = ry + h2 / 2;

    fill(228); noStroke(); rect(TL_LX, ry, TL_W, TL_ROW);

    // ACK from base — half height, all stations hear it
    for (let seg of baseStation.ackHistory) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let a = seg.end === null ? 130 : (seg.stationId === s.id ? 220 : 80);
      drawTLBar(r.x1, r.x2, y2, h2, [60, 190, 90], a, seg.end === null);
    }

    // Own transmission — full height
    for (let seg of s.history) {
      if (seg.state !== 'TRANSMITTING') continue;
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      drawTLBar(r.x1, r.x2, ry, TL_ROW, [tr, tg, tb], seg.end === null ? 130 : 220, false);
    }

    // Backoff line
    for (let seg of s.history) {
      if (seg.state !== 'BACKOFF') continue;
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      stroke(210, 70, 70); strokeWeight(1.5); noFill();
      line(r.x1, ry + TL_ROW / 2, r.x2, ry + TL_ROW / 2);
    }

    // Own ACK segment — half height
    for (let seg of s.ackHistory) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      drawTLBar(r.x1, r.x2, y2, h2, [60, 190, 90], seg.end === null ? 130 : 220, seg.end === null);
    }

    fill(60); noStroke(); textAlign(RIGHT, CENTER);
    text(s.label, TL_LX - 4, ry + TL_ROW / 2);
  }

  // Base station row
  let bry = TL_Y + TL_ANN_H + stations.length * (TL_ROW + TL_GAP);
  fill(195); noStroke(); rect(TL_LX, bry, TL_W, TL_ROW);

  // Incoming transmissions — half height, stripes if ruined
  for (let s of stations) {
    for (let seg of s.history) {
      if (seg.state !== 'TRANSMITTING') continue;
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let ruined = seg.end === null ? (s.networkTx?.ruined ?? false) : (seg.ruined ?? false);
      drawTLBar(r.x1, r.x2, bry + TL_ROW / 4, TL_ROW / 2, [tr, tg, tb], seg.end === null ? 130 : 220, ruined);
    }
  }

  // ACK outgoing — full height
  for (let seg of baseStation.ackHistory) {
    let r = segToXRange(seg, tStart, tEnd);
    if (!r) continue;
    drawTLBar(r.x1, r.x2, bry, TL_ROW, [60, 190, 90], seg.end === null ? 130 : 220, seg.end === null);
  }

  fill(50); noStroke(); textAlign(RIGHT, CENTER);
  text('Base', TL_LX - 4, bry + TL_ROW / 2);

  // Now-marker
  let nowX = map(globalTime, tStart, tEnd, TL_LX, TL_LX + TL_W);
  stroke(140); strokeWeight(1);
  line(nowX, TL_Y + TL_ANN_H, nowX, bry + TL_ROW);

  // Time axis
  let axisY = bry + TL_ROW + 12;
  stroke(160); strokeWeight(1);
  line(TL_LX, axisY - 8, TL_LX + TL_W, axisY - 8);
  noStroke(); fill(80); textAlign(CENTER, TOP);
  for (let ts = ceil(tStart / 5) * 5; ts <= tEnd; ts += 5) {
    let tx = map(ts, tStart, tEnd, TL_LX, TL_LX + TL_W);
    stroke(160); strokeWeight(1); line(tx, axisY - 8, tx, axisY - 4); noStroke();
    text(nf(ts, 1, 0) + 's', tx, axisY - 3);
  }

  pop();
}
