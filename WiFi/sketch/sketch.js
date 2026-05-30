// WiFi (CSMA/CA) simulation
const SIFS       = 0.1;   // s — Short Inter-Frame Space
const ACK_DELAY  = 0.4;   // s — total: SIFS (0.1) + ACK frame (0.3)
const RAND_SEED  = 41;

// CSMA/CA timing
const DIFS       = 0.4;
const SLOT_TIME  = 0.15;
const CW_MIN     = 7;
const CW_MAX     = 63;

// Transmission timing
const TX_DURATION = 1.8;   // s — data frame on air

const BASE_ID = -1;

// Layout — same topology as WiFi-RTS (A hidden from B and C)
const BASE_POS = { x: 320, y: 145 };
const STATION_CFGS = [
  { x: 180, y: 145, label: 'A', col: [220, 55,  55] },
  { x: 425, y: 90,  label: 'B', col: [55,  175, 75] },
  { x: 425, y: 200, label: 'C', col: [55,  110, 215] },
];
const COMM_RADIUS = 160;

// Timeline — identical dimensions to WiFi-RTS
const TL_WIN   = 20;
const TL_Y     = 257;
const TL_ANN_H = 16;
const TL_ROW   = 28;
const TL_GAP   = 9;
const TL_LX    = 50;
const TL_W     = 460;

const MESSAGE_SCHEDULE = [
  { time: 1.0,  stationId: 0 },

  { time: 6.0,  stationId: 1 },
  
  { time: 11,  stationId: 2 },
  { time: 11.9,  stationId: 1 },

  { time: 19.0, stationId: 0 },
  { time: 19.5, stationId: 2 },
  
  { time: 34.0,  stationId: 1 },
  { time: 34.1, stationId: 0 },
  { time: 34.2, stationId: 2 },
];
const SCHEDULE_PERIOD = 50;

const ANNOTATIONS = [
  { label: 'Node A (hidden)', start: 0.9, end: 4 },
  { label: 'Node B (neighbor)', start: 5.9, end: 9 },
  { label: 'B and C (neighbors) avoid collision', start: 10.9, end: 17 },
  { label: 'A and B (hidden) collide', start: 18.9, end: 32 },

  { label: 'All nodes colliding', start: 33.9, end: 47 },
];


const TX_COL = [100, 160, 255];

let routerImg, compImg;
let network, baseStation, stations, globalTime, prevMillis;
let scheduleIndex, schedulePeriodStart;

function preload() {
  routerImg = loadImage('./router.png');
  compImg   = loadImage('./computer.png');
}


// ---- Network ----------------------------------------------------------------

class Network {
  constructor() { this.transmissions = []; }

  register(id, startTime, duration) {
    let srcX = id === BASE_ID ? baseStation.x : stations[id].x;
    let srcY = id === BASE_ID ? baseStation.y : stations[id].y;
    let tx = { id, startTime, endTime: startTime + duration, ruined: false, srcX, srcY };
    for (let other of this.transmissions) {
      if (other.startTime < tx.endTime && other.endTime > tx.startTime) {
        other.ruined = true;
        tx.ruined    = true;
      }
    }
    this.transmissions.push(tx);
    return tx;
  }

  isRuinedAt(tx, x, y) {
    return this.transmissions.some(other => {
      if (other === tx) return false;
      if (other.startTime >= tx.endTime || other.endTime <= tx.startTime) return false;
      return dist(x, y, other.srcX, other.srcY) <= COMM_RADIUS;
    });
  }

  prune(time) {
    this.transmissions = this.transmissions.filter(t => t.endTime > time - TX_DURATION - 1);
  }
}


// ---- Station ----------------------------------------------------------------
// State machine:
//   IDLE → message arrives → SENSING or DIFS_WAIT
//   SENSING → channel free → DIFS_WAIT
//   DIFS_WAIT → DIFS elapsed, first clean access → TRANSMITTING; after busy/collision → BACKOFF
//   BACKOFF → slots exhausted → TRANSMITTING
//   TRANSMITTING → sent → DIFS_WAIT (wait for ACK)
//   DIFS_WAIT/BACKOFF → ACK received → IDLE

class Station {
  constructor(cfg, id) {
    this.x     = cfg.x;
    this.y     = cfg.y;
    this.label = cfg.label;
    this.col   = cfg.col;
    this.id    = id;

    this.state            = 'IDLE';
    this.hasMessage       = false;
    this.difsTimer        = 0;
    this.backoffTimer     = 0;
    this.backoffMax       = 1;
    this.backoffPaused    = false;
    this.needsBackoff     = false;
    this.transmitTimer    = 0;
    this.transmitDuration = 0;
    this.txAttempts       = 0;
    this.contentionWin    = CW_MIN;
    this.networkTx        = null;
    this.history          = [];
    this.ackHistory       = [];
    this.messageRequest   = [];
  }

  _setState(newState) {
    if (this.history.length > 0) {
      let last = this.history[this.history.length - 1];
      if (last.end === null) {
        last.end = globalTime;
        if (this.networkTx && last.state === 'TRANSMITTING') {
          last.interferers = network.transmissions
            .filter(tx => tx.id !== this.id && tx.startTime < last.end && tx.endTime > last.start)
            .map(tx => ({ srcX: tx.srcX, srcY: tx.srcY }));
        }
      }
    }
    this.state = newState;
    const tracked = ['SENSING', 'DIFS_WAIT', 'BACKOFF', 'TRANSMITTING'];
    if (tracked.includes(newState)) {
      this.history.push({ state: newState, start: globalTime, end: null });
    }
  }

  _channelBusy() {
    return network.transmissions.some(tx => {
      if (tx.id === this.id || tx.endTime <= globalTime) return false;
      let srcX = tx.id === BASE_ID ? baseStation.x : stations[tx.id].x;
      let srcY = tx.id === BASE_ID ? baseStation.y : stations[tx.id].y;
      return dist(this.x, this.y, srcX, srcY) <= COMM_RADIUS;
    });
  }

  triggerMessage() {
    if (this.hasMessage) return;
    this.hasMessage = true;
    this.messageRequest.push(globalTime);
    if (this.state === 'IDLE') {
      if (this._channelBusy()) { this._setState('SENSING'); }
      else { this._retryDIFS(false); }
    }
  }

  _enterBackoff() {
    if (this.txAttempts > 0) {
      this.contentionWin = min(this.contentionWin * 2, CW_MAX);
    }
    let slots          = floor(random(0, this.contentionWin + 1));
    this.backoffMax    = this.contentionWin * SLOT_TIME;
    this.backoffTimer  = slots * SLOT_TIME;
    this.backoffPaused = false;
    this._setState('BACKOFF');
  }

  _retryDIFS(needsBackoff = true) { this.needsBackoff = needsBackoff; this._setState('DIFS_WAIT'); this.difsTimer = DIFS; }

  _beginTransmit() {
    this.txAttempts++;
    this._setState('TRANSMITTING');
    this.networkTx        = network.register(this.id, globalTime, TX_DURATION);
    this.transmitTimer    = TX_DURATION;
    this.transmitDuration = TX_DURATION;
  }

  noteAckSent() {
    this.ackHistory.push({ start: globalTime + SIFS, end: null });
  }

  receiveAck() {
    if (this.state === 'DIFS_WAIT' || this.state === 'BACKOFF' || this.state === 'SENSING') {
      closeOpen(this.ackHistory);
      this.hasMessage    = false;
      this.txAttempts    = 0;
      this.contentionWin = CW_MIN;
      this._setState('IDLE');
    }
  }

  update(dt) {
    this.history        = this.history.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.ackHistory     = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.messageRequest = this.messageRequest.filter(t => t > globalTime - TL_WIN - 2);

    if (this.state === 'SENSING') {
      if (!this._channelBusy()) { this._retryDIFS(); }

    } else if (this.state === 'DIFS_WAIT') {
      if (this._channelBusy()) { this._setState('SENSING'); }
      else {
        this.difsTimer -= dt;
        if (this.difsTimer <= 0) { if (this.needsBackoff) this._enterBackoff(); else this._beginTransmit(); }
      }

    } else if (this.state === 'BACKOFF') {
      let busy = this._channelBusy();
      if (busy !== this.backoffPaused) {
        this.backoffPaused = busy;
        let last = this.history[this.history.length - 1];
        if (last && last.end === null) last.end = globalTime;
        this.history.push({ state: busy ? 'SENSING' : 'BACKOFF', start: globalTime, end: null });
      }
      if (!busy) {
        this.backoffTimer -= dt;
        if (this.backoffTimer <= 0) this._beginTransmit();
      }

    } else if (this.state === 'TRANSMITTING') {
      this.transmitTimer -= dt;
      if (this.transmitTimer <= 0) {
        baseStation.receiveData(this);
        this._retryDIFS();
      }
    }
  }

  draw() {
    let transmitting = this.state === 'TRANSMITTING';

    drawRangeCircle(this.x, this.y);

    if (transmitting) {
      drawGlowRing(this.x, this.y, ...TX_COL);
      drawArrow(this.x, this.y, baseStation.x, baseStation.y, ...TX_COL);
    }

    blendMode(MULTIPLY);
    imageMode(CENTER);
    image(compImg, this.x, this.y, 33, 28);
    imageMode(CORNER);
    blendMode(BLEND);

    push();
    textAlign(CENTER, BOTTOM); textSize(12); noStroke();
    fill(60);
    text(this.label, this.x, this.y - 22);
    pop();

    if (transmitting) {
      let frac = max(0, 1 - this.transmitTimer / this.transmitDuration);
      push(); noFill(); stroke(...TX_COL); strokeWeight(2.5);
      arc(this.x, this.y, 54, 54, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    if (this.state === 'BACKOFF') {
      let frac   = max(0, this.backoffTimer / this.backoffMax);
      let frozen = this._channelBusy();
      push(); noFill();
      stroke(frozen ? 160 : 210, frozen ? 160 : 70, frozen ? 160 : 70);
      strokeWeight(2.5);
      arc(this.x, this.y, 54, 54, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }
  }
}


// ---- BaseStation ------------------------------------------------------------

class BaseStation {
  constructor(x, y) {
    this.x = x;
    this.y = y;
    this.pendingAcks = [];
    this.ackHistory  = [];
  }

  receiveData(station) {
    if (network.isRuinedAt(station.networkTx, this.x, this.y)) return;
    station.noteAckSent();
    this.ackHistory.push({ start: globalTime + SIFS, end: null, stationId: station.id });
    this.pendingAcks.push({ stationId: station.id, timer: ACK_DELAY });
    network.register(BASE_ID, globalTime + SIFS, ACK_DELAY - SIFS);
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
    imageMode(CENTER);
    image(routerImg, this.x, this.y, 44, 33);
    imageMode(CORNER);
    blendMode(BLEND);

    if (sendingACK) {
      let most = this.pendingAcks.reduce((best, a) => a.timer < best.timer ? a : best);
      let frac = max(0, 1 - most.timer / (ACK_DELAY - SIFS));
      push(); noFill(); stroke(60, 190, 90); strokeWeight(2.5);
      arc(this.x, this.y, 64, 64, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    push();
    textAlign(CENTER, BOTTOM); textSize(11); noStroke();
    fill(80);
    text('Router', this.x, this.y - 25);
    pop();
  }
}


function closeOpen(arr) {
  let open = arr.findLast(s => s.end === null);
  if (open) open.end = globalTime;
}

function drawRangeCircle(x, y) {
  push();
  noFill(); stroke(180, 180, 200, 80); strokeWeight(1);
  drawingContext.setLineDash([4, 6]);
  ellipse(x, y, COMM_RADIUS * 2, COMM_RADIUS * 2);
  drawingContext.setLineDash([]);
  pop();
}

function drawGlowRing(x, y, r, g, b) {
  push();
  noStroke(); fill(r, g, b, 35);
  ellipse(x, y, COMM_RADIUS * 2, COMM_RADIUS * 2);
  noFill(); stroke(r, g, b, 100); strokeWeight(1.5);
  ellipse(x, y, COMM_RADIUS * 2, COMM_RADIUS * 2);
  pop();
}

function drawArrow(x1, y1, x2, y2, r, g, b) {
  let dx = x2 - x1, dy = y2 - y1;
  let d = sqrt(dx * dx + dy * dy);
  if (d < 1) return;
  let nx = dx / d, ny = dy / d;
  let sx = x1 + nx * 33, sy = y1 + ny * 33;
  let ex = x2 - nx * 30, ey = y2 - ny * 30;
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
  baseStation = new BaseStation(BASE_POS.x, BASE_POS.y);
  stations    = STATION_CFGS.map((cfg, i) => new Station(cfg, i));
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

  network.prune(globalTime);
  baseStation.update(dt);
  for (let s of stations) s.update(dt);

  while (scheduleIndex < MESSAGE_SCHEDULE.length) {
    let msg      = MESSAGE_SCHEDULE[scheduleIndex];
    let fireTime = schedulePeriodStart + msg.time;
    if (globalTime < fireTime) break;
    stations[msg.stationId].triggerMessage();
    scheduleIndex++;
  }
  if (scheduleIndex >= MESSAGE_SCHEDULE.length) {
    scheduleIndex       = 0;
    schedulePeriodStart += SCHEDULE_PERIOD;
  }

  for (let s of stations) s.draw();
  baseStation.draw();

  drawTimeline();

  // Legend
  push();
  textSize(10); textAlign(LEFT, CENTER);
  let lx = 7;
  const lh = 16;
  const legendBoxH = 106;
  const legendBoxY = floor((TL_Y - legendBoxH) / 2);
  let ly = legendBoxY + 6;
  let [tr, tg, tb] = TX_COL;

  fill(240, 240, 240, 210); stroke(90, 90, 90); strokeWeight(0.8);
  rect(2, legendBoxY, 90, legendBoxH, 6);

  fill(tr, tg, tb, 160); noStroke(); rect(lx, ly,       10, 10);
  fill(30); text('Data',        lx + 14, ly + 5);
  fill(60, 190, 90);      noStroke(); rect(lx, ly+lh,   10, 10);
  fill(30); text('ACK',         lx + 14, ly + lh   + 5);
  stroke(0); strokeWeight(1.5); line(lx+5, ly+lh*2, lx+5, ly+lh*2+10);
  fill(30); noStroke(); text('New message', lx + 14, ly + lh*2 + 5);
  stroke(0); strokeWeight(2); line(lx, ly+lh*3+5, lx+10, ly+lh*3+5);
  fill(30); noStroke(); text('Sensing',     lx + 14, ly + lh*3 + 5);
  stroke(230, 140, 30); strokeWeight(2); line(lx, ly+lh*4+5, lx+10, ly+lh*4+5);
  fill(30); noStroke(); text('DIFS wait',   lx + 14, ly + lh*4 + 5);
  stroke(210, 70, 70);  strokeWeight(2); line(lx, ly+lh*5+5, lx+10, ly+lh*5+5);
  fill(30); noStroke(); text('Backoff',     lx + 14, ly + lh*5 + 5);
  pop();
}


// ---- Timeline ---------------------------------------------------------------

function segRuinedAt(seg, x, y) {
  if (!seg.interferers || seg.interferers.length === 0) return false;
  return seg.interferers.some(p => dist(x, y, p.srcX, p.srcY) <= COMM_RADIUS);
}

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

    // Overheard transmissions from in-range stations — half height
    for (let src of stations) {
      if (src === s) continue;
      if (dist(s.x, s.y, src.x, src.y) > COMM_RADIUS) continue;
      for (let seg of src.history) {
        if (seg.state !== 'TRANSMITTING') continue;
        let r = segToXRange(seg, tStart, tEnd);
        if (!r) continue;
        drawTLBar(r.x1, r.x2, y2, h2, [tr, tg, tb], seg.end === null ? 130 : 80, seg.end === null || segRuinedAt(seg, s.x, s.y));
      }
    }

    // ACK from router — half height
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

    // State lines
    for (let seg of s.history) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let { x1, x2 } = r;
      if (seg.state === 'SENSING') {
        stroke(0); strokeWeight(1.5); noFill();
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      } else if (seg.state === 'DIFS_WAIT') {
        stroke(230, 140, 30); strokeWeight(1.5); noFill();
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      } else if (seg.state === 'BACKOFF') {
        stroke(210, 70, 70); strokeWeight(1.5); noFill();
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      }
    }

    // Message-arrival tick
    for (let t of s.messageRequest) {
      if (t < tStart || t > tEnd) continue;
      let tx = map(t, tStart, tEnd, TL_LX, TL_LX + TL_W);
      stroke(0); strokeWeight(1.5); noFill();
      line(tx, ry, tx, ry + TL_ROW);
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

  // Router row
  let bry = TL_Y + TL_ANN_H + stations.length * (TL_ROW + TL_GAP);
  fill(195); noStroke(); rect(TL_LX, bry, TL_W, TL_ROW);

  // Incoming transmissions on router row — half height
  for (let s of stations) {
    for (let seg of s.history) {
      if (seg.state !== 'TRANSMITTING') continue;
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      drawTLBar(r.x1, r.x2, bry + TL_ROW / 4, TL_ROW / 2, [tr, tg, tb], seg.end === null ? 130 : 220, seg.end === null || segRuinedAt(seg, baseStation.x, baseStation.y));
    }
  }

  // ACK from router — full height
  for (let seg of baseStation.ackHistory) {
    let r = segToXRange(seg, tStart, tEnd);
    if (!r) continue;
    drawTLBar(r.x1, r.x2, bry, TL_ROW, [60, 190, 90], seg.end === null ? 130 : 220, seg.end === null);
  }

  fill(50); noStroke(); textAlign(RIGHT, CENTER);
  text('Router', TL_LX - 4, bry + TL_ROW / 2);

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
