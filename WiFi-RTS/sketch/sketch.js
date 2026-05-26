// WiFi RTS/CTS simulation
const SIFS            = 0.1;   // s — Short Inter-Frame Space
const ACK_DELAY       = 0.4;   // s — total: SIFS (0.1) + ACK frame (0.3)
const RAND_SEED       = 42;

// CSMA/CA timing
const DIFS       = 0.4;
const SLOT_TIME  = 0.15;
const CW_MIN     = 7;
const CW_MAX     = 63;

// RTS/CTS timing
const RTS_DURATION  = 0.45;  // s — RTS frame on the air
const CTS_DURATION  = 0.3;   // s — CTS frame on the air
const DATA_DURATION = 1.8;   // s — data payload
const CTS_TIMEOUT   = 0.5;   // s — SIFS + CTS_DURATION + small margin

const BASE_ID = -1;          // sentinel for router transmissions in network

// Layout
const BASE_POS = { x: 320, y: 145 };
const STATION_CFGS = [
  { x: 180, y: 145, label: 'A', col: [220, 55,  55]  },
  { x: 425, y: 90,  label: 'B', col: [55,  175, 75]  },
  { x: 425, y: 200, label: 'C', col: [55,  110, 215] },
];
const COMM_RADIUS = 160;

// Timeline
const TL_WIN   = 20;
const TL_Y     = 257;   // top of timeline panel (annotation lane starts here)
const TL_ANN_H = 16;    // height of annotation lane above the rows
const TL_ROW   = 28;
const TL_GAP   = 9;
const TL_LX    = 50;
const TL_W     = 460;

const MESSAGE_SCHEDULE = [
  { time: 1.0,  stationId: 0 },

  { time: 7.0,  stationId: 1 },
  
  { time: 13,  stationId: 2 },
  { time: 14.9,  stationId: 1 },

  { time: 23.0, stationId: 0 },
  { time: 23.5, stationId: 2 },
  
  { time: 33.0,  stationId: 1 },
  { time: 33.1, stationId: 0 },
  { time: 33.2, stationId: 2 },
];
const SCHEDULE_PERIOD = 50;

const ANNOTATIONS = [
  { label: 'Hidden node (A)', start: 0.9, end: 5 },
  { label: 'Neighbor node (B)', start: 6.9, end: 11 },
  { label: 'Both neighbors (B, C)', start: 12.9, end: 21 },
  { label: 'Hidden and neighbor (A, B)', start: 22.9, end: 31 },

  { label: 'All (A, B, C) colliding', start: 32.9, end: 46 },

  // { label: 'Hidden terminal collision', start: 32.9, end: 35.5 },
];

const TX_COL  = [100, 160, 255]; // data — blue
const RTS_COL = [180, 100, 220]; // RTS  — purple
const CTS_COL = [240, 150,  40]; // CTS  — orange

let routerImg, compImg;
let network, baseStation, stations, globalTime, prevMillis;
let scheduleIndex, schedulePeriodStart;

function preload() {
  routerImg = loadImage('./router.png');
  compImg   = loadImage('./computer.png');
}


// ---- Network ------------------------------------------------------------

class Network {
  constructor() { this.transmissions = []; }

  register(id, startTime, duration, type = 'data') {
    let srcX = id === BASE_ID ? baseStation.x : stations[id].x;
    let srcY = id === BASE_ID ? baseStation.y : stations[id].y;
    let tx = { id, startTime, endTime: startTime + duration, ruined: false, type, srcX, srcY };
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
    this.transmissions = this.transmissions.filter(t => t.endTime > time - 0.5);
  }
}


// ---- Station ------------------------------------------------------------
// State machine:
//   IDLE → message arrives → SENSING or DIFS_WAIT
//   SENSING → channel free → DIFS_WAIT
//   DIFS_WAIT → DIFS elapsed, first clean access → RTS; after busy/collision → BACKOFF
//   BACKOFF → slots exhausted → RTS
//   RTS → locally clean → WAIT_CTS; locally ruined → DIFS_WAIT
//   WAIT_CTS → CTS received → DATA_TX; timeout → DIFS_WAIT
//   DATA_TX → sent → DIFS_WAIT (wait for ACK)
//   DIFS_WAIT/BACKOFF → ACK received → IDLE

class Station {
  constructor(cfg, id) {
    this.x     = cfg.x;
    this.y     = cfg.y;
    this.label = cfg.label;
    this.col   = cfg.col;
    this.id    = id;

    this.state         = 'IDLE';
    this.hasMessage    = false;
    this.difsTimer     = 0;
    this.backoffTimer  = 0;
    this.backoffMax    = 1;
    this.backoffPaused = false;
    this.needsBackoff  = false;
    this.transmitTimer    = 0;
    this.transmitDuration = 0;
    this.txAttempts    = 0;
    this.contentionWin = CW_MIN;
    this.networkTx     = null;
    this.navTimer      = 0;
    this.sifsTimer     = 0;
    this.ctsTimeout    = 0;
    this.history       = [];
    this.navHistory    = [];
    this.ackHistory    = [];
    this.messageRequest = [];
  }

  _setState(newState) {
    if (this.history.length > 0) {
      let last = this.history[this.history.length - 1];
      if (last.end === null) {
        last.end = globalTime;
        if (this.networkTx && (last.state === 'RTS' || last.state === 'DATA_TX')) {
          last.interferers = network.transmissions
            .filter(tx => tx.id !== this.id && tx.startTime < last.end && tx.endTime > last.start)
            .map(tx => ({ srcX: tx.srcX, srcY: tx.srcY }));
        }
      }
    }
    this.state = newState;
    const tracked = ['SENSING', 'DIFS_WAIT', 'BACKOFF', 'RTS', 'WAIT_CTS', 'DATA_TX'];
    if (tracked.includes(newState)) {
      this.history.push({ state: newState, start: globalTime, end: null });
    }
  }

  _channelBusy() {
    if (this.navTimer > 0) return true;
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

  _beginRTS() {
    this.txAttempts++;
    this._setState('RTS');
    this.networkTx        = network.register(this.id, globalTime, RTS_DURATION, 'rts');
    this.transmitTimer    = RTS_DURATION;
    this.transmitDuration = RTS_DURATION;
  }

  receiveCTS() {
    if (this.state !== 'WAIT_CTS') return;
    this._setState('SIFS_WAIT');  // not tracked in history
    this.sifsTimer = SIFS;
  }

  receiveNAV(duration) {
    if (this.state === 'DATA_TX' || this.state === 'RTS' || this.state === 'WAIT_CTS' || this.state === 'SIFS_WAIT') return;
    if (this.navTimer <= 0) {
      this.navHistory.push({ start: globalTime, end: null });
    }
    this.navTimer = max(this.navTimer, duration);
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
    this.navHistory     = this.navHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.ackHistory     = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.messageRequest = this.messageRequest.filter(t => t > globalTime - TL_WIN - 2);

    if (this.navTimer > 0) {
      this.navTimer = max(0, this.navTimer - dt);
      if (this.navTimer === 0) closeOpen(this.navHistory);
    }

    if (this.state === 'SENSING') {
      if (!this._channelBusy()) { this._retryDIFS(); }

    } else if (this.state === 'DIFS_WAIT') {
      if (this._channelBusy()) { this._setState('SENSING'); }
      else {
        this.difsTimer -= dt;
        if (this.difsTimer <= 0) { if (this.needsBackoff) this._enterBackoff(); else this._beginRTS(); }
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
        if (this.backoffTimer <= 0) this._beginRTS();
      }

    } else if (this.state === 'RTS') {
      this.transmitTimer -= dt;
      if (this.transmitTimer <= 0) {
        // Notify bystanders in range that received this RTS cleanly at their location
        let navDur = SIFS + CTS_DURATION + SIFS + DATA_DURATION + ACK_DELAY;
        for (let st of stations) {
          if (st.id === this.id) continue;
          if (dist(this.x, this.y, st.x, st.y) > COMM_RADIUS) continue;
          if (!network.isRuinedAt(this.networkTx, st.x, st.y)) st.receiveNAV(navDur);
        }
        baseStation.receiveRTS(this); // router decides independently if it heard it cleanly
        if (network.isRuinedAt(this.networkTx, this.x, this.y)) {
          // Locally detected collision — we know we failed
          let last = this.history[this.history.length - 1];
          if (last && last.end === null) last.ruined = true;
          this._retryDIFS();
        } else {
          // No local collision detected — wait for CTS (hidden terminal may still fail at router)
          this._setState('WAIT_CTS');
          this.ctsTimeout = CTS_TIMEOUT;
        }
      }

    } else if (this.state === 'WAIT_CTS') {
      this.ctsTimeout -= dt;
      if (this.ctsTimeout <= 0) this._retryDIFS();

    } else if (this.state === 'SIFS_WAIT') {
      this.sifsTimer -= dt;
      if (this.sifsTimer <= 0) {
        this._setState('DATA_TX');
        this.networkTx        = network.register(this.id, globalTime, DATA_DURATION, 'data');
        this.transmitTimer    = DATA_DURATION;
        this.transmitDuration = DATA_DURATION;
      }

    } else if (this.state === 'DATA_TX') {
      this.transmitTimer -= dt;
      if (this.transmitTimer <= 0) {
        baseStation.receiveData(this);
        this._retryDIFS();
      }
    }
  }

  draw() {
    let txCol = this.state === 'RTS' ? RTS_COL : this.state === 'DATA_TX' ? TX_COL : null;

    drawRangeCircle(this.x, this.y);

    // NAV indicator — dashed grey ring
    if (this.navTimer > 0 && !txCol) {
      push();
      noFill(); stroke(150, 150, 180, 90); strokeWeight(1.5);
      drawingContext.setLineDash([3, 4]);
      ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
      drawingContext.setLineDash([]);
      pop();
    }

    // Transmission glow ring + arrow to router
    if (txCol) {
      drawGlowRing(this.x, this.y, ...txCol);
      drawArrow(this.x, this.y, baseStation.x, baseStation.y, ...txCol);
    }

    // Computer icon
    blendMode(MULTIPLY);
    imageMode(CENTER);
    image(compImg, this.x, this.y, 33, 28);
    imageMode(CORNER);
    blendMode(BLEND);

    // Label
    push();
    textAlign(CENTER, BOTTOM); textSize(12); noStroke();
    fill(60);
    text(this.label, this.x, this.y - 22);
    pop();

    // Progress arc (RTS = purple, DATA = blue)
    if (txCol) {
      let frac = max(0, 1 - this.transmitTimer / this.transmitDuration);
      push(); noFill(); stroke(...txCol); strokeWeight(2.5);
      arc(this.x, this.y, 54, 54, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    // Backoff arc
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


// ---- BaseStation --------------------------------------------------------

class BaseStation {
  constructor(x, y) {
    this.x = x;
    this.y = y;
    this.busyWith  = null;   // stationId currently granted the channel
    this.pendingCTS  = [];
    this.pendingAcks = [];
    this.ctsHistory  = [];
    this.ackHistory  = [];
  }

  receiveRTS(station) {
    if (this.busyWith !== null) return;
    if (network.isRuinedAt(station.networkTx, this.x, this.y)) return;
    this.busyWith = station.id;
    this.ctsHistory.push({ start: globalTime + SIFS, end: null, stationId: station.id });
    this.pendingCTS.push({ stationId: station.id, timer: SIFS + CTS_DURATION });
    network.register(BASE_ID, globalTime + SIFS, CTS_DURATION, 'cts');
    // Bystander NAV is set by the sending station (location-aware); see Station.update RTS block
  }

  receiveData(station) {
    station.noteAckSent();
    this.ackHistory.push({ start: globalTime + SIFS, end: null, stationId: station.id });
    this.pendingAcks.push({ stationId: station.id, timer: ACK_DELAY });
    network.register(BASE_ID, globalTime + SIFS, ACK_DELAY - SIFS, 'ack');
  }

  update(dt) {
    this.ctsHistory = this.ctsHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.ackHistory = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);

    for (let cts of this.pendingCTS) {
      cts.timer -= dt;
      if (cts.timer <= 0) {
        closeOpen(this.ctsHistory);
        let s = stations.find(st => st.id === cts.stationId);
        if (s) {
          s.receiveCTS();
          // NAV from CTS end: SIFS (station waits) + DATA + SIFS + ACK
          let navDur = SIFS + DATA_DURATION + ACK_DELAY;
          for (let st of stations) {
            if (st.id !== cts.stationId) st.receiveNAV(navDur);
          }
        }
      }
    }
    this.pendingCTS = this.pendingCTS.filter(c => c.timer > 0);

    for (let ack of this.pendingAcks) {
      ack.timer -= dt;
      if (ack.timer <= 0) {
        closeOpen(this.ackHistory);
        let s = stations.find(st => st.id === ack.stationId);
        if (s) s.receiveAck();
        this.busyWith = null;
      }
    }
    this.pendingAcks = this.pendingAcks.filter(a => a.timer > 0);
  }

  draw() {
    let sendingCTS = this.pendingCTS.length > 0;
    let sendingACK = this.pendingAcks.length > 0;
    let [cr, cg, cb] = CTS_COL;

    if (sendingCTS) {
      drawGlowRing(this.x, this.y, cr, cg, cb);
      let target = stations.find(st => st.id === this.pendingCTS[0].stationId);
      if (target) drawArrow(this.x, this.y, target.x, target.y, cr, cg, cb);
    } else if (sendingACK) {
      drawGlowRing(this.x, this.y, 60, 190, 90);
      let target = stations.find(st => st.id === this.pendingAcks[0].stationId);
      if (target) drawArrow(this.x, this.y, target.x, target.y, 60, 190, 90);
    }

    drawRangeCircle(this.x, this.y);

    // Router icon
    blendMode(MULTIPLY);
    imageMode(CENTER);
    image(routerImg, this.x, this.y, 44, 33);
    imageMode(CORNER);
    blendMode(BLEND);

    // Progress arc — CTS (orange) or ACK (green)
    if (sendingCTS) {
      let most = this.pendingCTS.reduce((best, c) => c.timer < best.timer ? c : best);
      let frac = max(0, 1 - most.timer / CTS_DURATION);
      push(); noFill(); stroke(cr, cg, cb); strokeWeight(2.5);
      arc(this.x, this.y, 64, 64, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    } else if (sendingACK) {
      let most = this.pendingAcks.reduce((best, a) => a.timer < best.timer ? a : best);
      let frac = max(0, 1 - most.timer / ACK_DELAY);
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
  let sx = x1 + nx * 33, sy = y1 + ny * 33; // clear source icon + arc
  let ex = x2 - nx * 30, ey = y2 - ny * 30; // clear target icon
  push();
  stroke(r, g, b, 210); strokeWeight(2);
  line(sx, sy, ex - nx * 11, ey - ny * 11); // stop before arrowhead base
  fill(r, g, b, 210); noStroke();
  push();
  translate(ex, ey);
  rotate(atan2(dy, dx));
  triangle(0, 0, -13, -5, -13, 5);
  pop();
  pop();
}


// ---- p5 lifecycle -------------------------------------------------------

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
  // P5Capture.getInstance().start({ format: 'webm' });
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
  const legendBoxH = 154;
  const legendBoxY = floor((TL_Y - legendBoxH) / 2);
  let ly = legendBoxY + 6;
  let [rr, rg, rb] = RTS_COL;
  let [cr, cg, cb] = CTS_COL;
  let [tr, tg, tb] = TX_COL;

  fill(240, 240, 240, 210); stroke(90, 90, 90); strokeWeight(0.8);
  rect(2, legendBoxY, 90, legendBoxH, 6);

  fill(rr, rg, rb, 160); noStroke(); rect(lx, ly,       10, 10);
  fill(30); text('RTS',         lx + 14, ly + 5);
  fill(cr, cg, cb, 160);         noStroke(); rect(lx, ly+lh,   10, 10);
  fill(30); text('CTS',         lx + 14, ly + lh   + 5);
  fill(tr, tg, tb, 160);         noStroke(); rect(lx, ly+lh*2, 10, 10);
  fill(30); text('Data',        lx + 14, ly + lh*2 + 5);
  fill(60, 190, 90);              noStroke(); rect(lx, ly+lh*3, 10, 10);
  fill(30); text('ACK',         lx + 14, ly + lh*3 + 5);
  stroke(0); strokeWeight(1.5); line(lx+5, ly+lh*4, lx+5, ly+lh*4+10);
  fill(30); noStroke(); text('New message', lx + 14, ly + lh*4 + 5);
  stroke(0); strokeWeight(2); line(lx, ly+lh*5+5, lx+10, ly+lh*5+5);
  fill(30); noStroke(); text('Sensing',     lx + 14, ly + lh*5 + 5);
  stroke(230, 140, 30); strokeWeight(2); line(lx, ly+lh*6+5, lx+10, ly+lh*6+5);
  fill(30); noStroke(); text('DIFS wait',   lx + 14, ly + lh*6 + 5);
  stroke(210, 70, 70);  strokeWeight(2); line(lx, ly+lh*7+5, lx+10, ly+lh*7+5);
  fill(30); noStroke(); text('Backoff',     lx + 14, ly + lh*7 + 5);
  drawDashedBox(lx, ly+lh*8, 10, 10);
  fill(30); noStroke(); text('NAV',         lx + 14, ly + lh*8 + 5);
  pop();
}


// ---- Timeline -----------------------------------------------------------

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

// Draw each side independently so the dash pattern is anchored to each
// edge's start point and doesn't shift as the box width grows.
function drawDashedBox(x, y, w, h) {
  if (w <= 0 || h <= 0) return;
  drawingContext.save();
  drawingContext.strokeStyle = '#000000';
  drawingContext.lineWidth = 1.5;
  drawingContext.setLineDash([3, 4]);
  for (let [ax, ay, bx, by] of [
    [x,     y,     x + w, y    ],
    [x,     y + h, x + w, y + h],
    [x,     y,     x,     y + h],
    [x + w, y,     x + w, y + h],
  ]) {
    drawingContext.beginPath();
    drawingContext.moveTo(ax, ay);
    drawingContext.lineTo(bx, by);
    drawingContext.stroke();
  }
  drawingContext.restore();
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
  let [rr, rg, rb] = RTS_COL;
  let [cr, cg, cb] = CTS_COL;

  // Annotation lane
  let annLineY = TL_Y + 8;  // leave gap above rows
  let tickH = 4;
  for (let ann of ANNOTATIONS) {
    if (globalTime < ann.start) continue;          // don't show before time is reached
    if (ann.end < tStart || ann.start > tEnd) continue;
    let visEnd = min(ann.end, globalTime);          // line only extends to "now"
    let ax1    = map(max(ann.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
    let ax2    = map(min(visEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
    let ax1raw = map(ann.start, tStart, tEnd, TL_LX, TL_LX + TL_W);
    let ax2raw = map(ann.end,   tStart, tEnd, TL_LX, TL_LX + TL_W);
    stroke(0); strokeWeight(1); noFill();
    line(ax1, annLineY, ax2, annLineY);
    if (ann.start >= tStart)               { line(ax1, annLineY - tickH, ax1, annLineY + tickH); }
    if (ann.end <= globalTime && visEnd <= tEnd) { line(ax2, annLineY - tickH, ax2, annLineY + tickH); }
    // Label left-aligned at annotation start, clipped at "now" so it grows with the timeline
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

    // Overheard RTS/data from in-range stations — half height
    for (let src of stations) {
      if (src === s) continue;
      if (dist(s.x, s.y, src.x, src.y) > COMM_RADIUS) continue;
      for (let seg of src.history) {
        if (seg.state !== 'DATA_TX' && seg.state !== 'RTS') continue;
        let r = segToXRange(seg, tStart, tEnd);
        if (!r) continue;
        let col = seg.state === 'RTS' ? [rr, rg, rb] : [tr, tg, tb];
        drawTLBar(r.x1, r.x2, y2, h2, col, seg.end === null ? 130 : 80, seg.end === null || segRuinedAt(seg, s.x, s.y));
      }
    }

    // CTS and ACK from router — all stations hear it (half height)
    for (let seg of baseStation.ctsHistory) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let a = seg.end === null ? 130 : (seg.stationId === s.id ? 220 : 80);
      drawTLBar(r.x1, r.x2, y2, h2, [cr, cg, cb], a, seg.end === null);
    }
    for (let seg of baseStation.ackHistory) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let a = seg.end === null ? 130 : (seg.stationId === s.id ? 220 : 80);
      drawTLBar(r.x1, r.x2, y2, h2, [60, 190, 90], a, seg.end === null);
    }

    // Own segments
    for (let seg of s.history) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let { x1, x2 } = r;

      if (seg.state === 'DATA_TX') {
        drawTLBar(x1, x2, ry, TL_ROW, [tr, tg, tb], seg.end === null ? 130 : 220, false);
      } else if (seg.state === 'RTS') {
        drawTLBar(x1, x2, ry, TL_ROW, [rr, rg, rb], seg.end === null ? 130 : 220, false);
      } else if (seg.state === 'WAIT_CTS') {
        stroke(cr, cg, cb); strokeWeight(1.5); noFill();
        drawingContext.setLineDash([3, 3]);
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
        drawingContext.setLineDash([]);
      } else if (seg.state === 'SENSING') {
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

    // NAV periods — dashed box at mid-height
    for (let seg of s.navHistory) {
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      drawDashedBox(r.x1, y2, r.x2 - r.x1, h2);
    }

    // ACK segment (half height, on station row)
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

  // Incoming RTS/data shown on router row (half height)
  for (let s of stations) {
    for (let seg of s.history) {
      if (seg.state !== 'RTS' && seg.state !== 'DATA_TX') continue;
      let r = segToXRange(seg, tStart, tEnd);
      if (!r) continue;
      let col = seg.state === 'RTS' ? [rr, rg, rb] : [tr, tg, tb];
      drawTLBar(r.x1, r.x2, bry + TL_ROW / 4, TL_ROW / 2, col, seg.end === null ? 130 : 220, seg.end === null || segRuinedAt(seg, baseStation.x, baseStation.y));
    }
  }

  // CTS from router (full height, orange)
  for (let seg of baseStation.ctsHistory) {
    let r = segToXRange(seg, tStart, tEnd);
    if (!r) continue;
    drawTLBar(r.x1, r.x2, bry, TL_ROW, [cr, cg, cb], seg.end === null ? 130 : 220, seg.end === null);
  }

  // ACK from router (full height, green)
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
