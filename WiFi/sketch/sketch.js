// WiFi (Pure ALOHA) simulation
// Router (access point) sits at the centre of the canvas.
// Three computers form an equilateral triangle around it.

const PACKET_SPEED     = 110;   // px/s
const ACK_DELAY        = 0.3;   // s — router waits before sending ACK
const RAND_SEED   = 42;

// CSMA/CA timing
const DIFS        = 0.4;   // s — minimum idle time before starting backoff
const SLOT_TIME   = 0.15;  // s — duration of one backoff slot
const CW_MIN      = 7;     // initial contention window: draw from [0, CW_MIN] slots
const CW_MAX      = 63;    // maximum contention window after repeated collisions

// Layout
//   A (top):   (260,  60) — 125 px from router
//   B (bot-L): (205, 285) — 114 px from router, 110 px from C
//   C (bot-R): (315, 285) — 114 px from router, 110 px from B
//   A↔B = A↔C ≈ 232 px  →  outside COMM_RADIUS, so A is a hidden node to B/C
const BASE_POS = { x: 260, y: 185 };
const STATION_CFGS = [
  { x: 260, y: 60,  label: 'A', col: [220, 55,  55]  },
  { x: 205, y: 285, label: 'B', col: [55,  175, 75]  },
  { x: 315, y: 285, label: 'C', col: [55,  110, 215] },
];

// Stations can only sense each other's transmissions within this radius.
// B↔C (110 px) < COMM_RADIUS < A↔B (232 px), so B and C hear each other
// but A is a hidden node from their perspective.
const COMM_RADIUS = 160;

// Timeline
const TL_WIN = 20;
const TL_Y   = 350;
const TL_ROW = 14;
const TL_GAP = 4;
const TL_LX  = 78;
const TL_W   = 432;

const MESSAGE_SCHEDULE = [
  { time: 1.0,  stationId: 0 },
  { time: 5.0,  stationId: 1 },
  { time: 8.5,  stationId: 2 },
  { time: 8.9,  stationId: 1 },  // overlaps Big Island → collision
  { time: 14.0, stationId: 1 },
  { time: 14.7, stationId: 0 },
  // { time: 17.5, stationId: 2 },
];
const SCHEDULE_PERIOD = 30;

// Single color used for all transmissions in the timeline (shared wireless medium).
const TX_COL = [100, 160, 255];

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
    this.transmissions = this.transmissions.filter(t => t.endTime > time - 0.5);
  }
}


// ---- Station ------------------------------------------------------------
// CSMA/CA state machine:
//   IDLE → (message, channel free) → TRANSMITTING immediately
//   IDLE → (message, channel busy) → SENSING
//   SENSING: wait for channel idle, then → DIFS_WAIT
//   DIFS_WAIT: count down DIFS; channel goes busy → back to SENSING
//   BACKOFF: count down random slots (frozen while busy); at 0 → TRANSMITTING
//   TRANSMITTING → DIFS_WAIT (assume failure; ACK cancels into IDLE; retry doubles CW)

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
    this.backoffMax    = 1;    // used for arc display
    this.transmitTimer    = 0;
    this.transmitDuration = 0;  // initial value of transmitTimer; used for fill-arc fraction
    this.txAttempts    = 0;    // increments each TX; resets on ACK; drives CW doubling
    this.contentionWin = CW_MIN;
    this.networkTx      = null;
    this.history        = [];
    this.ackHistory     = [];
    this.messageRequest = [];  // timestamps when a new message arrives
  }

  // Close open history entry and open a new one for any tracked state.
  _setState(newState) {
    if (this.history.length > 0) {
      let last = this.history[this.history.length - 1];
      if (last.end === null) last.end = globalTime;
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
      let src = stations[tx.id];
      return dist(this.x, this.y, src.x, src.y) <= COMM_RADIUS;
    });
  }

  triggerMessage() {
    if (this.hasMessage) return;
    this.hasMessage = true;
    this.messageRequest.push(globalTime);
    if (this.state === 'IDLE') {
      if (this._channelBusy()) { this._setState('SENSING'); }
      else                     { this._beginTransmit(); }  // free → no wait needed
    }
  }

  _enterBackoff() {
    // Each call after an unacknowledged TX doubles the contention window.
    if (this.txAttempts > 0) {
      this.contentionWin = min(this.contentionWin * 2, CW_MAX);
    }
    let slots         = floor(random(0, this.contentionWin + 1));
    this.backoffMax   = this.contentionWin * SLOT_TIME;
    this.backoffTimer = slots * SLOT_TIME;
    this._setState('BACKOFF');
  }

  _beginTransmit() {
    this.txAttempts++;
    this._setState('TRANSMITTING');
    let travelTime     = dist(this.x, this.y, baseStation.x, baseStation.y) / PACKET_SPEED;
    this.networkTx        = network.register(this.id, globalTime, travelTime);
    this.transmitTimer    = travelTime;
    this.transmitDuration = travelTime;
  }

  update(dt) {
    this.history        = this.history.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.ackHistory     = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.messageRequest = this.messageRequest.filter(t => t > globalTime - TL_WIN - 2);

    if (this.state === 'SENSING') {
      if (!this._channelBusy()) { this._setState('DIFS_WAIT'); this.difsTimer = DIFS; }

    } else if (this.state === 'DIFS_WAIT') {
      if (this._channelBusy()) { this._setState('SENSING'); }
      else {
        this.difsTimer -= dt;
        if (this.difsTimer <= 0) this._enterBackoff();
      }

    } else if (this.state === 'BACKOFF') {
      if (!this._channelBusy()) {
        this.backoffTimer -= dt;
        if (this.backoffTimer <= 0) this._beginTransmit();
      }
      // timer frozen while channel is busy

    } else if (this.state === 'TRANSMITTING') {
      this.transmitTimer -= dt;
      if (this.transmitTimer <= 0) {
        if (!this.networkTx.ruined) baseStation.receivePacket(this);
        // Assume failure until ACK proves otherwise — immediately start DIFS.
        this._setState('DIFS_WAIT');
        this.difsTimer = DIFS;
      }
    }
  }

  noteAckSent() {
    this.ackHistory.push({ start: globalTime, end: null });
  }

  receiveAck() {
    // ACK can arrive during DIFS_WAIT or BACKOFF (the post-TX retry window).
    if (this.state === 'DIFS_WAIT' || this.state === 'BACKOFF' || this.state === 'SENSING') {
      let open = this.ackHistory.findLast(s => s.end === null);
      if (open) open.end = globalTime;
      this.hasMessage    = false;
      this.txAttempts    = 0;
      this.contentionWin = CW_MIN;
      this._setState('IDLE');  // closes open DIFS_WAIT or BACKOFF history entry
    }
  }

  draw() {
    let [r, g, b] = this.col;

    // Communication range circle — always visible, very faint
    push();
    noFill(); stroke(180, 180, 200, 80); strokeWeight(1);
    drawingContext.setLineDash([4, 6]);
    ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
    drawingContext.setLineDash([]);
    pop();

    // Transmission glow ring — same size as the communication range
    if (this.state === 'TRANSMITTING') {
      let [tr, tg, tb] = TX_COL;
      push();
      noStroke(); fill(tr, tg, tb, 35);
      ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
      noFill(); stroke(tr, tg, tb, 100); strokeWeight(1.5);
      ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
      pop();
    }

    // Computer icon (MULTIPLY makes white background invisible)
    blendMode(MULTIPLY);
    imageMode(CENTER);
    image(compImg, this.x, this.y, 40, 34);
    imageMode(CORNER);
    blendMode(BLEND);

    // Label above icon
    push();
    textAlign(CENTER, BOTTOM); textSize(12); noStroke();
    fill(60);
    text(this.label, this.x, this.y - 22);
    pop();

    // Transmission progress arc — fills up as the packet travels (blue)
    if (this.state === 'TRANSMITTING') {
      let [tr, tg, tb] = TX_COL;
      let frac = max(0, 1 - this.transmitTimer / this.transmitDuration);
      push(); noFill(); stroke(tr, tg, tb); strokeWeight(2.5);
      arc(this.x, this.y, 54, 54, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    // Backoff countdown arc — grey when frozen (channel busy), red when counting
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
    this.pendingAcks = [];
    this.ackHistory  = [];
  }

  receivePacket(station) {
    station.noteAckSent();
    this.ackHistory.push({ start: globalTime, end: null });
    this.pendingAcks.push({ stationId: station.id, timer: ACK_DELAY });
  }

  // Returns true if the ACK to `station` will be corrupted because another
  // in-range station is transmitting at the moment the ACK arrives.
  _ackIsLost(station) {
    return network.transmissions.some(tx => {
      if (tx.id === station.id || tx.endTime <= globalTime) return false;
      return dist(station.x, station.y, stations[tx.id].x, stations[tx.id].y) <= COMM_RADIUS;
    });
  }

  update(dt) {
    this.ackHistory = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    for (let ack of this.pendingAcks) {
      ack.timer -= dt;
      if (ack.timer <= 0) {
        let open = this.ackHistory.findLast(s => s.end === null);
        if (open) open.end = globalTime;
        let s = stations.find(st => st.id === ack.stationId);
        if (s) {
          if (!this._ackIsLost(s)) {
            s.receiveAck();
          } else {
            // ACK collided — close the station's pending ack segment without delivering it.
            let sAck = s.ackHistory.findLast(seg => seg.end === null);
            if (sAck) sAck.end = globalTime;
          }
        }
      }
    }
    this.pendingAcks = this.pendingAcks.filter(a => a.timer > 0);
  }

  draw() {
    // Green glow when sending ACKs
    if (this.pendingAcks.length > 0) {
      push();
      noStroke(); fill(60, 190, 90, 35);
      ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
      noFill(); stroke(60, 190, 90, 100); strokeWeight(1.5);
      ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
      pop();
    }

    // Communication range circle — matches station style
    push();
    noFill(); stroke(180, 180, 200, 80); strokeWeight(1);
    drawingContext.setLineDash([4, 6]);
    ellipse(this.x, this.y, COMM_RADIUS * 2, COMM_RADIUS * 2);
    drawingContext.setLineDash([]);
    pop();

    // Router icon
    blendMode(MULTIPLY);
    imageMode(CENTER);
    image(routerImg, this.x, this.y, 54, 40);
    imageMode(CORNER);
    blendMode(BLEND);

    // ACK progress arc — fills up as the ACK delay counts down (green)
    if (this.pendingAcks.length > 0) {
      let mostProgress = this.pendingAcks.reduce((best, a) => a.timer < best.timer ? a : best);
      let frac = max(0, 1 - mostProgress.timer / ACK_DELAY);
      push(); noFill(); stroke(60, 190, 90); strokeWeight(2.5);
      arc(this.x, this.y, 64, 64, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    // Label
    push();
    textAlign(CENTER, BOTTOM); textSize(11); noStroke();
    fill(80);
    text('Router', this.x, this.y - 25);
    pop();
  }
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
    let s = stations[msg.stationId];
    s.triggerMessage();
    scheduleIndex++;
  }
  if (scheduleIndex >= MESSAGE_SCHEDULE.length) {
    scheduleIndex       = 0;
    schedulePeriodStart += SCHEDULE_PERIOD;
  }

  // Draw lines first (behind everything), then base, then stations
  for (let s of stations) s.draw();
  baseStation.draw();

  drawTimeline();

  // Legend
  push();
  textSize(10); textAlign(LEFT, CENTER);
  let lx = width - 148, ly = 10;
  const lh = 16;
  fill(100, 160, 255, 160); noStroke(); rect(lx, ly,       10, 10);
  fill(30); text('Data', lx + 14, ly + 5);
  fill(60, 190, 90);          noStroke(); rect(lx, ly+lh,   10, 10);
  fill(30); text('ACK',          lx + 14, ly + lh  + 5);
  stroke(120); strokeWeight(1.5); line(lx+5, ly+lh*2, lx+5, ly+lh*2+10);
  fill(30); noStroke(); text('New message', lx + 14, ly + lh*2 + 5);
  stroke(160); strokeWeight(2); line(lx, ly+lh*3+5, lx+10, ly+lh*3+5);
  fill(30); noStroke(); text('Sensing',      lx + 14, ly + lh*3 + 5);
  stroke(230, 140, 30); strokeWeight(2); line(lx, ly+lh*4+5, lx+10, ly+lh*4+5);
  fill(30); noStroke(); text('DIFS wait',    lx + 14, ly + lh*4 + 5);
  stroke(210, 70, 70);  strokeWeight(2); line(lx, ly+lh*5+5, lx+10, ly+lh*5+5);
  fill(30); noStroke(); text('Backoff',      lx + 14, ly + lh*5 + 5);
  pop();
}


// ---- Timeline -----------------------------------------------------------

function drawTimeline() {
  let tEnd   = max(TL_WIN, globalTime);
  let tStart = tEnd - TL_WIN;
  let rows   = stations.length + 1;
  let totalH = rows * (TL_ROW + TL_GAP) + 18;

  push();
  fill(245); noStroke();
  rect(0, TL_Y - 8, width, totalH + 8);
  stroke(190); strokeWeight(1);
  line(0, TL_Y - 9, width, TL_Y - 9);
  pop();

  push();
  textSize(9);

  let [tr, tg, tb] = TX_COL;

  for (let i = 0; i < stations.length; i++) {
    let s   = stations[i];
    let ry  = TL_Y + i * (TL_ROW + TL_GAP);
    let [r, g, b] = s.col;

    fill(228); noStroke(); rect(TL_LX, ry, TL_W, TL_ROW);

    // Overheard transmissions from in-range stations — half height, centred in row.
    for (let src of stations) {
      if (src === s) continue;
      if (dist(s.x, s.y, src.x, src.y) > COMM_RADIUS) continue;
      for (let seg of src.history) {
        if (seg.state !== 'TRANSMITTING') continue;
        let segEnd = seg.end === null ? globalTime : seg.end;
        if (segEnd < tStart) continue;
        let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
        let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
        if (x2 <= x1) continue;
        fill(tr, tg, tb, 110); stroke(tr * 0.6, tg * 0.6, tb * 0.6); strokeWeight(1);
        rect(x1, ry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
      }
    }

    // Own transmission — full height.
    for (let seg of s.history) {
      if (seg.state !== 'TRANSMITTING') continue;
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(tr, tg, tb, 160); stroke(tr * 0.6, tg * 0.6, tb * 0.6); strokeWeight(1);
      rect(x1, ry, x2 - x1, TL_ROW);
    }

    // Pre-TX phases — drawn from history so past durations are visible.
    // Sensing (waiting for airwaves to clear): grey line
    // DIFS (mandatory inter-frame gap):        orange line
    // Backoff (random slot countdown):         red line
    for (let seg of s.history) {
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      noFill();
      if (seg.state === 'SENSING') {
        stroke(160); strokeWeight(1.5);
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      } else if (seg.state === 'DIFS_WAIT') {
        stroke(230, 140, 30); strokeWeight(1.5);
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      } else if (seg.state === 'BACKOFF') {
        stroke(210, 70, 70); strokeWeight(1.5);
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      }
    }

    // Message-arrival tick — grey vertical line when the node first wants to send
    for (let t of s.messageRequest) {
      if (t < tStart || t > tEnd) continue;
      let tx = map(t, tStart, tEnd, TL_LX, TL_LX + TL_W);
      stroke(120); strokeWeight(1.5); noFill();
      line(tx, ry, tx, ry + TL_ROW);
    }

    // ACK from router — all stations hear it (half height)
    for (let seg of baseStation.ackHistory) {
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(60, 190, 90, 110); stroke(30, 140, 60); strokeWeight(1);
      rect(x1, ry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
    }

    // ACK — only shown on the station the ACK is addressed to
    for (let seg of s.ackHistory) {
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(60, 190, 90, 160); stroke(30, 140, 60); strokeWeight(1);
      rect(x1, ry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
    }

    fill(60); noStroke(); textAlign(RIGHT, CENTER);
    text(s.label, TL_LX - 4, ry + TL_ROW / 2);
  }

  // Base station row
  let bry = TL_Y + stations.length * (TL_ROW + TL_GAP);
  fill(195); noStroke(); rect(TL_LX, bry, TL_W, TL_ROW);

  for (let s of stations) {
    for (let seg of s.history) {
      if (seg.state !== 'TRANSMITTING') continue;
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(tr, tg, tb, 140); stroke(tr * 0.6, tg * 0.6, tb * 0.6); strokeWeight(1);
      rect(x1, bry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
    }
  }

  for (let seg of baseStation.ackHistory) {
    let segEnd = seg.end === null ? globalTime : seg.end;
    if (segEnd < tStart) continue;
    let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
    let x2 = map(min(segEnd, tEnd),      tStart, tEnd, TL_LX, TL_LX + TL_W);
    if (x2 <= x1) continue;
    fill(60, 190, 90, 160); stroke(30, 140, 60); strokeWeight(1);
    rect(x1, bry, x2 - x1, TL_ROW);
  }

  fill(50); noStroke(); textAlign(RIGHT, CENTER);
  text('Router', TL_LX - 4, bry + TL_ROW / 2);

  // Now-marker
  let nowX = map(globalTime, tStart, tEnd, TL_LX, TL_LX + TL_W);
  stroke(140); strokeWeight(1);
  line(nowX, TL_Y, nowX, bry + TL_ROW);

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
