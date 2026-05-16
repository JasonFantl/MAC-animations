// Pure ALOHA simulation on a Hawaii map
//
// Each user station = cell tower on an island with a range circle.
// Base station (Oahu) receives uplink packets and sends ACKs on the downlink.
// Network detects collisions via overlapping transmission time intervals.

const PACKET_SPEED  = 110;   // px/s (travel time drives network timing)
const ACK_DELAY     = 0.3;   // seconds the base station waits before delivering ACK
const RANGE_RADIUS  = 220;   // px — visual radio range circle

// Map image is 500×500; drawn at (MAP_X, MAP_Y) on the canvas.
const MAP_X = 0, MAP_Y = 0;

// Island center positions within the 500×500 map
const BASE_MAP_POS = { x: 215, y: 145 };  // Oahu — base station
const ISLAND_POSITIONS = [
  { x: 91,  y: 70,  label: 'A'       },
  { x: 306, y: 195, label: 'B'        },
  { x: 356, y: 235, label: 'C'  },
];

// Timeline layout constants
const TL_WIN  = 20;   // seconds of history shown
const TL_Y    = 350;  // top of timeline area
const TL_ROW  = 14;   // row height px
const TL_GAP  = 4;    // gap between rows px
const TL_LX   = 78;   // x where timeline bars start (after labels)
const TL_W    = 432;  // width of timeline bar area

// Reproducible randomness — backoff delays are seeded so every run is identical.
const RAND_SEED        = 42;
const BACKOFF_MEAN_SEC = 1.5;  // mean of the exponential backoff distribution (seconds)

// Inverse-transform sample from Exponential(1/mean).
function expRandom(mean) {
  return -Math.log(max(1e-6, random())) * mean;
}

// Fixed message schedule. Times are seconds from the start of each period.
// Stations: 0 = Kauai, 1 = Maui, 2 = Big Island
const MESSAGE_SCHEDULE = [
  { time: 1.0,  stationId: 0 },

  { time: 5.0,  stationId: 1 },
  { time: 5.1,  stationId: 2 },

  { time: 13.0,  stationId: 1 },  // overlaps with Big Island → collision
  { time: 13.2, stationId: 0 },
  { time: 14.0, stationId: 2 },
];
const SCHEDULE_PERIOD = 35;  // seconds before the schedule repeats

let mapImg, towerImg;
let network, baseStation, stations, globalTime, prevMillis;
let scheduleIndex, schedulePeriodStart;

function preload() {
  mapImg   = loadImage('./hawaiian-island-map-outline-vector-55378863.webp');
  towerImg = loadImage('./cell-tower-icon.jpg');
}


// ---- Network ------------------------------------------------------------
// Tracks UPLINK transmissions only (station → base, shared frequency).
// ACK signals travel on a separate downlink frequency and are never registered
// here — they cannot collide with uplink traffic or with each other.
// When a new uplink transmission overlaps any existing one, both are immediately
// marked ruined; the base station will not deliver either.

class Network {
  constructor() {
    this.transmissions = [];
  }

  // Only call this for uplink transmissions. Never call for ACKs.
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
// States: IDLE → TRANSMITTING → BACKOFF → … (BACKOFF canceled by ACK → IDLE)

class Station {
  constructor(mapX, mapY, id, label) {
    this.x     = MAP_X + mapX;
    this.y     = MAP_Y + mapY;
    this.id    = id;
    this.label = label;

    this.state            = 'IDLE';
    this.backoffTimer     = 0;
    this.backoffMax       = 1;
    this.transmitTimer    = 0;
    this.transmitDuration = 0;

    this.networkTx  = null;  // transmission record from Network
    this.history    = [];    // [{state, start, end}] for timeline
    this.ackHistory = [];    // [{start, end}] for in-flight ACK segments
  }

  // Set state and record segment for timeline-tracked states.
  _setState(newState) {
    if (this.history.length > 0) {
      let last = this.history[this.history.length - 1];
      if (last.end === null) last.end = globalTime;
    }
    this.state = newState;
    if (newState === 'TRANSMITTING' || newState === 'BACKOFF') {
      this.history.push({ state: newState, start: globalTime, end: null });
    }
  }

  update(dt) {
    this.history    = this.history.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);
    this.ackHistory = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);

    if (this.state === 'TRANSMITTING') {
      this.transmitTimer -= dt;
      if (this.transmitTimer <= 0) {
        if (!this.networkTx.ruined) {
          baseStation.receivePacket(this);
        }
        let bo = max(ACK_DELAY, expRandom(BACKOFF_MEAN_SEC));
        this.backoffMax = bo; this.backoffTimer = bo;
        this._setState('BACKOFF');
      }

    } else if (this.state === 'BACKOFF') {
      this.backoffTimer -= dt;
      if (this.backoffTimer <= 0) this._beginTransmit();
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
    this.ackHistory.push({ start: globalTime, end: null });
  }

  // Called when an ACK arrives on the separate downlink channel.
  // ACKs always go through, so honour the receipt from any active state.
  receiveAck() {
    if (this.state === 'BACKOFF') {
      let open = this.ackHistory.findLast(s => s.end === null);
      if (open) open.end = globalTime;
      this._setState('IDLE');
    }
  }

  draw() {
    // Communication range circle — always visible, very faint
    push();
    noFill(); stroke(180, 180, 200, 80); strokeWeight(1);
    drawingContext.setLineDash([4, 6]);
    ellipse(this.x, this.y, RANGE_RADIUS * 2, RANGE_RADIUS * 2);
    drawingContext.setLineDash([]);
    pop();

    // Large range circle — visible only while actively transmitting
    if (this.state === 'TRANSMITTING') {
      push();
      noStroke(); fill(100, 160, 255, 35);
      ellipse(this.x, this.y, RANGE_RADIUS * 2, RANGE_RADIUS * 2);
      noFill(); stroke(100, 160, 255, 90); strokeWeight(1.5);
      ellipse(this.x, this.y, RANGE_RADIUS * 2, RANGE_RADIUS * 2);
      pop();
    }

    // Tower icon (JPEG, white bg — MULTIPLY makes white invisible on ocean-blue)
    blendMode(MULTIPLY);
    image(towerImg, this.x - 12, this.y - 20, 24, 30);
    blendMode(BLEND);

    // Island label
    push();
    textAlign(CENTER, BOTTOM); textSize(10); noStroke(); fill(30);
    text(this.label, this.x, this.y - 22);
    pop();

    // Transmission progress dial — fills up as packet travels (blue)
    if (this.state === 'TRANSMITTING') {
      let frac = max(0, 1 - this.transmitTimer / this.transmitDuration);
      push(); noFill(); stroke(100, 160, 255); strokeWeight(2.5);
      arc(this.x, this.y, 48, 48, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }

    // Backoff countdown dial — empties as backoff expires (red)
    if (this.state === 'BACKOFF') {
      let frac = this.backoffTimer / this.backoffMax;
      push(); noFill(); stroke(210, 70, 70); strokeWeight(2.5);
      arc(this.x, this.y, 48, 48, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }
  }
}


// ---- BaseStation --------------------------------------------------------
// Central hub on Oahu. Receives uplink packets; sends ACKs after ACK_DELAY.

class BaseStation {
  constructor(mapX, mapY) {
    this.x = MAP_X + mapX;
    this.y = MAP_Y + mapY;
    this.pendingAcks = [];  // [{stationId, timer}]
    this.ackHistory  = [];  // [{start, end}] when ACK signals are in flight
  }

  receivePacket(station) {
    station.noteAckSent();
    this.ackHistory.push({ start: globalTime, end: null });
    this.pendingAcks.push({ stationId: station.id, timer: ACK_DELAY });
  }

  update(dt) {
    this.ackHistory = this.ackHistory.filter(s => s.end === null || s.end > globalTime - TL_WIN - 2);

    for (let ack of this.pendingAcks) {
      ack.timer -= dt;
      if (ack.timer <= 0) {
        let open = this.ackHistory.findLast(s => s.end === null);
        if (open) open.end = globalTime;
        let s = stations.find(st => st.id === ack.stationId);
        if (s) s.receiveAck();
      }
    }
    this.pendingAcks = this.pendingAcks.filter(a => a.timer > 0);
  }

  draw() {
    // Communication range circle — always visible, very faint
    push();
    noFill(); stroke(180, 180, 200, 80); strokeWeight(1);
    drawingContext.setLineDash([4, 6]);
    ellipse(this.x, this.y, RANGE_RADIUS * 2.2, RANGE_RADIUS * 2.2);
    drawingContext.setLineDash([]);
    pop();

    // Green range circle while processing incoming messages
    if (this.pendingAcks.length > 0) {
      push();
      noStroke(); fill(60, 190, 90, 35);
      ellipse(this.x, this.y, RANGE_RADIUS * 2.2, RANGE_RADIUS * 2.2);
      noFill(); stroke(60, 190, 90, 100); strokeWeight(1.5);
      ellipse(this.x, this.y, RANGE_RADIUS * 2.2, RANGE_RADIUS * 2.2);
      pop();
    }

    // Larger tower icon for the base station
    blendMode(MULTIPLY);
    image(towerImg, this.x - 22, this.y - 40, 44, 54);
    blendMode(BLEND);

    // Label
    push();
    textAlign(CENTER, BOTTOM); textSize(10); noStroke(); fill(30);
    text('Base Station', this.x, this.y - 44);
    pop();

    // ACK progress dial — fills up as the ACK delay counts down (green)
    if (this.pendingAcks.length > 0) {
      let mostProgress = this.pendingAcks.reduce((best, a) => a.timer < best.timer ? a : best);
      let frac = max(0, 1 - mostProgress.timer / ACK_DELAY);
      push(); noFill(); stroke(60, 190, 90); strokeWeight(2.5);
      arc(this.x, this.y, 64, 64, -HALF_PI, -HALF_PI + TWO_PI * frac);
      pop();
    }
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
  baseStation = new BaseStation(BASE_MAP_POS.x, BASE_MAP_POS.y);
  stations    = ISLAND_POSITIONS.map((pos, i) => new Station(pos.x, pos.y, i, pos.label));
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
  let dt = min((now - prevMillis) / 1000, 0.05);
  prevMillis = now;
  globalTime += dt;

  // Ocean background — MULTIPLY on the map will replace white with this color
  background(255);

  // Map outline: MULTIPLY blend makes white → ocean blue, black lines stay dark
  // blendMode(MULTIPLY);
  image(mapImg, MAP_X, MAP_Y, 500, 500);
  // blendMode(BLEND);

  // Update all objects
  network.prune(globalTime);
  baseStation.update(dt);
  for (let s of stations) s.update(dt);

  // Fire scheduled messages
  while (scheduleIndex < MESSAGE_SCHEDULE.length) {
    let msg      = MESSAGE_SCHEDULE[scheduleIndex];
    let fireTime = schedulePeriodStart + msg.time;
    if (globalTime < fireTime) break;
    let s = stations[msg.stationId];
    if (s.state === 'IDLE') s._beginTransmit();
    scheduleIndex++;
  }
  // Advance to next period once all messages in this period are scheduled
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
  let lx = width - 148, ly = 14;
  const lh = 16;
  fill(100, 160, 255, 160); noStroke(); rect(lx, ly,       10, 10);
  fill(30); text('Data', lx + 14, ly + 5);
  fill(60, 190, 90);          noStroke(); rect(lx, ly+lh,   10, 10);
  fill(30); text('ACK',          lx + 14, ly + lh  + 5);
  stroke(210, 70, 70); strokeWeight(2); line(lx, ly+lh*2+5, lx+10, ly+lh*2+5);
  fill(30); noStroke(); text('Backoff',      lx + 14, ly + lh*2 + 5);
  pop();
}

// ---- Timeline -----------------------------------------------------------
// Scrolling Gantt-style diagram showing each station's state over time,
// plus a base-station row indicating collisions vs clean receives.

function drawTimeline() {
  let tEnd   = max(TL_WIN, globalTime);
  let tStart = tEnd - TL_WIN;
  let rows   = stations.length + 1;   // stations + base
  let totalH = rows * (TL_ROW + TL_GAP) + 18;  // +18 for time axis

  // Background panel
  push();
  fill(245); noStroke();
  rect(0, TL_Y - 8, width, totalH + 8);
  pop();

  // Section divider
  push(); stroke(190); strokeWeight(1); line(0, TL_Y - 9, width, TL_Y - 9); pop();

  push();
  textSize(9);

  // Station rows
  for (let i = 0; i < stations.length; i++) {
    let s  = stations[i];
    let ry = TL_Y + i * (TL_ROW + TL_GAP);

    fill(228); noStroke(); rect(TL_LX, ry, TL_W, TL_ROW);

    for (let seg of s.history) {
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;

      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd,    tEnd),   tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;

      if (seg.state === 'TRANSMITTING') {
        fill(100, 160, 255, 160); stroke(60, 120, 220); strokeWeight(1);
        rect(x1, ry, x2 - x1, TL_ROW);
      } else if (seg.state === 'BACKOFF') {
        stroke(210, 70, 70); strokeWeight(1.5); noFill();
        line(x1, ry + TL_ROW / 2, x2, ry + TL_ROW / 2);
      }
    }

    // ACK from base station — all stations hear it (half height)
    for (let seg of baseStation.ackHistory) {
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd,    tEnd),   tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(60, 190, 90, 110); stroke(30, 140, 60); strokeWeight(1);
      rect(x1, ry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
    }

    // ACK received — half height, centered, semi-transparent green + solid outline
    for (let seg of s.ackHistory) {
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd,    tEnd),   tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(60, 190, 90, 160); stroke(30, 140, 60); strokeWeight(1);
      rect(x1, ry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
    }

    fill(50); noStroke(); textAlign(RIGHT, CENTER);
    text(s.label, TL_LX - 4, ry + TL_ROW / 2);
  }

  // Base station row — darker background to distinguish it from station rows
  let bry = TL_Y + stations.length * (TL_ROW + TL_GAP);
  fill(195); noStroke(); rect(TL_LX, bry, TL_W, TL_ROW);

  // Incoming transmissions — half height, semi-transparent light blue + outline
  for (let s of stations) {
    for (let seg of s.history) {
      if (seg.state !== 'TRANSMITTING') continue;
      let segEnd = seg.end === null ? globalTime : seg.end;
      if (segEnd < tStart) continue;
      let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
      let x2 = map(min(segEnd,    tEnd),   tStart, tEnd, TL_LX, TL_LX + TL_W);
      if (x2 <= x1) continue;
      fill(100, 170, 255, 140); stroke(60, 120, 220); strokeWeight(1);
      rect(x1, bry + TL_ROW / 4, x2 - x1, TL_ROW / 2);
    }
  }

  // Outgoing ACK signals — full height, semi-transparent green + solid outline
  for (let seg of baseStation.ackHistory) {
    let segEnd = seg.end === null ? globalTime : seg.end;
    if (segEnd < tStart) continue;
    let x1 = map(max(seg.start, tStart), tStart, tEnd, TL_LX, TL_LX + TL_W);
    let x2 = map(min(segEnd,    tEnd),   tStart, tEnd, TL_LX, TL_LX + TL_W);
    if (x2 <= x1) continue;
    fill(60, 190, 90, 160); stroke(30, 140, 60); strokeWeight(1);
    rect(x1, bry, x2 - x1, TL_ROW);
  }

  fill(50); noStroke(); textAlign(RIGHT, CENTER);
  text('Base', TL_LX - 4, bry + TL_ROW / 2);

  // Current-time marker
  let nowX = map(globalTime, tStart, tEnd, TL_LX, TL_LX + TL_W);
  stroke(140); strokeWeight(1);
  line(nowX, TL_Y, nowX, bry + TL_ROW);

  // Time axis — tick every 5 s
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
