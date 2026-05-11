/**
 * TheGunshots – game.js
 * Multiplayer tactical shooter built with pixi.js v7 + PeerJS
 *
 * Controls (desktop):  WASD move · mouse aim · left-click shoot · E interact door
 * Controls (mobile):   left joystick move · right joystick aim · shoot button · interact button
 */
(function () {
  'use strict';

  // ── Lock viewport dimensions so mobile nav-bar changes never reflow the layout ──
  (function lockAppDimensions() {
    const setDims = () => {
      document.documentElement.style.setProperty('--app-h', window.innerHeight + 'px');
      document.documentElement.style.setProperty('--app-w', window.innerWidth + 'px');
    };
    setDims();
    // Only update on real orientation changes, not on nav-bar show/hide
    if (screen.orientation) {
      screen.orientation.addEventListener('change', () => setTimeout(setDims, 300));
    } else {
      window.addEventListener('orientationchange', () => setTimeout(setDims, 300));
    }
  })();

  // ─────────────────────────────────────────────────────────────────────────
  // CONSTANTS
  // ─────────────────────────────────────────────────────────────────────────
  const TS = 40;          // tile size (px)
  let   MW = 34;          // map width  (tiles) – configurable via waiting room
  let   MH = 22;          // map height (tiles) – configurable via waiting room

  // Map size presets for the waiting room settings panel
  const MAP_SIZES = {
    small:  { w: 24, h: 16 },
    medium: { w: 34, h: 22 },
    large:  { w: 46, h: 30 },
  };

  const T = { WALL: 0, FLOOR: 1, DOOR: 2 };

  const FOV_DIST  = 270;           // max ray length (px)
  const FOV_HALF  = Math.PI / 3;   // half-cone = 60° → full cone = 120°
  const N_RAYS    = 180;           // rays per frame
  const AMB_R     = 52;            // ambient-glow radius (px)

  const P_SPD     = 165;           // player speed (px/s)
  const P_RAD     = 11;            // player body radius (px)
  const DOOR_D    = 54;            // max door-interaction distance (px)
  const SYNC_MS   = 80;            // state-sync interval (ms)
  const IND_TTL   = 2.5;           // shot-indicator time-to-live (s)
  const SOUND_RANGE    = 380;      // max distance to hear footsteps / shots (px)
  const SOUND_TTL      = 1.8;      // sound-arc indicator time-to-live (s)
  const SOUND_ARC_R    = 88;       // radius of sound arc from screen centre (px)
  const SOUND_ARC_HALF = Math.PI / 7; // ±~26° half-width of sound arc
  const SOUND_TIP_OFFSET = 6;     // inward offset of the arc's direction dot (px)
  const RESPAWN_S = 3.5;           // respawn delay (s)
  const MAX_HP    = 100;
  const MAG_SIZE  = 8;             // bullets per magazine
  const RELOAD_S  = 1.4;           // reload time (s)
  const RESPAWN_MS = RESPAWN_S * 1000;
  const RELOAD_MS  = RELOAD_S * 1000;
  const NET_MAX_STEP = P_SPD * (SYNC_MS / 1000) * 2.4;
  const NET_STEP_TOLERANCE = 1.75;
  const SHOT_POS_EPS = 56;

  // ── Joystick constants ────────────────────────────────────────────────
  const JOY_DEAD_ZONE = 8;         // minimum joystick offset to register input (px)
  const JOY_MAX_R     = 60;        // joystick offset for full-speed movement (px)

  // ── Bot constants ─────────────────────────────────────────────────────
  const BOT_SPD       = 110;       // bot movement speed (px/s)
  const BOT_SHOOT_CD  = 1.8;       // seconds between bot shots
  const BOT_SIGHT     = 280;       // bot detection radius (px)
  const BOT_AIM_TOL   = Math.PI / 5; // ±36° aim tolerance before bot shoots
  const MAX_PLAYERS   = 8;         // max total players (humans + bots) per room
  const FFA_KILL_LIMIT = 12;
  const TEAM_KILL_LIMIT = 24;

  const C = {
    FLOOR:    0x252525,
    FLOOR_LN: 0x2d2d2d,
    WALL:     0x564535,
    WALL_TOP: 0x7a6448,
    DOOR_CL:  0x9B6E3E,
    DOOR_OP:  0x3c1e08,
    SELF:     0x44ff88,
    ENEMY:    0xff5533,
    BOT:      0xff9922,   // orange – distinct from human enemy (red)
    TEAM_A:   0x44aaff,   // blue – team A ally
    TEAM_B:   0xff4433,   // red  – team B enemy
    DEAD_P:   0x555555,
    BULLET:   0xFFFF55,
    IND:      0xff2222,
    SOUND_IND:0xffaa22,   // orange arc for footstep / nearby sound
    HP_BG:    0x2a2a2a,
    HP_FG:    0x44ee44,
    HP_LOW:   0xee4422,
  };

  // Selector for interactive UI elements that should not have touch events intercepted
  const INTERACTIVE_SELECTOR = 'button, input, a';

  // Selector for scrollable containers that need native touch-scroll to work
  const SCROLLABLE_SELECTOR = '.wr-col, #wr-players, #hud-match-end';

  // Maximum pixel height change that can be attributed to a mobile nav-bar appearing
  // (genuine resizes such as orientation changes are larger)
  const MAX_NAVBAR_HEIGHT_CHANGE = 200;

  // ─────────────────────────────────────────────────────────────────────────
  // UTILITIES
  // ─────────────────────────────────────────────────────────────────────────

  function mkRng(seed) {
    let s = (seed ^ 0xdeadbeef) >>> 0;
    return () => {
      s ^= s << 13; s ^= s >> 17; s ^= s << 5;
      return (s >>> 0) / 0x100000000;
    };
  }

  function dist2(ax, ay, bx, by) {
    const dx = bx - ax, dy = by - ay;
    return dx * dx + dy * dy;
  }

  function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }

  function randomSeed() { return (Math.random() * 0xFFFFFF | 0) + 1; }

  // Fisher-Yates in-place shuffle (mutates and returns the array)
  function shuffleArray(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  function normalizeAngle(a) {
    while (a >  Math.PI) a -= 2 * Math.PI;
    while (a < -Math.PI) a += 2 * Math.PI;
    return a;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // MAP GENERATION
  // ─────────────────────────────────────────────────────────────────────────

  function generateMap(seed) {
    const rng   = mkRng(seed);
    const tiles = Array.from({ length: MH }, () => new Uint8Array(MW)); // all WALL (0)
    const rooms = [];
    const doors = [];

    function carve(x, y) {
      if (x > 0 && x < MW - 1 && y > 0 && y < MH - 1) tiles[y][x] = T.FLOOR;
    }

    function tryRoom(x, y, w, h) {
      if (x < 1 || y < 1 || x + w >= MW - 1 || y + h >= MH - 1) return false;
      for (const r of rooms) {
        if (x - 1 <= r.x + r.w && x + w + 1 >= r.x &&
            y - 1 <= r.y + r.h && y + h + 1 >= r.y) return false;
      }
      rooms.push({ x, y, w, h });
      for (let ry = y; ry < y + h; ry++)
        for (let rx = x; rx < x + w; rx++)
          tiles[ry][rx] = T.FLOOR;
      return true;
    }

    // Place rooms
    for (let i = 0; i < 28; i++) {
      const w = 4 + Math.floor(rng() * 6);
      const h = 3 + Math.floor(rng() * 4);
      tryRoom(
        1 + Math.floor(rng() * (MW - w - 2)),
        1 + Math.floor(rng() * (MH - h - 2)),
        w, h
      );
    }

    if (rooms.length < 2) {
      // Fallback: two fixed rooms + a corridor
      tryRoom(2, 2, 6, 5);
      tryRoom(14, 10, 7, 5);
    }

    // Connect rooms with L-shaped corridors
    for (let i = 1; i < rooms.length; i++) {
      const a = rooms[i - 1], b = rooms[i];
      let x = Math.floor(a.x + a.w / 2);
      let y = Math.floor(a.y + a.h / 2);
      const ex = Math.floor(b.x + b.w / 2);
      const ey = Math.floor(b.y + b.h / 2);
      while (x !== ex) { carve(x, y); x += x < ex ? 1 : -1; }
      while (y !== ey) { carve(x, y); y += y < ey ? 1 : -1; }
      carve(x, y);
    }

    // Add doors in narrow corridors
    for (let y = 1; y < MH - 1; y++) {
      for (let x = 1; x < MW - 1; x++) {
        if (tiles[y][x] !== T.FLOOR || rng() > 0.065) continue;
        const wN = tiles[y - 1][x], wS = tiles[y + 1][x];
        const wE = tiles[y][x + 1], wW = tiles[y][x - 1];
        const horiz = wN === T.WALL && wS === T.WALL && wE === T.FLOOR && wW === T.FLOOR;
        const vert  = wE === T.WALL && wW === T.WALL && wN === T.FLOOR && wS === T.FLOOR;
        if (horiz || vert) {
          tiles[y][x] = T.DOOR;
          doors.push({ x, y, open: false });
        }
      }
    }

    const spawns = rooms.map(r => ({
      x: (r.x + r.w / 2) * TS,
      y: (r.y + r.h / 2) * TS,
    }));

    return { tiles, doors, rooms, spawns, seed };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // RAYCASTING / FOV
  // ─────────────────────────────────────────────────────────────────────────

  function castRay(map, ox, oy, angle) {
    const { tiles, doors } = map;
    const dx = Math.cos(angle);
    const dy = Math.sin(angle);
    const adx = Math.abs(dx) || 1e-10;
    const ady = Math.abs(dy) || 1e-10;

    let mx = Math.floor(ox / TS);
    let my = Math.floor(oy / TS);
    if (mx < 0 || mx >= MW || my < 0 || my >= MH) return { x: ox, y: oy, dist: 0 };

    const ddx = TS / adx;
    const ddy = TS / ady;
    let sdx = dx < 0 ? (ox - mx * TS) / adx : ((mx + 1) * TS - ox) / adx;
    let sdy = dy < 0 ? (oy - my * TS) / ady : ((my + 1) * TS - oy) / ady;
    const stX = dx < 0 ? -1 : 1;
    const stY = dy < 0 ? -1 : 1;

    let dist = 0;
    for (let i = 0; i < 256; i++) {
      if (sdx < sdy) { dist = sdx; sdx += ddx; mx += stX; }
      else           { dist = sdy; sdy += ddy; my += stY; }
      if (dist >= FOV_DIST) { dist = FOV_DIST; break; }
      if (mx < 0 || mx >= MW || my < 0 || my >= MH) break;
      const t = tiles[my][mx];
      if (t === T.WALL) break;
      if (t === T.DOOR) {
        const d = doors.find(d => d.x === mx && d.y === my);
        if (!d || !d.open) break;
      }
    }

    dist = Math.min(dist, FOV_DIST);
    return { x: ox + dx * dist, y: oy + dy * dist, dist };
  }

  // Returns flat [x0,y0, x1,y1, ...] polygon points in world-space
  function buildFovPoly(map, px, py, angle) {
    const pts = [];
    for (let i = 0; i <= N_RAYS; i++) {
      const a = angle - FOV_HALF + (i / N_RAYS) * FOV_HALF * 2;
      const h = castRay(map, px, py, a);
      pts.push(h.x, h.y);
    }
    return pts;
  }

  // Returns true if target is within the observer's FOV cone and has line-of-sight
  function isInFov(map, obs, target) {
    const dx = target.x - obs.x, dy = target.y - obs.y;
    const dist = Math.hypot(dx, dy);
    if (dist > FOV_DIST + P_RAD) return false;
    const angleTo = Math.atan2(dy, dx);
    const diff = Math.abs(normalizeAngle(angleTo - obs.angle));
    if (diff > FOV_HALF) return false;
    // Line-of-sight: ray must reach at least as far as the target's body edge
    const ray = castRay(map, obs.x, obs.y, angleTo);
    return ray.dist >= dist - P_RAD;
  }

  // ─────────────────────────────────────────────────────────────────────────
  // AUDIO  (Web Audio API – procedural)
  // ─────────────────────────────────────────────────────────────────────────

  let _ac = null;
  function getAC() {
    return _ac || (_ac = new (window.AudioContext || window.webkitAudioContext)());
  }

  function playShot(local) {
    try {
      const ctx = getAC();
      if (ctx.state === 'suspended') ctx.resume();
      const sr  = ctx.sampleRate;
      const len = sr * 0.22;
      const buf = ctx.createBuffer(1, len, sr);
      const dat = buf.getChannelData(0);
      const dec = local ? 14 : 28;
      const vol = local ? 0.85 : 0.38;
      for (let i = 0; i < len; i++)
        dat[i] = (Math.random() * 2 - 1) * Math.exp(-i / (sr / dec)) * vol;
      const src = ctx.createBufferSource();
      src.buffer = buf;
      const g = ctx.createGain();
      g.gain.value = 1;
      src.connect(g);
      g.connect(ctx.destination);
      src.start();
    } catch (_) {}
  }

  // ─────────────────────────────────────────────────────────────────────────
  // MAIN GAME CLASS
  // ─────────────────────────────────────────────────────────────────────────

  class Game {
    constructor() {
      // ── State ──────────────────────────────────────────────────────────
      this.map      = null;
      this.myId     = null;    // my PeerJS ID
      this.isHost   = false;
      this.peer     = null;
      this.conns    = new Map();    // peerId → DataConnection
      this.players  = new Map();   // peerId → playerState
      this.bullets  = [];          // active bullet objects
      this.shotInds = [];          // {wx,wy,angle,ttl}  shot indicators (world-space origin)
      this.soundInds = [];         // {wx,wy,ttl,type}   sound-arc indicators (world-space origin)
      this.running  = false;
      this.syncTimer = 0;
      this.lastNetStateAt = new Map();
      this.respawnTimers  = new Map();
      this.specCamX = 0;   // spectator camera world-X (used when local player is dead)
      this.specCamY = 0;   // spectator camera world-Y

      // ── Bot state ──────────────────────────────────────────────────────
      this.botCount = 0;
      this.botRng   = mkRng(Date.now());

      // ── Spawn assignments (set by host at game start) ──────────────────
      this.mySpawnIdx    = 0;      // host's own assigned spawn index
      this.teamSpawnIdxs = null;   // { 0: spawnIdx, 1: spawnIdx } in team mode

      // ── Waiting room state ─────────────────────────────────────────────
      this.roomSettings  = { mapSize: 'medium', botCount: 0, gameMode: 'ffa', lives: 0, teamAssignments: {} };
      this.waitingPeerIds = [];   // peer IDs of non-host players in waiting room
      this.hostId        = null;  // PeerJS ID of the host
      this.matchEnded    = false;
      this.matchStats    = { ffaKills: {}, teamKills: { 0: 0, 1: 0 } };

      // ── Input ──────────────────────────────────────────────────────────
      this.keys = {};
      this.mouse = { x: 0, y: 0 };

      // ── Virtual joysticks ──────────────────────────────────────────────
      this.jL = { on: false, ox: 0, oy: 0, dx: 0, dy: 0, id: null }; // move
      this.jR = { on: false, ox: 0, oy: 0, dx: 0, dy: 0, id: null, shotPending: false }; // aim+shoot

      // ── PIXI objects ───────────────────────────────────────────────────
      this.app      = null;
      this.world    = null;   // scrolling world container
      this.mapGfx   = null;
      this.bullGfx  = null;
      this.playGfx  = null;
      this.darkFill = null;
      this.darkAmb  = null;
      this.darkFov  = null;
      this.darkRT   = null;
      this.darkSpr  = null;
      this.indGfx   = null;
      this.hudGfx   = null;
      this.joyGfx   = null;
      this.soundGfx = null;

      // ── DOM HUD refs ───────────────────────────────────────────────────
      this.domHud       = document.getElementById('hud-overlay');
      this.domDead      = document.getElementById('hud-dead');
      this.domRespawn   = document.getElementById('hud-respawn-msg');
      this.domDoorPrmpt = document.getElementById('hud-door-prompt');
      this.domRoomCode  = document.getElementById('hud-room-code');
      this.domAmmo      = document.getElementById('hud-ammo');
      this.domLives     = document.getElementById('hud-lives');
      this.domMode      = document.getElementById('hud-mode');
      this.domMatchEnd  = document.getElementById('hud-match-end');
      this.domMatchEndTitle = document.getElementById('hud-match-end-title');
      this.domMatchEndDesc  = document.getElementById('hud-match-end-desc');
      this.domScoreboard    = document.getElementById('hud-scoreboard');
      this.domBtnShootLeft = document.getElementById('btn-shoot-left');
      this.domBtnShoot  = document.getElementById('btn-shoot');
      this.domBtnInteract = document.getElementById('btn-interact');

      this._init();
    }

    // ══════════════════════════════════════════════════════════════════════
    // INIT
    // ══════════════════════════════════════════════════════════════════════

    _init() {
      this._initPixi();
      this._initInput();
      this._initLobby();
      this._registerSW();
      this._initInstallPrompt();
    }

    // ── PIXI setup ─────────────────────────────────────────────────────────
    _initPixi() {
      // Use locked dimensions (same values as CSS --app-h/--app-w) so the canvas
      // never resizes due to mobile nav-bar or status-bar changes.
      let _appW = window.innerWidth;
      let _appH = window.innerHeight;

      const app = new PIXI.Application({
        width: _appW,
        height: _appH,
        backgroundColor: 0x000000,
        resolution: Math.min(window.devicePixelRatio || 1, 2),
        autoDensity: true,
        antialias: false,
      });

      const wrap = document.getElementById('canvas-wrap');
      wrap.appendChild(app.view);
      this.app = app;

      // Resize only on real orientation / window changes – NOT on nav-bar show/hide.
      // A nav-bar change is a small height-only decrease (<= 200 px); anything else
      // (width change, height increase, or large height decrease) is a genuine resize.
      const onResize = () => {
        const nw = window.innerWidth;
        const nh = window.innerHeight;
        const heightDecreased = nh < _appH;
        const smallDecrease   = (_appH - nh) <= MAX_NAVBAR_HEIGHT_CHANGE;
        if (nw === _appW && heightDecreased && smallDecrease) return; // nav-bar – ignore
        _appW = nw;
        _appH = nh;
        app.renderer.resize(_appW, _appH);
        this._rebuildDarkRT();
      };

      if (screen.orientation) {
        screen.orientation.addEventListener('change', () => setTimeout(onResize, 300));
      } else {
        window.addEventListener('orientationchange', () => setTimeout(onResize, 300));
      }
      // Also handle desktop browser resizes
      window.addEventListener('resize', onResize);

      // World container (camera scroll)
      this.world = new PIXI.Container();
      app.stage.addChild(this.world);

      // Map tiles (static, redrawn when map changes)
      this.mapGfx = new PIXI.Graphics();
      this.world.addChild(this.mapGfx);

      // Bullets (world-space, redrawn each tick)
      this.bullGfx = new PIXI.Graphics();
      this.world.addChild(this.bullGfx);

      // Players (world-space, redrawn each tick)
      this.playGfx = new PIXI.Graphics();
      this.world.addChild(this.playGfx);

      // Reusable graphics for darkness overlay
      this.darkFill = new PIXI.Graphics();
      this.darkAmb  = new PIXI.Graphics();
      this.darkFov  = new PIXI.Graphics();
      this.darkAmb.blendMode = PIXI.BLEND_MODES.ERASE;
      this.darkFov.blendMode = PIXI.BLEND_MODES.ERASE;

      // Darkness sprite (covers full screen, screen-space)
      this._rebuildDarkRT();

      // Shot indicators + HUD + joystick + sound arcs (screen-space)
      this.indGfx   = new PIXI.Graphics();
      this.hudGfx   = new PIXI.Graphics();
      this.joyGfx   = new PIXI.Graphics();
      this.soundGfx = new PIXI.Graphics();
      app.stage.addChild(this.indGfx);
      app.stage.addChild(this.hudGfx);
      app.stage.addChild(this.joyGfx);
      app.stage.addChild(this.soundGfx);

      app.ticker.add(delta => this._tick(delta * (1 / 60)));
    }

    _rebuildDarkRT() {
      const { app } = this;
      const W = app.screen.width, H = app.screen.height;
      if (this.darkSpr) app.stage.removeChild(this.darkSpr);
      if (this.darkRT)  this.darkRT.destroy(true);
      this.darkRT  = PIXI.RenderTexture.create({ width: W, height: H });
      this.darkSpr = new PIXI.Sprite(this.darkRT);
      // Insert after world (index 1) so it sits above game world but below HUD
      app.stage.addChildAt(this.darkSpr, 1);
    }

    // ── Input ─────────────────────────────────────────────────────────────
    _initInput() {
      window.addEventListener('keydown', e => {
        this.keys[e.key.toLowerCase()] = true;
        if (!this.running) return;
        if (e.key === ' ' || e.key.toLowerCase() === 'f') {
          e.preventDefault();
          this._shoot();
        }
        if (e.key.toLowerCase() === 'e') this._interactDoor();
      });
      window.addEventListener('keyup', e => { this.keys[e.key.toLowerCase()] = false; });

      window.addEventListener('mousemove', e => {
        this.mouse.x = e.clientX;
        this.mouse.y = e.clientY;
        if (this.running) {
          const me = this.players.get(this.myId);
          if (!me) return;
          const cx = this.app.screen.width  / 2;
          const cy = this.app.screen.height / 2;
          me.angle = Math.atan2(e.clientY - cy, e.clientX - cx);
        }
      });

      window.addEventListener('click', e => {
        if (e.target.closest(INTERACTIVE_SELECTOR)) return;
        if (this.running) this._shoot();
      });

      // Touch – split screen into left (move) and right (aim/shoot)
      window.addEventListener('touchstart', e => this._onTouchStart(e), { passive: false });
      window.addEventListener('touchmove',  e => this._onTouchMove(e),  { passive: false });
      window.addEventListener('touchend',   e => this._onTouchEnd(e),   { passive: false });
      window.addEventListener('touchcancel',e => this._onTouchEnd(e),   { passive: false });

      // Mobile action buttons
      this.domBtnShootLeft.addEventListener('touchstart', e => { e.preventDefault(); if (this.running) this._shoot(); }, { passive: false });
      this.domBtnShootLeft.addEventListener('click', () => { if (this.running) this._shoot(); });
      this.domBtnShoot.addEventListener('touchstart', e => { e.preventDefault(); if (this.running) this._shoot(); }, { passive: false });
      this.domBtnShoot.addEventListener('click', () => { if (this.running) this._shoot(); });
      this.domBtnInteract.addEventListener('touchstart', e => { e.preventDefault(); if (this.running) this._interactDoor(); }, { passive: false });
      this.domBtnInteract.addEventListener('click', () => { if (this.running) this._interactDoor(); });
    }

    _onTouchStart(e) {
      // Don't intercept touches on buttons/inputs so click handlers still fire,
      // and don't intercept touches inside scrollable containers.
      if (e.target.closest(INTERACTIVE_SELECTOR)) return;
      if (e.target.closest(SCROLLABLE_SELECTOR)) return;
      e.preventDefault();
      for (const t of e.changedTouches) {
        const half = window.innerWidth / 2;
        if (t.clientX < half) {
          this.jL = { on: true, ox: t.clientX, oy: t.clientY, dx: 0, dy: 0, id: t.identifier };
        } else {
          this.jR = { on: true, ox: t.clientX, oy: t.clientY, dx: 0, dy: 0, id: t.identifier, shotPending: false };
        }
      }
    }

    _onTouchMove(e) {
      if (e.target.closest(INTERACTIVE_SELECTOR)) return;
      if (e.target.closest(SCROLLABLE_SELECTOR)) return;
      e.preventDefault();
      for (const t of e.changedTouches) {
        if (this.jL.on && t.identifier === this.jL.id) {
          this.jL.dx = t.clientX - this.jL.ox;
          this.jL.dy = t.clientY - this.jL.oy;
        }
        if (this.jR.on && t.identifier === this.jR.id) {
          this.jR.dx = t.clientX - this.jR.ox;
          this.jR.dy = t.clientY - this.jR.oy;
          if (this.running) {
            const me = this.players.get(this.myId);
            const len = Math.hypot(this.jR.dx, this.jR.dy);
            if (me && len > JOY_DEAD_ZONE) me.angle = Math.atan2(this.jR.dy, this.jR.dx);
          }
        }
      }
    }

    _onTouchEnd(e) {
      // Always clean up any joystick state for this touch, regardless of where
      // the finger lifted. This prevents a ghost "stuck" joystick when a drag
      // starts outside an interactive element but ends over one.
      for (const t of e.changedTouches) {
        if (this.jL.on && t.identifier === this.jL.id) {
          this.jL = { on: false, ox: 0, oy: 0, dx: 0, dy: 0, id: null };
        }
        if (this.jR.on && t.identifier === this.jR.id) {
          this.jR = { on: false, ox: 0, oy: 0, dx: 0, dy: 0, id: null, shotPending: false };
        }
      }
      // Only suppress the browser's default action when the touch is not on an
      // interactive element or inside a scrollable container.
      if (e.target.closest(INTERACTIVE_SELECTOR)) return;
      if (e.target.closest(SCROLLABLE_SELECTOR)) return;
      e.preventDefault();
    }

    // ── Service Worker ─────────────────────────────────────────────────────
    _registerSW() {
      if ('serviceWorker' in navigator) {
        navigator.serviceWorker.register('./sw.js').catch(() => {});
      }
    }

    // ── Install Prompt ─────────────────────────────────────────────────────
    _initInstallPrompt() {
      let deferredPrompt = null;
      const banner    = document.getElementById('install-banner');
      const btnInst   = document.getElementById('btn-install');
      const btnClose  = document.getElementById('install-close');

      window.addEventListener('beforeinstallprompt', e => {
        e.preventDefault();
        deferredPrompt = e;
        banner.style.display = 'flex';
      });

      btnInst.addEventListener('click', () => {
        banner.style.display = 'none';
        if (deferredPrompt) { deferredPrompt.prompt(); deferredPrompt = null; }
      });

      btnClose.addEventListener('click', () => { banner.style.display = 'none'; });
    }

    // ── Lobby UI ───────────────────────────────────────────────────────────
    _initLobby() {
      const createBtn = document.getElementById('btn-create');
      const joinBtn   = document.getElementById('btn-join');
      const joinInput = document.getElementById('join-input');
      const statusEl  = document.getElementById('status-msg');

      createBtn.addEventListener('click', () => {
        createBtn.disabled = true;
        statusEl.textContent = '正在建立房間…';
        // Generate a short room code and use it as the peer ID so joiners can
        // connect with the code directly (avoids UUID truncation mismatch).
        const tryCreate = () => {
          const chars = '0123456789abcdefghijklmnopqrstuvwxyz';
          const arr = new Uint8Array(6);
          crypto.getRandomValues(arr);
          const roomCode = Array.from(arr, b => chars[b % 36]).join('').toUpperCase();
          this._initPeer(roomCode.toLowerCase(), peerId => {
            this.isHost = true;
            this.hostId = peerId;
            this._showWaitingRoom(true, roomCode);
          }, err => {
            if (err === 'unavailable-id') {
              // Rare ID collision – retry with a new code
              if (this.peer) { this.peer.destroy(); this.peer = null; }
              tryCreate();
            } else {
              createBtn.disabled = false;
              statusEl.textContent = '建立失敗：' + err;
            }
          });
        };
        tryCreate();
      });

      joinBtn.addEventListener('click', () => {
        const code = joinInput.value.trim().toUpperCase();
        if (code.length < 6) { statusEl.textContent = '請輸入正確代碼'; return; }
        joinInput.blur(); // dismiss mobile soft keyboard
        joinBtn.disabled = true;
        statusEl.textContent = '正在連線…';
        this._initPeer(null, () => {
          this._connectToHost(code, statusEl, joinBtn);
        }, err => {
          joinBtn.disabled = false;
          statusEl.textContent = '連線失敗：' + err;
        });
      });

      joinInput.addEventListener('keydown', e => {
        if (e.key === 'Enter') joinBtn.click();
      });

      // Back to lobby from match-end screen (reloads page)
      const backLobbyBtn = document.getElementById('btn-back-lobby');
      if (backLobbyBtn) {
        backLobbyBtn.addEventListener('click', () => window.location.reload());
      }

      // Waiting room: click code to copy
      document.getElementById('wr-code').addEventListener('click', () => {
        const el = document.getElementById('wr-code');
        const code = el.textContent;
        navigator.clipboard?.writeText(code).then(() => {
          el.textContent = '已複製！';
          setTimeout(() => { el.textContent = code; }, 1200);
        });
      });

      document.getElementById('wr-players').addEventListener('click', e => {
        const btn = e.target.closest('[data-team-player-id]');
        if (!btn || !this.isHost || !this._isTeamMode()) return;
        const playerId = btn.dataset.teamPlayerId;
        const currentTeam = Number(btn.dataset.team);
        if (!Number.isFinite(currentTeam)) return;
        this._syncWaitingTeamAssignments();
        if (!Object.prototype.hasOwnProperty.call(this.roomSettings.teamAssignments, playerId)) return;
        this.roomSettings.teamAssignments[playerId] = currentTeam === 1 ? 0 : 1;
        this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
        this._updateWaitingRoomUI();
      });

      // Waiting room: map size selection (host only)
      document.querySelectorAll('.size-btn').forEach(btn => {
        btn.addEventListener('click', () => {
          if (!this.isHost) return;
          this.roomSettings.mapSize = btn.dataset.size;
          this._updateWaitingSettings();
          this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
        });
      });

      // Waiting room: bot count (host only)
      document.getElementById('wr-bot-dec').addEventListener('click', () => {
        if (!this.isHost) return;
        const humans = 1 + this.waitingPeerIds.length;
        if (this.roomSettings.botCount > 0) {
          this.roomSettings.botCount--;
          this._syncWaitingTeamAssignments();
          this._updateWaitingSettings();
          this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
          this._updateWaitingRoomUI();
        }
      });

      document.getElementById('wr-bot-inc').addEventListener('click', () => {
        if (!this.isHost) return;
        const humans = 1 + this.waitingPeerIds.length;
        const maxBots = MAX_PLAYERS - humans;
        if (this.roomSettings.botCount < maxBots) {
          this.roomSettings.botCount++;
          this._syncWaitingTeamAssignments();
          this._updateWaitingSettings();
          this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
          this._updateWaitingRoomUI();
        }
      });

      // Waiting room: lives per player (host only)
      document.getElementById('wr-lives-dec').addEventListener('click', () => {
        if (!this.isHost) return;
        if ((this.roomSettings.lives || 0) > 0) {
          this.roomSettings.lives--;
          this._updateWaitingSettings();
          this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
        }
      });

      document.getElementById('wr-lives-inc').addEventListener('click', () => {
        if (!this.isHost) return;
        if ((this.roomSettings.lives || 0) < 10) {
          this.roomSettings.lives = (this.roomSettings.lives || 0) + 1;
          this._updateWaitingSettings();
          this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
        }
      });

      // Waiting room: game mode (host only)
      document.querySelectorAll('.mode-btn').forEach(btn => {
        btn.addEventListener('click', () => {
          if (!this.isHost) return;
          this.roomSettings.gameMode = this._normalizeGameMode(btn.dataset.mode);
          this._syncWaitingTeamAssignments();
          this._updateWaitingSettings();
          this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
          this._updateWaitingRoomUI();
        });
      });

      // Waiting room: start game (host only)
      document.getElementById('btn-start-game').addEventListener('click', () => {
        if (!this.isHost) return;
        const size = MAP_SIZES[this.roomSettings.mapSize] || MAP_SIZES.medium;
        MW = size.w; MH = size.h;
        const seed = randomSeed();
        this.map = generateMap(seed);

        // Build ordered player list for team/spawn assignment
        // (bot IDs are predictable: bot-0, bot-1, … since botCount is reset to 0)
        const allPlayerIds = [this.myId, ...this.waitingPeerIds];
        for (let i = 0; i < this.roomSettings.botCount; i++) {
          allPlayerIds.push('bot-' + i);
        }

        // Assign teams (team mode only)
        this._syncWaitingTeamAssignments();
        const teamAssignments = {};
        if (this._isTeamMode()) {
          allPlayerIds.forEach((pid, idx) => {
            teamAssignments[pid] = this._getWaitingTeamAssignment(pid, idx);
          });
        }

        // Assign random spawn indices: FFA → each player a different random point;
        // team mode → each team gets its own randomly chosen spawn point
        const numSpawns = this.map.spawns.length;
        const spawnAssignments = {};
        if (this._isTeamMode()) {
          const idxA = Math.floor(Math.random() * numSpawns);
          const idxB = numSpawns > 1
            ? (idxA + 1 + Math.floor(Math.random() * (numSpawns - 1))) % numSpawns
            : idxA;
          this.teamSpawnIdxs = { 0: idxA, 1: idxB };
          allPlayerIds.forEach(pid => {
            spawnAssignments[pid] = this.teamSpawnIdxs[teamAssignments[pid] ?? 0];
          });
        } else {
          this.teamSpawnIdxs = null;
          // Build enough shuffled indices so every player gets a unique spawn
          // before any is reused (each spawn point used once per "round").
          const shuffled = [];
          while (shuffled.length < allPlayerIds.length) {
            shuffled.push(...shuffleArray(Array.from({ length: numSpawns }, (_, i) => i)));
          }
          allPlayerIds.forEach((pid, i) => { spawnAssignments[pid] = shuffled[i]; });
        }
        this.mySpawnIdx = spawnAssignments[this.myId] ?? 0;

        // Build the authoritative player roster before the match starts
        for (const id of [...this.respawnTimers.keys()]) this._clearRespawnTimer(id);
        this.lastNetStateAt.clear();
        this.players.clear();
        for (const pid of [this.myId, ...this.waitingPeerIds]) {
            this._spawnPlayerState(
              pid,
              spawnAssignments[pid] ?? 0,
              this._isTeamMode() ? (teamAssignments[pid] ?? 0) : 0
            );
          }

        // Spawn bots with their assigned positions (don't broadcast yet)
        this.botCount = 0;
        for (let i = 0; i < this.roomSettings.botCount; i++) {
          this._addBot(false, spawnAssignments['bot-' + i]);
        }

        // Apply teams to all authoritative players
        for (const [pid, p] of this.players) {
          p.team = this._isTeamMode() ? (teamAssignments[pid] ?? 0) : 0;
        }

        // Send welcome to each peer (includes bots, team assignments, and spawn info)
        for (const [pid] of this.conns) {
          this._sendTo(pid, {
            type: 'welcome',
            seed,
            spawnIdx: spawnAssignments[pid] ?? 0,
            mapSize: this.roomSettings.mapSize,
            gameMode: this.roomSettings.gameMode,
            lives: this.roomSettings.lives || 0,
            teams: teamAssignments,
            teamSpawnIdxs: this.teamSpawnIdxs,
            players: [...this.players.entries()].map(([id, p]) => this._serializePlayer(id, p)),
          });
        }
        this._startGame();
      });
    }

    // ══════════════════════════════════════════════════════════════════════
    // PEER.JS NETWORKING
    // ══════════════════════════════════════════════════════════════════════

    _initPeer(id, onOpen, onError) {
      const options = { debug: 0 };
      const p = id ? new Peer(id, options) : new Peer(options);
      this.peer = p;

      p.on('open', pid => { this.myId = pid; onOpen(pid); });
      p.on('error', err => { if (onError) onError(err.type || err.message); });
      p.on('connection', conn => this._handleIncoming(conn));
    }

    _connectToHost(code, statusEl, joinBtn) {
      // PeerJS IDs are lowercase; try to find the real peer ID
      const hostId = code.toLowerCase();
      const conn = this.peer.connect(hostId, { reliable: true });
      conn.on('open', () => {
        statusEl.textContent = '已連線，等待地圖…';
        this._registerConn(conn);
        conn.send({ type: 'hello', id: this.myId });
      });
      conn.on('error', err => {
        joinBtn.disabled = false;
        statusEl.textContent = '連線錯誤：' + (err.message || err);
      });
    }

    _handleIncoming(conn) {
      conn.on('open', () => this._registerConn(conn));
    }

    _registerConn(conn) {
      const pid = conn.peer;
      this.conns.set(pid, conn);
      conn.on('data', data => this._onMsg(pid, data));
      conn.on('close', () => {
        this.conns.delete(pid);
        this._clearRespawnTimer(pid);
        this.players.delete(pid);
        if (!this.running) {
          this.waitingPeerIds = this.waitingPeerIds.filter(id => id !== pid);
          if (this.isHost) {
            this._syncWaitingTeamAssignments();
            this._broadcast({ type: 'playerListUpdate', peerIds: [...this.waitingPeerIds] });
            this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
          }
          this._updateWaitingRoomUI();
        } else if (this.isHost) {
          this._broadcast({ type: 'playerLeave', id: pid });
          this._checkMatchEndCondition();
        }
      });
    }

    _broadcast(msg, exceptId) {
      for (const [pid, conn] of this.conns) {
        if (pid !== exceptId && conn.open) {
          try { conn.send(msg); } catch (_) {}
        }
      }
    }

    _sendTo(pid, msg) {
      const conn = this.conns.get(pid);
      if (conn && conn.open) { try { conn.send(msg); } catch (_) {} }
    }

    _serializePlayer(id, p) {
      return {
        id,
        x: p.x,
        y: p.y,
        angle: p.angle,
        hp: p.hp,
        dead: !!p.dead,
        isBot: !!p.isBot,
        team: p.team ?? 0,
        respawnAt: p.respawnAt || 0,
        ammo: Number.isFinite(p.ammo) ? p.ammo : MAG_SIZE,
        reloading: !!p.reloading,
        reloadUntil: p.reloadUntil || 0,
        kills: p.kills || 0,
        deaths: p.deaths || 0,
        livesLeft: p.livesLeft ?? 0,
      };
    }

    _sanitizeTeamAssignments(assignments) {
      const normalized = {};
      for (const [id, team] of Object.entries(assignments || {})) {
        const teamNum = Number(team);
        if (teamNum === 0 || teamNum === 1) normalized[id] = teamNum;
      }
      return normalized;
    }

    _getWaitingParticipantIds() {
      const ids = [];
      const hostId = this.hostId || this.myId;
      if (hostId) ids.push(hostId);
      ids.push(...this.waitingPeerIds);
      for (let i = 0; i < (this.roomSettings.botCount || 0); i++) ids.push('bot-' + i);
      return ids;
    }

    _syncWaitingTeamAssignments() {
      const ids = this._getWaitingParticipantIds();
      const current = this._sanitizeTeamAssignments(this.roomSettings.teamAssignments);
      const next = {};
      const counts = [0, 0];
      for (const id of ids) {
        const team = current[id] ?? (counts[0] <= counts[1] ? 0 : 1);
        next[id] = team;
        counts[team] = (counts[team] || 0) + 1;
      }
      this.roomSettings.teamAssignments = next;
      return next;
    }

    _getWaitingTeamAssignment(playerId, fallbackIndex = 0) {
      const assignments = this._sanitizeTeamAssignments(this.roomSettings.teamAssignments);
      return assignments[playerId] ?? (fallbackIndex % 2);
    }

    _broadcastPlayerState(id, exceptId) {
      if (!this.isHost) return;
      const p = this.players.get(id);
      if (!p) return;
      this._broadcast({ type: 'state', ...this._serializePlayer(id, p) }, exceptId);
    }

    _broadcastAllPlayerStates() {
      if (!this.isHost) return;
      for (const [id] of this.players) this._broadcastPlayerState(id);
    }

    _clearRespawnTimer(id) {
      const timer = this.respawnTimers.get(id);
      if (timer) clearTimeout(timer);
      this.respawnTimers.delete(id);
    }

    _isValidPlayerPosition(x, y) {
      if (!this.map) return false;
      if (!Number.isFinite(x) || !Number.isFinite(y)) return false;
      if (x < P_RAD || y < P_RAD) return false;
      if (x > MW * TS - P_RAD || y > MH * TS - P_RAD) return false;
      return !this._solid(x, y);
    }

    _isTeamMode() {
      return this.roomSettings.gameMode === 'team_deathmatch' ||
        this.roomSettings.gameMode === 'team_survival';
    }

    _normalizeGameMode(mode) {
      if (mode === 'team') return 'team_deathmatch';
      if (mode === 'team_deathmatch' || mode === 'team_survival' || mode === 'ffa') return mode;
      return 'ffa';
    }

    _isTeamSurvivalMode() {
      return this.roomSettings.gameMode === 'team_survival';
    }

    _modeLabel(mode = this.roomSettings.gameMode) {
      if (mode === 'team_deathmatch') return '團隊死鬥';
      if (mode === 'team_survival') return '團隊生存';
      return '大亂鬥';
    }

    _teamName(team) {
      return team === 1 ? 'B隊' : 'A隊';
    }

    _resetMatchStats() {
      this.matchEnded = false;
      this.matchStats = { ffaKills: {}, teamKills: { 0: 0, 1: 0 } };
      if (this.domMatchEnd) this.domMatchEnd.classList.remove('show');
    }

    _recordKill(attackerId, targetId) {
      if (this.matchEnded) return;
      const target = this.players.get(targetId);
      if (target) {
        target.deaths = (target.deaths || 0) + 1;
        if ((this.roomSettings.lives || 0) > 0) {
          target.livesLeft = Math.max(0, (target.livesLeft || 0) - 1);
        }
      }
      if (!attackerId || attackerId === targetId) return;
      const attacker = this.players.get(attackerId);
      if (!attacker) return;
      attacker.kills = (attacker.kills || 0) + 1;
      if (this.roomSettings.gameMode === 'ffa') {
        this.matchStats.ffaKills[attackerId] = (this.matchStats.ffaKills[attackerId] || 0) + 1;
      } else if (this._isTeamMode()) {
        const team = attacker.team ?? 0;
        this.matchStats.teamKills[team] = (this.matchStats.teamKills[team] || 0) + 1;
      }
    }

    _countAliveTeams() {
      const alive = { 0: 0, 1: 0 };
      for (const [, p] of this.players) {
        if (!p.dead) alive[p.team ?? 0] = (alive[p.team ?? 0] || 0) + 1;
      }
      return alive;
    }

    _checkMatchEndCondition() {
      if (!this.isHost || this.matchEnded || !this.running) return;
      const livesMode = (this.roomSettings.lives || 0) > 0;

      if (this.roomSettings.gameMode === 'ffa') {
        if (livesMode) {
          // FFA with lives: match ends when ≤1 player still has lives
          const withLives = [...this.players.values()].filter(p => (p.livesLeft || 0) > 0);
          if (withLives.length <= 1) {
            const winner = withLives[0];
            this._endMatch({
              title: '🏆 比賽結束',
              desc: winner
                ? `${winner.id.slice(0, 8).toUpperCase()} 最後存活獲勝`
                : '所有玩家陣亡，平手',
            });
          }
          return;
        }
        // FFA unlimited: kill limit
        for (const [pid, kills] of Object.entries(this.matchStats.ffaKills)) {
          if (kills >= FFA_KILL_LIMIT) {
            this._endMatch({
              title: '🏆 比賽結束',
              desc: `${pid.slice(0, 8).toUpperCase()} 達成 ${FFA_KILL_LIMIT} 擊殺獲勝`,
            });
            return;
          }
        }
        return;
      }

      if (this.roomSettings.gameMode === 'team_deathmatch') {
        if (livesMode) {
          // Team deathmatch with lives: team wins when enemy team has 0 lives
          const teamLives = { 0: 0, 1: 0 };
          for (const [, p] of this.players) {
            const t = p.team ?? 0;
            teamLives[t] = (teamLives[t] || 0) + (p.livesLeft || 0);
          }
          for (const t of [0, 1]) {
            if (teamLives[t] <= 0) {
              const winner = t === 0 ? 1 : 0;
              this._endMatch({
                title: '🏆 團隊勝利',
                desc: `${this._teamName(winner)} 消滅了對方全隊`,
              });
              return;
            }
          }
          return;
        }
        // Team deathmatch unlimited: kill limit
        for (const team of [0, 1]) {
          if ((this.matchStats.teamKills[team] || 0) >= TEAM_KILL_LIMIT) {
            this._endMatch({
              title: '🏆 團隊勝利',
              desc: `${this._teamName(team)} 先達成 ${TEAM_KILL_LIMIT} 擊殺`,
            });
            return;
          }
        }
        return;
      }

      if (this._isTeamSurvivalMode()) {
        const alive = this._countAliveTeams();
        const aliveTeams = [0, 1].filter(team => (alive[team] || 0) > 0);
        if (aliveTeams.length === 1) {
          this._endMatch({
            title: '🏆 回合結束',
            desc: `${this._teamName(aliveTeams[0])} 全員存活到最後`,
          });
        } else if (aliveTeams.length === 0) {
          this._endMatch({ title: '🏆 回合結束', desc: '雙方同時陣亡，平手' });
        }
      }
    }

    _endMatch(result) {
      this.matchEnded = true;
      this.running = false;
      this.domDead.classList.remove('show');
      this.domDoorPrmpt.classList.remove('show');
      this.domBtnInteract.classList.remove('show');
      if (this.domMatchEndTitle) this.domMatchEndTitle.textContent = result.title;
      if (this.domMatchEndDesc) this.domMatchEndDesc.textContent = result.desc;
      if (this.domScoreboard) this.domScoreboard.innerHTML = this._buildScoreboard();
      if (this.domMatchEnd) this.domMatchEnd.classList.add('show');
      if (this.isHost) this._broadcast({ type: 'matchEnd', result });
    }

    _buildScoreboard() {
      const isTeam = this._isTeamMode();
      const hasLives = (this.roomSettings.lives || 0) > 0;
      const teamAColor = '#' + C.TEAM_A.toString(16).padStart(6, '0');
      const teamBColor = '#' + C.TEAM_B.toString(16).padStart(6, '0');

      // Collect and sort: by kills desc, then deaths asc
      const entries = [...this.players.values()].map(p => ({
        id: p.id,
        isBot: !!p.isBot,
        kills: p.kills || 0,
        deaths: p.deaths || 0,
        team: p.team ?? 0,
        livesLeft: p.livesLeft ?? 0,
      })).sort((a, b) => b.kills !== a.kills ? b.kills - a.kills : a.deaths - b.deaths);

      const teamHeader = isTeam ? '<th>隊伍</th>' : '';
      const livesHeader = hasLives ? '<th>剩餘命</th>' : '';

      const rows = entries.map((e, i) => {
        const isMe = e.id === this.myId;
        const label = e.isBot ? `🤖 Bot` : e.id.slice(0, 8).toUpperCase();
        const meTag = isMe ? ' <span style="color:#44ff88">（你）</span>' : '';
        const teamCell = isTeam
          ? `<td style="color:${e.team === 0 ? teamAColor : teamBColor}">${this._teamName(e.team)}</td>`
          : '';
        const livesCell = hasLives ? `<td>${e.livesLeft}</td>` : '';
        return `<tr class="${isMe ? 'is-self' : ''}">
          <td>${i + 1}</td>
          <td style="text-align:left">${label}${meTag}</td>
          ${teamCell}<td>${e.kills}</td><td>${e.deaths}</td>${livesCell}
        </tr>`;
      }).join('');

      return `<table class="scoreboard">
        <thead><tr><th>名次</th><th>玩家</th>${teamHeader}<th>擊殺</th><th>死亡</th>${livesHeader}</tr></thead>
        <tbody>${rows}</tbody>
      </table>`;
    }

    _pickLateJoinTeam() {
      if (!this._isTeamMode()) return 0;
      const counts = [0, 0];
      for (const [, p] of this.players) {
        counts[p.team ?? 0] = (counts[p.team ?? 0] || 0) + 1;
      }
      return counts[0] <= counts[1] ? 0 : 1;
    }

    _pickSpawnIdxForTeam(team) {
      if (!this.map || !this.map.spawns.length) return 0;
      if (this._isTeamMode() && this.teamSpawnIdxs) {
        return this.teamSpawnIdxs[team ?? 0] ?? 0;
      }
      return Math.floor(Math.random() * this.map.spawns.length);
    }

    _spawnPlayerState(id, spawnIdx, team, extras = {}) {
      const safeIdx = this.map.spawns.length ? (spawnIdx % this.map.spawns.length) : 0;
      const sp = this.map.spawns[safeIdx] || { x: TS * 1.5, y: TS * 1.5 };
      const p = mkPlayer(id, sp.x, sp.y);
      p.team = team ?? 0;
      p.isBot = !!extras.isBot;
      p.respawnAt = 0;
      p.kills = 0;
      p.deaths = 0;
      p.livesLeft = this.roomSettings.lives || 0;
      if (p.isBot) {
        p.botState = 'wander';
        p.botTarget = null;
        p.botTimer = 0;
        p.botShootTimer = BOT_SHOOT_CD * this.botRng();
      }
      this.players.set(id, p);
      if (!p.isBot) this.lastNetStateAt.set(id, Date.now());
      return p;
    }

    _upsertPlayerFromSnapshot(data) {
      let p = this.players.get(data.id);
      if (!p) {
        const fallbackTeam = data.team ?? 0;
        const fallbackSpawn = this.map ? this.map.spawns[this._pickSpawnIdxForTeam(fallbackTeam)] : { x: TS * 1.5, y: TS * 1.5 };
        p = mkPlayer(data.id, fallbackSpawn.x, fallbackSpawn.y);
        this.players.set(data.id, p);
      }
      const validPos = this._isValidPlayerPosition(data.x, data.y);
      const nextX = validPos ? data.x : p.x;
      const nextY = validPos ? data.y : p.y;
      p.x = nextX;
      p.y = nextY;
      if (Number.isFinite(data.angle)) p.angle = data.angle;
      if (Number.isFinite(data.hp)) p.hp = clamp(data.hp, 0, MAX_HP);
      p.dead = !!data.dead;
      p.isBot = !!data.isBot;
      p.team = data.team ?? p.team ?? 0;
      p.respawnAt = data.respawnAt || 0;
      if (Number.isFinite(data.ammo)) p.ammo = clamp(data.ammo, 0, MAG_SIZE);
      else if (!Number.isFinite(p.ammo)) p.ammo = MAG_SIZE;
      p.reloading = !!data.reloading;
      p.reloadUntil = Number.isFinite(data.reloadUntil)
        ? data.reloadUntil
        : (Number.isFinite(p.reloadUntil) ? p.reloadUntil : 0);
      if (Number.isFinite(data.kills)) p.kills = data.kills;
      else if (!Number.isFinite(p.kills)) p.kills = 0;
      if (Number.isFinite(data.deaths)) p.deaths = data.deaths;
      else if (!Number.isFinite(p.deaths)) p.deaths = 0;
      if (Number.isFinite(data.livesLeft)) p.livesLeft = data.livesLeft;
      else if (!Number.isFinite(p.livesLeft)) p.livesLeft = 0;
      if (p.isBot) {
        p.botState = p.botState || 'wander';
        p.botTarget = p.botTarget || null;
        p.botTimer = Number.isFinite(p.botTimer) ? p.botTimer : 0;
        p.botShootTimer = Number.isFinite(p.botShootTimer) ? p.botShootTimer : BOT_SHOOT_CD * this.botRng();
      }
      return p;
    }

    _isFriendlyFire(attacker, target) {
      return this._isTeamMode() &&
        (attacker.team ?? 0) === (target.team ?? 0);
    }

    _findShotTarget(shooter) {
      const ray = castRay(this.map, shooter.x, shooter.y, shooter.angle);
      let bestId = null;
      let bestProj = ray.dist + P_RAD;
      for (const [id, p] of this.players) {
        if (id === shooter.id || p.dead) continue;
        if (this._isFriendlyFire(shooter, p)) continue;
        const dx = p.x - shooter.x, dy = p.y - shooter.y;
        const cos = Math.cos(shooter.angle), sin = Math.sin(shooter.angle);
        const proj = dx * cos + dy * sin;
        const perp = Math.abs(dx * sin - dy * cos);
        if (proj > 0 && proj <= bestProj && perp <= P_RAD * 1.4) {
          bestProj = proj;
          bestId = id;
        }
      }
      return bestId;
    }

    _scheduleRespawn(id) {
      if (!this.isHost) return;
      this._clearRespawnTimer(id);
      if (this._isTeamSurvivalMode()) return;
      const p = this.players.get(id);
      if (!p) return;
      // If a lives limit is set and this player has exhausted their lives, no respawn
      if ((this.roomSettings.lives || 0) > 0 && (p.livesLeft || 0) <= 0) {
        this._broadcastPlayerState(id);
        return;
      }
      p.respawnAt = Date.now() + RESPAWN_MS;
      this._broadcastPlayerState(id);
      const timer = setTimeout(() => {
        this.respawnTimers.delete(id);
        this._respawnPlayer(id);
      }, RESPAWN_MS);
      this.respawnTimers.set(id, timer);
    }

    _respawnPlayer(id) {
      const p = this.players.get(id);
      if (!p || !p.dead || !this.map) return;
      const sp = this.map.spawns[this._pickRespawnIdx(p)] || { x: TS * 1.5, y: TS * 1.5 };
      p.x = sp.x;
      p.y = sp.y;
      p.hp = MAX_HP;
      p.dead = false;
      p.respawnAt = 0;
      p.ammo = MAG_SIZE;
      p.reloading = false;
      p.reloadUntil = 0;
      if (p.isBot) {
        p.botState = 'wander';
        p.botTarget = null;
        p.botTimer = 0;
        p.botShootTimer = BOT_SHOOT_CD * this.botRng();
      }
      this._broadcast({ type: 'respawn', player: this._serializePlayer(id, p) });
    }

    _applyDamage(targetId, dmg, attackerId) {
      if (!this.isHost) return false;
      const target = this.players.get(targetId);
      if (!target || target.dead) return false;
      const attacker = attackerId ? this.players.get(attackerId) : null;
      if (attacker && this._isFriendlyFire(attacker, target)) return false;
      target.hp = Math.max(0, target.hp - dmg);
      if (target.hp <= 0) {
        target.hp = 0;
        target.dead = true;
        this._recordKill(attackerId, targetId);
        this._scheduleRespawn(targetId);
        if (this._isTeamSurvivalMode()) this._broadcastPlayerState(targetId);
        this._checkMatchEndCondition();
      } else {
        this._broadcastPlayerState(targetId);
      }
      return true;
    }

    _handleStateRequest(fromId, msg) {
      const p = this.players.get(fromId);
      if (!p || p.dead) return;
      const prevAt = this.lastNetStateAt.get(fromId) || Date.now();
      const now = Date.now();
      this.lastNetStateAt.set(fromId, now);
      const minElapsed = Math.min(SYNC_MS / 1000, 0.25);
      const maxElapsed = Math.max(SYNC_MS / 1000, 0.25);
      const elapsed = clamp((now - prevAt) / 1000, minElapsed, maxElapsed);
      const maxStep = Math.max(NET_MAX_STEP, P_SPD * elapsed * NET_STEP_TOLERANCE);
      let dx = Number.isFinite(msg.x) ? msg.x - p.x : 0;
      let dy = Number.isFinite(msg.y) ? msg.y - p.y : 0;
      const dist = Math.hypot(dx, dy);
      if (dist > maxStep && dist > 0) {
        const s = maxStep / dist;
        dx *= s;
        dy *= s;
      }
      this._movePlayer(p, dx, dy);
      if (Number.isFinite(msg.angle)) p.angle = msg.angle;
      this._broadcastPlayerState(fromId);
    }

    _handleShootRequest(fromId, msg) {
      const shooter = this.players.get(fromId);
      if (!shooter || shooter.dead) return;
      if (Number.isFinite(msg.x) && Number.isFinite(msg.y)) {
        const drift = Math.hypot(msg.x - shooter.x, msg.y - shooter.y);
        if (drift > SHOT_POS_EPS) return;
      }
      if (Number.isFinite(msg.angle)) shooter.angle = msg.angle;
      if (!this._consumeAmmoAndReload(shooter)) {
        this._broadcastPlayerState(fromId);
        return;
      }
      const targetId = this._findShotTarget(shooter);
      if (targetId) this._applyDamage(targetId, MAX_HP, fromId);
      this._broadcastPlayerState(fromId);
      this._broadcast({
        type: 'shot',
        id: fromId,
        x: shooter.x,
        y: shooter.y,
        angle: shooter.angle,
      });
    }

    _handleDoorRequest(fromId, msg) {
      const p = this.players.get(fromId);
      if (!p || p.dead) return;
      const door = this.map.doors.find(d => d.x === msg.x && d.y === msg.y);
      if (!door) return;
      const dx = door.x * TS + TS / 2 - p.x;
      const dy = door.y * TS + TS / 2 - p.y;
      if (dx * dx + dy * dy > DOOR_D * DOOR_D) return;
      door.open = !door.open;
      this._redrawMap();
      this._broadcast({ type: 'door', x: door.x, y: door.y, open: door.open });
    }

    _onMsg(fromId, msg) {
      switch (msg.type) {
        case 'hello':
          // Client joined: send map seed + current players (or waiting room state)
          if (this.isHost) {
            if (this.running) {
              // Late joiner: spawn and sync them from the authoritative host state
              const team = this._pickLateJoinTeam();
              const spawnIdx = this._pickSpawnIdxForTeam(team);
              this._spawnPlayerState(fromId, spawnIdx, team);
              this._sendTo(fromId, {
                type: 'welcome',
                seed: this.map.seed,
                spawnIdx,
                mapSize: this.roomSettings.mapSize,
                gameMode: this.roomSettings.gameMode,
                lives: this.roomSettings.lives || 0,
                teams: Object.fromEntries([...this.players.entries()].map(([id, p]) => [id, p.team ?? 0])),
                teamSpawnIdxs: this.teamSpawnIdxs,
                players: [...this.players.entries()].map(([id, p]) => this._serializePlayer(id, p)),
              });
              // Tell existing players about the newcomer
              this._broadcast({ type: 'playerJoin', player: this._serializePlayer(fromId, this.players.get(fromId)) }, fromId);
            } else {
              // Waiting room: enforce max player limit
              const totalPlayers = 1 + this.waitingPeerIds.length + this.roomSettings.botCount;
              if (totalPlayers >= MAX_PLAYERS) {
                this._sendTo(fromId, { type: 'roomFull' });
                return;
              }
              if (!this.waitingPeerIds.includes(fromId)) {
                this.waitingPeerIds.push(fromId);
                // Reduce bot count if humans now exceed available slots
                const maxBots = MAX_PLAYERS - 1 - this.waitingPeerIds.length;
                if (this.roomSettings.botCount > maxBots) {
                  this.roomSettings.botCount = Math.max(0, maxBots);
                }
              }
              this._syncWaitingTeamAssignments();
              this._sendTo(fromId, {
                type: 'waitingAck',
                hostId: this.myId,
                settings: this.roomSettings,
                peerIds: [...this.waitingPeerIds],
              });
              this._broadcast({ type: 'playerListUpdate', peerIds: [...this.waitingPeerIds] }, fromId);
              this._broadcast({ type: 'settingsUpdate', settings: this.roomSettings });
              this._updateWaitingSettings();
              this._updateWaitingRoomUI();
            }
          }
          break;

        case 'waitingAck':
          // We (client) entered the waiting room
          this.hostId = msg.hostId;
          this.waitingPeerIds = msg.peerIds;
          {
            const incoming = msg.settings || {};
            this.roomSettings = {
              ...this.roomSettings,
              ...incoming,
              gameMode: this._normalizeGameMode(incoming.gameMode),
              teamAssignments: this._sanitizeTeamAssignments(incoming.teamAssignments),
            };
          }
          this._showWaitingRoom(false);
          this._updateWaitingRoomUI();
          this._updateWaitingSettings();
          break;

        case 'roomFull':
          // Host rejected us – room is at capacity
          document.getElementById('status-msg').textContent = `房間已滿（最多 ${MAX_PLAYERS} 人）`;
          document.getElementById('btn-join').disabled = false;
          if (this.peer) { this.peer.destroy(); this.peer = null; }
          break;

        case 'playerListUpdate':
          // Host updated the waiting room player list
          this.waitingPeerIds = msg.peerIds;
          this._updateWaitingRoomUI();
          break;

        case 'settingsUpdate':
          // Host changed room settings
          {
            const incoming = msg.settings || {};
            this.roomSettings = {
              ...this.roomSettings,
              ...incoming,
              gameMode: this._normalizeGameMode(incoming.gameMode),
              teamAssignments: this._sanitizeTeamAssignments(incoming.teamAssignments),
            };
          }
          this._updateWaitingSettings();
          this._updateWaitingRoomUI();
          break;

        case 'welcome':
          // We (client) received map + spawn from host – start the game
          if (msg.mapSize) {
            const sz = MAP_SIZES[msg.mapSize];
            if (sz) { MW = sz.w; MH = sz.h; }
          }
          if (msg.gameMode) this.roomSettings.gameMode = this._normalizeGameMode(msg.gameMode);
          if (Number.isFinite(msg.lives)) this.roomSettings.lives = msg.lives;
          this.teamSpawnIdxs = msg.teamSpawnIdxs || null;
          this.map = generateMap(msg.seed);
          const sp = this.map.spawns[msg.spawnIdx % this.map.spawns.length];
          const mePlayer = mkPlayer(this.myId, sp.x, sp.y);
          if (msg.teams && msg.teams[this.myId] !== undefined) mePlayer.team = msg.teams[this.myId];
          mePlayer.livesLeft = this.roomSettings.lives || 0;
          mePlayer.respawnAt = 0;
          this.players.set(this.myId, mePlayer);
          // Add existing players (including bots spawned by host)
          for (const pd of msg.players) {
            if (pd.id !== this.myId) {
              this._upsertPlayerFromSnapshot(pd);
            }
          }
          this._startGame();
          break;

        case 'playerJoin':
          if (msg.player && typeof msg.player.id === 'string' &&
              Number.isFinite(msg.player.x) && Number.isFinite(msg.player.y)) {
            this._upsertPlayerFromSnapshot(msg.player);
          }
          break;

        case 'state':
          if (this.isHost) break;
          {
            const existing = this.players.get(msg.id);
            if (msg.id !== this.myId && existing && !msg.dead && !existing.dead) {
              const moved = Math.hypot(msg.x - existing.x, msg.y - existing.y);
              if (moved > 2) this._pushSoundInd(msg.x, msg.y, 'step');
            }
            this._upsertPlayerFromSnapshot(msg);
          }
          break;

        case 'shot':
          if (msg.id !== this.myId) {
            playShot(false);
            this.shotInds.push({ wx: msg.x, wy: msg.y, angle: msg.angle, ttl: IND_TTL });
            // Visual bullet trail from the shooter's perspective
            this._spawnBullet(msg.x, msg.y, msg.angle, false);
            // Sound arc toward the shooter
            this._pushSoundInd(msg.x, msg.y, 'shot');
          }
          break;

        case 'stateRequest':
          if (this.isHost) this._handleStateRequest(fromId, msg);
          break;

        case 'shootRequest':
          if (this.isHost) this._handleShootRequest(fromId, msg);
          break;

        case 'doorRequest':
          if (this.isHost) this._handleDoorRequest(fromId, msg);
          break;

        case 'playerLeave':
          this.players.delete(msg.id);
          break;

        case 'door':
          const d = this.map.doors.find(d => d.x === msg.x && d.y === msg.y);
          if (d) d.open = msg.open;
          this._redrawMap();
          break;

        case 'respawn':
          if (!this.isHost && msg.player) this._upsertPlayerFromSnapshot(msg.player);
          break;

        case 'matchEnd':
          if (msg.result) this._endMatch(msg.result);
          break;
      }
    }

    // ══════════════════════════════════════════════════════════════════════
    // GAME LIFECYCLE
    // ══════════════════════════════════════════════════════════════════════

    _startGame() {
      // Spawn local player if not already created
      if (!this.players.has(this.myId)) {
        const spawnIdx = this.isHost ? this.mySpawnIdx : (this.players.size % this.map.spawns.length);
        const sp = this.map.spawns[spawnIdx];
        this.players.set(this.myId, mkPlayer(this.myId, sp.x, sp.y));
      }

      this._redrawMap();

      // Show room code in HUD corner (host ID is the room code)
      const roomCodeForHud = (this.hostId || this.myId).toUpperCase();
      this.domRoomCode.textContent = '房間: ' + roomCodeForHud;
      this.domRoomCode.classList.add('show');

      // Hide lobby and waiting room, show canvas + HUD
      document.getElementById('lobby').style.display = 'none';
      document.getElementById('waiting-room').style.display = 'none';
      document.getElementById('canvas-wrap').style.display = 'block';
      this.domHud.style.display = 'block';
      if (this.domMode) this.domMode.textContent = `模式：${this._modeLabel()}`;
      this._resetMatchStats();

      this.running = true;
      if (this.isHost && this._isTeamSurvivalMode()) this._checkMatchEndCondition();
    }

    // ── Waiting room helpers ───────────────────────────────────────────────
    _showWaitingRoom(isHost, code) {
      document.getElementById('lobby').style.display = 'none';
      document.getElementById('waiting-room').style.display = 'flex';

      const codeWrap = document.getElementById('wr-code-wrap');
      const codeEl   = document.getElementById('wr-code');
      if (code) {
        codeWrap.style.display = 'flex';
        codeEl.textContent = code;
      }

      // Settings card visible to all; controls disabled for non-host
      document.getElementById('wr-settings-card').style.display = 'flex';
      document.getElementById('btn-start-game').style.display   = isHost ? 'block' : 'none';
      document.getElementById('wr-waiting-msg').style.display   = isHost ? 'none' : 'block';

      if (isHost) this._syncWaitingTeamAssignments();

      // Disable controls for non-host clients (read-only view)
      const hostOnly = ['wr-bot-dec', 'wr-bot-inc', 'wr-lives-dec', 'wr-lives-inc'];
      document.querySelectorAll('.size-btn, .mode-btn').forEach(b => { b.disabled = !isHost; });
      hostOnly.forEach(id => { const el = document.getElementById(id); if (el) el.disabled = !isHost; });

      this._updateWaitingRoomUI();
      this._updateWaitingSettings();
    }

    _updateWaitingRoomUI() {
      const el = document.getElementById('wr-players');
      if (!el) return;

      const hostId    = this.hostId || this.myId;
      const hostShort = hostId.slice(0, 8).toUpperCase();
      const hostIsMe  = hostId === this.myId;
      const isTeam    = this._isTeamMode();
      const assignments = this._sanitizeTeamAssignments(this.roomSettings.teamAssignments);

      const teamControl = (playerId, fallbackIndex) => {
        if (!isTeam) return '';
        const team = assignments[playerId] ?? (fallbackIndex % 2);
        if (this.isHost) {
          return `<button class="wr-team-btn" type="button" data-team-player-id="${playerId}" data-team="${team}" title="點擊切換隊伍">${this._teamName(team)}</button>`;
        }
        return `<span class="wr-team-btn" data-team="${team}" aria-hidden="true">${this._teamName(team)}</span>`;
      };

      const renderEntry = (label, playerId, fallbackIndex, classes = '', extraStyle = '') =>
        `<div class="player-entry${classes ? ' ' + classes : ''}"${extraStyle ? ` style="${extraStyle}"` : ''}>` +
          `<span class="player-entry-label">${label}</span>${teamControl(playerId, fallbackIndex)}` +
        `</div>`;

      const entries = [
        renderEntry(`🎮 ${hostShort}${hostIsMe ? '（你·房主）' : '（房主）'}`, hostId, 0, `is-host${hostIsMe ? ' is-self' : ''}`),
      ];

      for (let i = 0; i < this.waitingPeerIds.length; i++) {
        const pid   = this.waitingPeerIds[i];
        const short = pid.slice(0, 8).toUpperCase();
        const isMe  = pid === this.myId;
        entries.push(renderEntry(`👤 ${short}${isMe ? '（你）' : ''}`, pid, i + 1, isMe ? 'is-self' : ''));
      }

      // Show pending bot slots
      const numHumans = 1 + this.waitingPeerIds.length;
      for (let i = 0; i < (this.roomSettings.botCount || 0); i++) {
        entries.push(renderEntry(
          `🤖 Bot ${i + 1}`,
          'bot-' + i,
          numHumans + i,
          '',
          'color:#ff9922;border-color:rgba(255,153,34,0.2)'
        ));
      }

      el.innerHTML = entries.join('');
      const teamHint = document.getElementById('wr-team-hint');
      if (teamHint) {
        teamHint.textContent = isTeam
          ? (this.isHost ? '點擊隊伍按鈕可切換 A / B 隊' : '隊伍由房主在等待室設定')
          : '';
      }

      // Update start button label with total count (host only)
      const startBtn = document.getElementById('btn-start-game');
      if (startBtn) {
        const total = numHumans + (this.roomSettings.botCount || 0);
        startBtn.textContent = `▶ 開始遊戲（${total} 人）`;
      }
    }

    _updateWaitingSettings() {
      document.querySelectorAll('.size-btn').forEach(b => {
        b.classList.toggle('active', b.dataset.size === this.roomSettings.mapSize);
      });
      document.querySelectorAll('.mode-btn').forEach(b => {
        b.classList.toggle('active', b.dataset.mode === this._normalizeGameMode(this.roomSettings.gameMode));
      });

      // Update bot count display
      const botDisplay = document.getElementById('wr-bot-display');
      if (botDisplay) botDisplay.textContent = this.roomSettings.botCount || 0;

      // Update bot +/− button states (host side)
      const humans  = 1 + this.waitingPeerIds.length;
      const maxBots = MAX_PLAYERS - humans;
      const decBtn  = document.getElementById('wr-bot-dec');
      const incBtn  = document.getElementById('wr-bot-inc');
      if (decBtn) decBtn.disabled = !this.isHost || (this.roomSettings.botCount || 0) <= 0;
      if (incBtn) incBtn.disabled = !this.isHost || (this.roomSettings.botCount || 0) >= maxBots;

      // Update lives display
      const lives = this.roomSettings.lives || 0;
      const livesDisplay = document.getElementById('wr-lives-display');
      if (livesDisplay) livesDisplay.textContent = lives === 0 ? '∞' : String(lives);
      const livesDecBtn = document.getElementById('wr-lives-dec');
      const livesIncBtn = document.getElementById('wr-lives-inc');
      if (livesDecBtn) livesDecBtn.disabled = !this.isHost || lives <= 0;
      if (livesIncBtn) livesIncBtn.disabled = !this.isHost || lives >= 10;
    }

    // ══════════════════════════════════════════════════════════════════════
    // MAP RENDERING  (called once on load, and after door state changes)
    // ══════════════════════════════════════════════════════════════════════

    _redrawMap() {
      const g = this.mapGfx;
      g.clear();
      const { tiles, doors } = this.map;

      for (let ty = 0; ty < MH; ty++) {
        for (let tx = 0; tx < MW; tx++) {
          const t  = tiles[ty][tx];
          const px = tx * TS, py = ty * TS;

          if (t === T.WALL) {
            g.beginFill(C.WALL);
            g.drawRect(px, py, TS, TS);
            g.endFill();
            // Lighter top edge
            g.beginFill(C.WALL_TOP);
            g.drawRect(px, py, TS, 5);
            g.endFill();
          } else if (t === T.FLOOR) {
            g.beginFill(C.FLOOR);
            g.drawRect(px, py, TS, TS);
            g.endFill();
            // Subtle grid lines
            g.lineStyle(0.5, C.FLOOR_LN, 0.4);
            g.drawRect(px, py, TS, TS);
            g.lineStyle(0);
          } else if (t === T.DOOR) {
            const door = doors.find(d => d.x === tx && d.y === ty);
            g.beginFill(door && door.open ? C.DOOR_OP : C.DOOR_CL);
            g.drawRect(px, py, TS, TS);
            g.endFill();
            // Door frame
            g.lineStyle(2, 0x000000, 0.5);
            g.drawRect(px + 2, py + 2, TS - 4, TS - 4);
            g.lineStyle(0);
          }
        }
      }
    }

    // ══════════════════════════════════════════════════════════════════════
    // GAME LOOP
    // ══════════════════════════════════════════════════════════════════════

    _tick(dt) {
      if (!this.running) return;

      const me = this.players.get(this.myId);
      if (!me) return;

      this._updateMovement(dt, me);
      this._updateBots(dt);
      this._updateBullets(dt);
      this._updateIndicators(dt);
      this._updateCamera(me);
      this._renderPlayers();
      this._renderBullets();
      this._renderDarkness(me);
      this._renderIndicators(me);
      this._renderSoundInds(me);
      this._renderHUD(me);
      this._renderJoysticks();
      this._syncState(dt, me);
    }

    // ── Movement ───────────────────────────────────────────────────────────
    _updateMovement(dt, me) {
      if (me.dead) {
        // Spectator mode: move the free-roaming camera with WASD / left joystick
        let vx = 0, vy = 0;
        if (this.keys['a'] || this.keys['arrowleft'])  vx -= 1;
        if (this.keys['d'] || this.keys['arrowright']) vx += 1;
        if (this.keys['w'] || this.keys['arrowup'])    vy -= 1;
        if (this.keys['s'] || this.keys['arrowdown'])  vy += 1;
        if (this.jL.on) {
          const len = Math.hypot(this.jL.dx, this.jL.dy);
          if (len > JOY_DEAD_ZONE) { vx = this.jL.dx / len; vy = this.jL.dy / len; }
          else { vx = 0; vy = 0; }
        }
        if (vx !== 0 || vy !== 0) {
          const len = Math.hypot(vx, vy) || 1;
          this.specCamX = clamp(this.specCamX + (vx / len) * P_SPD * dt, 0, MW * TS);
          this.specCamY = clamp(this.specCamY + (vy / len) * P_SPD * dt, 0, MH * TS);
        }
        return;
      }

      let vx = 0, vy = 0;

      // Keyboard
      if (this.keys['a'] || this.keys['arrowleft'])  vx -= 1;
      if (this.keys['d'] || this.keys['arrowright']) vx += 1;
      if (this.keys['w'] || this.keys['arrowup'])    vy -= 1;
      if (this.keys['s'] || this.keys['arrowdown'])  vy += 1;

      // Left joystick overrides keyboard axes with speed gradient
      let speedScale = 1;
      if (this.jL.on) {
        const len = Math.hypot(this.jL.dx, this.jL.dy);
        if (len > JOY_DEAD_ZONE) {
          speedScale = Math.min(len, JOY_MAX_R) / JOY_MAX_R; // 0→1 based on offset
          vx = this.jL.dx / len;
          vy = this.jL.dy / len;
        } else {
          vx = 0; vy = 0;
        }
      }

      if (vx !== 0 || vy !== 0) {
        if (!this.jL.on) {
          const len = Math.hypot(vx, vy) || 1;
          vx /= len; vy /= len;
        }
        this._movePlayer(me, vx * speedScale * P_SPD * dt, vy * speedScale * P_SPD * dt);
      }
      // Keep spectator camera in sync with live player position
      this.specCamX = me.x;
      this.specCamY = me.y;
    }

    _movePlayer(p, dx, dy) {
      // Slide along walls (try each axis separately)
      if (!this._solid(p.x + dx, p.y))       p.x += dx;
      else if (dx > 0 && !this._solid(p.x + 1, p.y)) p.x += 1;
      else if (dx < 0 && !this._solid(p.x - 1, p.y)) p.x -= 1;

      if (!this._solid(p.x, p.y + dy))       p.y += dy;
      else if (dy > 0 && !this._solid(p.x, p.y + 1)) p.y += 1;
      else if (dy < 0 && !this._solid(p.x, p.y - 1)) p.y -= 1;
    }

    _solid(wx, wy) {
      // Check corners of player circle
      const offsets = [
        [ P_RAD - 1,  0], [-P_RAD + 1,  0],
        [ 0,  P_RAD - 1], [ 0, -P_RAD + 1],
        [ P_RAD * 0.7,  P_RAD * 0.7], [-P_RAD * 0.7,  P_RAD * 0.7],
        [ P_RAD * 0.7, -P_RAD * 0.7], [-P_RAD * 0.7, -P_RAD * 0.7],
      ];
      for (const [ox, oy] of offsets) {
        if (this._tileBlocks(wx + ox, wy + oy)) return true;
      }
      return false;
    }

    _tileBlocks(wx, wy) {
      const tx = Math.floor(wx / TS), ty = Math.floor(wy / TS);
      if (tx < 0 || tx >= MW || ty < 0 || ty >= MH) return true;
      const t = this.map.tiles[ty][tx];
      if (t === T.WALL) return true;
      if (t === T.DOOR) {
        const d = this.map.doors.find(d => d.x === tx && d.y === ty);
        return !d || !d.open;
      }
      return false;
    }

    // ── Shooting ───────────────────────────────────────────────────────────
    _shoot() {
      const me = this.players.get(this.myId);
      if (!me || me.dead) return;
      if (!this._consumeAmmoAndReload(me)) return;

      playShot(true);
      this._spawnBullet(me.x, me.y, me.angle, true);

      if (this.isHost) {
        const targetId = this._findShotTarget(me);
        if (targetId) this._applyDamage(targetId, MAX_HP, this.myId);
        this._broadcastPlayerState(this.myId);
        this._broadcast({ type: 'shot', id: this.myId, x: me.x, y: me.y, angle: me.angle });
      } else {
        this._sendTo(this.hostId, {
          type: 'shootRequest',
          x: me.x,
          y: me.y,
          angle: me.angle,
        });
      }
    }

    _refreshReloadState(p, now = Date.now()) {
      if (!p) return;
      if (p.reloading && !Number.isFinite(p.reloadUntil)) {
        // Corrupted or incomplete sync snapshot: re-anchor reload timer instead
        // of instantly finishing reload.
        p.reloadUntil = now + RELOAD_MS;
        return;
      }
      if (p.reloading && now >= p.reloadUntil) {
        p.reloading = false;
        p.reloadUntil = 0;
        p.ammo = MAG_SIZE;
      }
    }

    _startReload(p, now = Date.now()) {
      this._refreshReloadState(p, now);
      if (!p || p.dead || p.reloading || p.ammo >= MAG_SIZE) return false;
      p.reloading = true;
      p.reloadUntil = now + RELOAD_MS;
      return true;
    }

    _consumeAmmoAndReload(p) {
      const now = Date.now();
      this._refreshReloadState(p, now);
      if (!p || p.dead || p.reloading) return false;
      if (p.ammo <= 0) {
        this._startReload(p, now);
        return false;
      }
      p.ammo = Math.max(0, p.ammo - 1);
      if (p.ammo === 0) this._startReload(p, now);
      return true;
    }

    _applyBotDamage(botId, dmg) {
      this._applyDamage(botId, dmg, null);
    }

    _spawnBullet(ox, oy, angle, local) {
      const cos = Math.cos(angle), sin = Math.sin(angle);
      const ray = castRay(this.map, ox, oy, angle);
      this.bullets.push({
        x: ox, y: oy,
        vx: cos * 480, vy: sin * 480,
        maxDist: ray.dist,
        travelDist: 0,
        ttl: 0.8,
        local,
      });
    }

    _updateBullets(dt) {
      for (const b of this.bullets) {
        const step = 480 * dt;
        b.x += b.vx * dt;
        b.y += b.vy * dt;
        b.travelDist += step;
        b.ttl -= dt;
      }
      this.bullets = this.bullets.filter(b => b.ttl > 0 && b.travelDist < b.maxDist + 8);
    }

    // ── Door interaction ───────────────────────────────────────────────────
    _interactDoor() {
      const me = this.players.get(this.myId);
      if (!me || me.dead) return;
      let closest = null, closestDist = DOOR_D * DOOR_D;
      for (const d of this.map.doors) {
        const dx = d.x * TS + TS / 2 - me.x;
        const dy = d.y * TS + TS / 2 - me.y;
        const dd = dx * dx + dy * dy;
        if (dd < closestDist) { closestDist = dd; closest = d; }
      }
      if (closest) {
        if (this.isHost) {
          closest.open = !closest.open;
          this._redrawMap();
          this._broadcast({ type: 'door', x: closest.x, y: closest.y, open: closest.open });
        } else {
          this._sendTo(this.hostId, { type: 'doorRequest', x: closest.x, y: closest.y });
        }
      }
    }

    // ── Death & Respawn ────────────────────────────────────────────────────
    _die() {
      if (this.isHost) this._applyDamage(this.myId, MAX_HP, null);
    }

    // Returns a spawn index for the given player: team-based in team mode, random otherwise
    _pickRespawnIdx(player) {
      const n = this.map.spawns.length;
      if (this._isTeamMode() && this.teamSpawnIdxs) {
        return this.teamSpawnIdxs[player.team ?? 0] ?? 0;
      }
      return Math.floor(Math.random() * n);
    }

    _respawn() {
      if (this.isHost) this._respawnPlayer(this.myId);
    }

    // ── Indicators ─────────────────────────────────────────────────────────
    _updateIndicators(dt) {
      for (const s of this.shotInds) s.ttl -= dt;
      this.shotInds = this.shotInds.filter(s => s.ttl > 0);
      for (const s of this.soundInds) s.ttl -= dt;
      this.soundInds = this.soundInds.filter(s => s.ttl > 0);
    }

    // Push a sound-arc indicator if the source is within hearing range and not self
    _pushSoundInd(wx, wy, type) {
      const me = this.players.get(this.myId);
      if (!me) return;
      const d = Math.hypot(wx - me.x, wy - me.y);
      if (d > 0 && d < SOUND_RANGE) {
        this.soundInds.push({ wx, wy, ttl: SOUND_TTL, type });
      }
    }

    // ── Bot: Add ───────────────────────────────────────────────────────────
    _addBot(broadcast = true, spawnIdx = null) {
      const botId   = 'bot-' + this.botCount;
      this.botCount += 1;
      const resolvedSpawnIdx = spawnIdx !== null
        ? spawnIdx
        : Math.floor(Math.random() * this.map.spawns.length);
      const sp      = this.map.spawns[resolvedSpawnIdx];
      const bot     = mkPlayer(botId, sp.x, sp.y);
      bot.isBot        = true;
      bot.respawnAt    = 0;
      bot.livesLeft    = this.roomSettings.lives || 0;
      bot.botState     = 'wander';     // 'wander' | 'chase'
      bot.botTarget    = null;         // {x, y} movement target
      bot.botTimer     = 0;            // time until next wander-target pick
      bot.botShootTimer = BOT_SHOOT_CD * this.botRng(); // stagger initial shot
      this.players.set(botId, bot);
      if (broadcast) {
        // Tell all connected peers about this new bot (in-game late-add scenario)
        this._broadcast({ type: 'playerJoin', player: this._serializePlayer(botId, bot) });
      }
    }

    // ── Bot: Update (host only) ────────────────────────────────────────────
    _updateBots(dt) {
      if (!this.isHost) return;

      for (const [id, bot] of this.players) {
        if (!bot.isBot || bot.dead) continue;

        // ── 1. Find nearest living enemy player ──────────────────────────
        let nearestDist = Infinity, nearestTarget = null;
        for (const [pid, p] of this.players) {
          if (pid === id || p.dead) continue;
          // In team mode, bots only target enemies (different team)
          if (this._isTeamMode() && p.team === bot.team) continue;
          const d2 = dist2(bot.x, bot.y, p.x, p.y);
          if (d2 < nearestDist) { nearestDist = d2; nearestTarget = p; }
        }

        // ── 2. State transitions ──────────────────────────────────────────
        bot.botTimer -= dt;
        if (nearestTarget && nearestDist < BOT_SIGHT * BOT_SIGHT) {
          bot.botState  = 'chase';
          bot.botTarget = { x: nearestTarget.x, y: nearestTarget.y };
        } else if (bot.botTimer <= 0) {
          bot.botState  = 'wander';
          bot.botTarget = this._randomFloorPoint();
          bot.botTimer  = 2 + this.botRng() * 3;
        }

        // ── 3. Movement ───────────────────────────────────────────────────
        if (bot.botTarget) {
          const tdx = bot.botTarget.x - bot.x;
          const tdy = bot.botTarget.y - bot.y;
          const d   = Math.hypot(tdx, tdy);
          if (d > 6) {
            bot.angle = Math.atan2(tdy, tdx);
            const prevX = bot.x, prevY = bot.y;
            this._movePlayer(bot, (tdx / d) * BOT_SPD * dt, (tdy / d) * BOT_SPD * dt);
            // Host-side footstep sound arc
            if (Math.hypot(bot.x - prevX, bot.y - prevY) > 0.5) {
              this._pushSoundInd(bot.x, bot.y, 'step');
            }
          } else if (bot.botState === 'wander') {
            bot.botTarget = null;
          }
        }

        // ── 4. Shooting ───────────────────────────────────────────────────
        bot.botShootTimer -= dt;
        if (nearestTarget && bot.botShootTimer <= 0 &&
            nearestDist < BOT_SIGHT * BOT_SIGHT) {
          const angleToPlayer = Math.atan2(
            nearestTarget.y - bot.y, nearestTarget.x - bot.x
          );
          // Snap aim toward player (with slight imprecision)
          const spread = (this.botRng() - 0.5) * 0.35;
          bot.angle = angleToPlayer + spread;

          const angleDiff = Math.abs(normalizeAngle(bot.angle - angleToPlayer));
          if (angleDiff < BOT_AIM_TOL) {
            if (this._botShoot(bot)) {
              bot.botShootTimer = BOT_SHOOT_CD + (this.botRng() - 0.5) * 0.6;
            }
          }
        }
      }
    }

    _randomFloorPoint() {
      const { tiles } = this.map;
      // Try up to 40 times to find a random floor tile
      for (let i = 0; i < 40; i++) {
        const tx = 1 + Math.floor(this.botRng() * (MW - 2));
        const ty = 1 + Math.floor(this.botRng() * (MH - 2));
        if (tiles[ty][tx] === T.FLOOR) {
          return { x: (tx + 0.5) * TS, y: (ty + 0.5) * TS };
        }
      }
      // Fallback to a spawn point
      return { ...this.map.spawns[0] };
    }

    _botShoot(bot) {
      if (!this._consumeAmmoAndReload(bot)) return false;
      playShot(false);
      this._spawnBullet(bot.x, bot.y, bot.angle, false);

      const targetId = this._findShotTarget(bot);
      if (targetId) this._applyDamage(targetId, MAX_HP, bot.id);

      // Broadcast shot indicator to all peers
      this._broadcast({
        type: 'shot', id: bot.id,
        x: bot.x, y: bot.y, angle: bot.angle,
      });
      // Host-side sound arc for bot shot
      this._pushSoundInd(bot.x, bot.y, 'shot');
      return true;
    }

    // ── Camera ─────────────────────────────────────────────────────────────
    _updateCamera(me) {
      const cx = me.dead ? this.specCamX : me.x;
      const cy = me.dead ? this.specCamY : me.y;
      this.world.x = Math.round(this.app.screen.width  / 2 - cx);
      this.world.y = Math.round(this.app.screen.height / 2 - cy);
    }

    // ── Render: Players ────────────────────────────────────────────────────
    _renderPlayers() {
      const g = this.playGfx;
      g.clear();

      const me = this.players.get(this.myId);

      for (const [id, p] of this.players) {
        const isSelf = id === this.myId;

        // Hide enemy/bot players that are outside the local player's FOV
        if (!isSelf && me && !me.dead && !isInFov(this.map, me, p)) continue;

        let col;
        if (p.dead)        col = C.DEAD_P;
        else if (isSelf)   col = C.SELF;
        else if (this._isTeamMode()) {
          const myTeam = me ? (me.team ?? 0) : 0;
          col = (p.team === myTeam) ? C.TEAM_A : C.TEAM_B;
        }
        else if (p.isBot)  col = C.BOT;
        else               col = C.ENEMY;

        // Body circle
        g.beginFill(col, p.dead ? 0.4 : 1);
        g.drawCircle(p.x, p.y, P_RAD);
        g.endFill();

        // Direction indicator line
        if (!p.dead) {
          g.lineStyle(2, col, 0.9);
          g.moveTo(p.x, p.y);
          g.lineTo(p.x + Math.cos(p.angle) * P_RAD * 2.2,
                   p.y + Math.sin(p.angle) * P_RAD * 2.2);
          g.lineStyle(0);
        }

        // HP bar (world-space, above player)
        if (!p.dead) {
          const bw = 30, bh = 4;
          const bx = p.x - bw / 2, by = p.y - P_RAD - 10;
          g.beginFill(C.HP_BG);
          g.drawRect(bx, by, bw, bh);
          g.endFill();
          const hpCol = p.hp > 40 ? C.HP_FG : C.HP_LOW;
          g.beginFill(hpCol);
          g.drawRect(bx, by, bw * (p.hp / MAX_HP), bh);
          g.endFill();
        }

        // "DEAD" text indicator
        if (p.dead && isSelf) {
          // handled in HUD
        }
      }
    }

    // ── Render: Bullets ────────────────────────────────────────────────────
    _renderBullets() {
      const g = this.bullGfx;
      g.clear();
      for (const b of this.bullets) {
        const alpha = clamp(b.ttl * 3, 0, 1);
        g.beginFill(C.BULLET, alpha);
        g.drawCircle(b.x, b.y, 3);
        g.endFill();
        // Trail
        const trail = 16;
        g.lineStyle(1.5, C.BULLET, alpha * 0.4);
        g.moveTo(b.x, b.y);
        g.lineTo(b.x - Math.cos(Math.atan2(b.vy, b.vx)) * trail,
                 b.y - Math.sin(Math.atan2(b.vy, b.vx)) * trail);
        g.lineStyle(0);
      }
    }

    // ── Render: Darkness / FOV ─────────────────────────────────────────────
    _renderDarkness(me) {
      const { app, darkRT, darkFill, darkAmb, darkFov } = this;
      const W = app.screen.width, H = app.screen.height;

      // Spectators see the full map – no darkness overlay
      if (me.dead) {
        darkFill.clear();
        app.renderer.render(darkFill, { renderTexture: darkRT, clear: true });
        return;
      }

      // 1. Fill render texture with opaque black
      const cx = W / 2, cy = H / 2;
      darkFill.clear();
      darkFill.beginFill(0x000000, 0.96);
      darkFill.drawRect(0, 0, W, H);
      darkFill.endFill();
      app.renderer.render(darkFill, { renderTexture: darkRT, clear: true });

      // 2. Erase ambient circle (always visible around player)
      darkAmb.clear();
      darkAmb.beginFill(0xFFFFCC, 1);
      darkAmb.drawCircle(cx, cy, AMB_R);
      darkAmb.endFill();
      app.renderer.render(darkAmb, { renderTexture: darkRT, clear: false });

      // 3. Erase FOV cone (player is alive at this point)
      {
        const worldPts = buildFovPoly(this.map, me.x, me.y, me.angle);
        // Transform to screen-space
        const offX = cx - me.x, offY = cy - me.y;
        const screenPts = [cx, cy]; // apex = player center
        for (let i = 0; i < worldPts.length; i += 2) {
          screenPts.push(worldPts[i] + offX, worldPts[i + 1] + offY);
        }
        darkFov.clear();
        darkFov.beginFill(0xFFFFCC, 1);
        darkFov.drawPolygon(screenPts);
        darkFov.endFill();
        app.renderer.render(darkFov, { renderTexture: darkRT, clear: false });
      }
    }

    // ── Render: Shot Indicators ────────────────────────────────────────────
    _renderIndicators(me) {
      const g = this.indGfx;
      g.clear();
      if (me.dead || !this.shotInds.length) return;

      const cx = this.app.screen.width  / 2;
      const cy = this.app.screen.height / 2;
      const offX = cx - me.x, offY = cy - me.y;

      for (const s of this.shotInds) {
        const alpha = clamp(s.ttl / IND_TTL, 0, 1);
        // Direction from shooter to shot destination (world space)
        const dx = Math.cos(s.angle), dy = Math.sin(s.angle);

        // Screen position of the shooter
        const sx = s.wx + offX, sy = s.wy + offY;

        // Arrow: draw from screen-edge pointing toward shooter
        const edgeDist = 80;
        const toShX = sx - cx, toShY = sy - cy;
        const len = Math.hypot(toShX, toShY) || 1;
        const norm = len > 1 ? 1 / len : 1;

        // Arrow tip on screen (clamped near shooter or edge)
        const tipX = cx + clamp(toShX, -cx + 40, cx - 40);
        const tipY = cy + clamp(toShY, -cy + 40, cy - 40);

        // Arrow body
        const arrowLen = 28;
        const ax = (toShX * norm) * arrowLen;
        const ay = (toShY * norm) * arrowLen;

        g.lineStyle(3, C.IND, alpha * 0.9);
        g.moveTo(tipX - ax, tipY - ay);
        g.lineTo(tipX,      tipY);
        g.lineStyle(0);

        // Arrowhead
        const perpX = -ay / arrowLen * 10, perpY = ax / arrowLen * 10;
        g.beginFill(C.IND, alpha * 0.9);
        g.drawPolygon([
          tipX, tipY,
          tipX - ax * 0.5 + perpX, tipY - ay * 0.5 + perpY,
          tipX - ax * 0.5 - perpX, tipY - ay * 0.5 - perpY,
        ]);
        g.endFill();

        // Shot line (red dashed line showing bullet path)
        g.lineStyle(1, C.IND, alpha * 0.35);
        g.moveTo(sx, sy);
        g.lineTo(sx + dx * FOV_DIST, sy + dy * FOV_DIST);
        g.lineStyle(0);
      }
    }

    // ── Render: Sound Arc Indicators ──────────────────────────────────────
    _renderSoundInds(me) {
      const g = this.soundGfx;
      g.clear();
      if (me.dead || !this.soundInds.length) return;

      const cx = this.app.screen.width  / 2;
      const cy = this.app.screen.height / 2;

      for (const s of this.soundInds) {
        const alpha = clamp(s.ttl / SOUND_TTL, 0, 1);
        // Direction from local player toward the sound source (world space)
        const angle = Math.atan2(s.wy - me.y, s.wx - me.x);
        const col   = s.type === 'shot' ? C.IND : C.SOUND_IND;

        // Draw arc as polyline at fixed radius from screen centre
        const segs = 18;
        g.lineStyle(3.5, col, alpha * 0.88);
        for (let i = 0; i <= segs; i++) {
          const a = angle - SOUND_ARC_HALF + (i / segs) * SOUND_ARC_HALF * 2;
          const x = cx + Math.cos(a) * SOUND_ARC_R;
          const y = cy + Math.sin(a) * SOUND_ARC_R;
          if (i === 0) g.moveTo(x, y);
          else         g.lineTo(x, y);
        }
        g.lineStyle(0);

        // Small filled tip at the midpoint of the arc to indicate direction
        const tx = cx + Math.cos(angle) * (SOUND_ARC_R - SOUND_TIP_OFFSET);
        const ty = cy + Math.sin(angle) * (SOUND_ARC_R - SOUND_TIP_OFFSET);
        g.beginFill(col, alpha * 0.75);
        g.drawCircle(tx, ty, 4);
        g.endFill();
      }
    }

    // ── Render: HUD ────────────────────────────────────────────────────────
    _renderHUD(me) {
      const g   = this.hudGfx;
      const W   = this.app.screen.width;
      const H   = this.app.screen.height;
      g.clear();

      // HP bar (bottom-center)
      const bw = 160, bh = 12, bx = (W - bw) / 2, by = H - 36;
      g.beginFill(C.HP_BG);
      g.drawRoundedRect(bx, by, bw, bh, 4);
      g.endFill();
      const hpRatio = me.hp / MAX_HP;
      const hpCol   = me.hp > 40 ? C.HP_FG : C.HP_LOW;
      g.beginFill(hpCol);
      g.drawRoundedRect(bx, by, bw * hpRatio, bh, 4);
      g.endFill();
      g.lineStyle(1, 0x555555);
      g.drawRoundedRect(bx, by, bw, bh, 4);
      g.lineStyle(0);

      const now = Date.now();
      this._refreshReloadState(me, now);
      if (this.domAmmo) {
        if (me.dead) {
          this.domAmmo.textContent = `彈藥: ${MAG_SIZE}/${MAG_SIZE}`;
        } else if (me.reloading) {
          const remain = Math.max(0, ((me.reloadUntil || 0) - now) / 1000);
          this.domAmmo.textContent = `裝填中... ${remain.toFixed(1)}s`;
        } else {
          this.domAmmo.textContent = `彈藥: ${me.ammo}/${MAG_SIZE}`;
        }
      }
      if (this.domMode) {
        if (this.roomSettings.gameMode === 'team_deathmatch') {
          this.domMode.textContent = `模式：${this._modeLabel()}（${TEAM_KILL_LIMIT} 擊殺）`;
        } else if (this.roomSettings.gameMode === 'team_survival') {
          this.domMode.textContent = `模式：${this._modeLabel()}（殲滅敵隊）`;
        } else {
          this.domMode.textContent = `模式：${this._modeLabel()}（${FFA_KILL_LIMIT} 擊殺）`;
        }
      }

      // Lives display
      if (this.domLives) {
        const lives = this.roomSettings.lives || 0;
        if (lives > 0) {
          const myPlayer = this.players.get(this.myId);
          const left = myPlayer ? (myPlayer.livesLeft || 0) : lives;
          this.domLives.textContent = `生命：${'❤️'.repeat(left)}${left === 0 ? '💀' : ''}（${left}/${lives}）`;
        } else {
          this.domLives.textContent = '';
        }
      }

      // Door prompt (DOM)
      let doorNearby = null;
      for (const d of this.map.doors) {
        const dx = d.x * TS + TS / 2 - me.x;
        const dy = d.y * TS + TS / 2 - me.y;
        if (dx * dx + dy * dy < DOOR_D * DOOR_D) { doorNearby = d; break; }
      }
      const isMobile = 'ontouchstart' in window;
      if (doorNearby && !me.dead) {
        const actionLabel = doorNearby.open ? '關門' : '開門';
        this.domDoorPrmpt.textContent = isMobile ? actionLabel : `[E] ${actionLabel}`;
        this.domDoorPrmpt.classList.add('show');
        this.domBtnInteract.textContent = actionLabel;
        this.domBtnInteract.classList.add('show');
      } else {
        this.domDoorPrmpt.classList.remove('show');
        this.domBtnInteract.classList.remove('show');
      }

      // Dead overlay (DOM)
      if (me.dead) {
        const lives = this.roomSettings.lives || 0;
        const permanentlyDead = lives > 0 && (me.livesLeft || 0) <= 0;
        const isMobile = 'ontouchstart' in window;
        const spectateHint = isMobile ? '（左搖桿移動視角）' : '（WASD 移動視角觀戰）';
        if (permanentlyDead) {
          this.domRespawn.textContent = `你已陣亡（無剩餘生命）${spectateHint}`;
        } else if (me.respawnAt) {
          const remain = Math.max(0, (me.respawnAt - Date.now()) / 1000);
          this.domRespawn.textContent = `${remain.toFixed(1)} 秒後重生… ${spectateHint}`;
        } else {
          this.domRespawn.textContent = `${RESPAWN_S.toFixed(1)} 秒後重生… ${spectateHint}`;
        }
        this.domDead.classList.add('show');
      } else {
        this.domDead.classList.remove('show');
      }
    }

    // ── Render: Joysticks ─────────────────────────────────────────────────
    _renderJoysticks() {
      const g = this.joyGfx;
      g.clear();

      if (!this.jL.on && !this.jR.on) return;

      const radius = 50, innerR = 22;

      const drawStick = (j) => {
        // Origin is always the initial touch point
        const ox = j.ox, oy = j.oy;
        const maxR = 55;
        const len  = Math.hypot(j.dx, j.dy);
        const clamped = Math.min(len, maxR);
        const nx = len > 0 ? j.dx / len * clamped : 0;
        const ny = len > 0 ? j.dy / len * clamped : 0;

        // Base ring
        g.lineStyle(2, 0xffffff, 0.18);
        g.beginFill(0xffffff, 0.06);
        g.drawCircle(ox, oy, radius);
        g.endFill();
        g.lineStyle(0);

        // Knob
        g.beginFill(0xffffff, 0.45);
        g.drawCircle(ox + nx, oy + ny, innerR);
        g.endFill();
      };

      if (this.jL.on) drawStick(this.jL);
      if (this.jR.on) drawStick(this.jR);
    }

    // ── Network: State Sync ───────────────────────────────────────────────
    _syncState(dt, me) {
      this.syncTimer += dt * 1000;
      if (this.syncTimer < SYNC_MS) return;
      this.syncTimer = 0;
      if (!this.conns.size) return;
      if (this.isHost) {
        this._broadcastAllPlayerStates();
      } else if (!me.dead) {
        // Dead players don't send position – host already knows their dead state
        this._sendTo(this.hostId, {
          type: 'stateRequest',
          x: me.x,
          y: me.y,
          angle: me.angle,
        });
      }
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // PLAYER FACTORY
  // ─────────────────────────────────────────────────────────────────────────

  function mkPlayer(id, x, y) {
    return {
      id, x, y, angle: 0, hp: MAX_HP, dead: false,
      ammo: MAG_SIZE, reloading: false, reloadUntil: 0,
      kills: 0, deaths: 0, livesLeft: 0,
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // BOOT
  // ─────────────────────────────────────────────────────────────────────────

  window.addEventListener('DOMContentLoaded', () => {
    if (typeof PIXI === 'undefined') {
      document.getElementById('status-msg').textContent = '載入 pixi.js 失敗，請檢查網路後重新整理。';
      return;
    }
    window._game = new Game();
  });

})();
