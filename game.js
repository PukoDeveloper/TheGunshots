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
  const RESPAWN_S = 3.5;           // respawn delay (s)
  const MAX_HP    = 100;

  // ── Joystick constants ────────────────────────────────────────────────
  const JOY_DEAD_ZONE = 8;         // minimum joystick offset to register input (px)
  const JOY_MAX_R     = 60;        // joystick offset for full-speed movement (px)

  // ── Bot constants ─────────────────────────────────────────────────────
  const BOT_SPD       = 110;       // bot movement speed (px/s)
  const BOT_SHOOT_CD  = 1.8;       // seconds between bot shots
  const BOT_SIGHT     = 280;       // bot detection radius (px)
  const BOT_AIM_TOL   = Math.PI / 5; // ±36° aim tolerance before bot shoots
  const MAX_BOTS      = 4;         // max bots per room

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
    DEAD_P:   0x555555,
    BULLET:   0xFFFF55,
    IND:      0xff2222,
    HP_BG:    0x2a2a2a,
    HP_FG:    0x44ee44,
    HP_LOW:   0xee4422,
  };

  // Selector for interactive UI elements that should not have touch events intercepted
  const INTERACTIVE_SELECTOR = 'button, input, a';

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
      this.running  = false;
      this.syncTimer = 0;

      // ── Bot state ──────────────────────────────────────────────────────
      this.botCount = 0;
      this.botRng   = mkRng(Date.now());

      // ── Waiting room state ─────────────────────────────────────────────
      this.roomSettings  = { mapSize: 'medium' };
      this.waitingPeerIds = [];   // peer IDs of non-host players in waiting room
      this.hostId        = null;  // PeerJS ID of the host

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

      // ── DOM HUD refs ───────────────────────────────────────────────────
      this.domHud       = document.getElementById('hud-overlay');
      this.domDead      = document.getElementById('hud-dead');
      this.domRespawn   = document.getElementById('hud-respawn-msg');
      this.domDoorPrmpt = document.getElementById('hud-door-prompt');
      this.domRoomCode  = document.getElementById('hud-room-code');
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

      // Shot indicators + HUD + joystick (screen-space)
      this.indGfx = new PIXI.Graphics();
      this.hudGfx = new PIXI.Graphics();
      this.joyGfx = new PIXI.Graphics();
      app.stage.addChild(this.indGfx);
      app.stage.addChild(this.hudGfx);
      app.stage.addChild(this.joyGfx);

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
        if (this.running) this._shoot();
      });

      // Touch – split screen into left (move) and right (aim/shoot)
      window.addEventListener('touchstart', e => this._onTouchStart(e), { passive: false });
      window.addEventListener('touchmove',  e => this._onTouchMove(e),  { passive: false });
      window.addEventListener('touchend',   e => this._onTouchEnd(e),   { passive: false });
      window.addEventListener('touchcancel',e => this._onTouchEnd(e),   { passive: false });

      // Mobile action buttons
      this.domBtnShoot.addEventListener('touchstart', e => { e.preventDefault(); if (this.running) this._shoot(); }, { passive: false });
      this.domBtnShoot.addEventListener('click', () => { if (this.running) this._shoot(); });
      this.domBtnInteract.addEventListener('touchstart', e => { e.preventDefault(); if (this.running) this._interactDoor(); }, { passive: false });
      this.domBtnInteract.addEventListener('click', () => { if (this.running) this._interactDoor(); });
    }

    _onTouchStart(e) {
      // Don't intercept touches on buttons/inputs so click handlers still fire
      if (e.target.closest(INTERACTIVE_SELECTOR)) return;
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
      e.preventDefault();
      for (const t of e.changedTouches) {
        if (this.jL.on && t.identifier === this.jL.id) {
          this.jL.dx = t.clientX - this.jL.ox;
          this.jL.dy = t.clientY - this.jL.oy;
          if (this.running) {
            // Update facing from movement direction when no right joystick
            if (!this.jR.on) {
              const me = this.players.get(this.myId);
              const len = Math.hypot(this.jL.dx, this.jL.dy);
              if (me && len > 5) me.angle = Math.atan2(this.jL.dy, this.jL.dx);
            }
          }
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
      // Don't intercept touches on buttons/inputs so click handlers still fire
      if (e.target.closest(INTERACTIVE_SELECTOR)) return;
      e.preventDefault();
      for (const t of e.changedTouches) {
        if (this.jL.on && t.identifier === this.jL.id) {
          this.jL = { on: false, ox: 0, oy: 0, dx: 0, dy: 0, id: null };
        }
        if (this.jR.on && t.identifier === this.jR.id) {
          this.jR = { on: false, ox: 0, oy: 0, dx: 0, dy: 0, id: null, shotPending: false };
        }
      }
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
        this._initPeer(null, peerId => {
          this.isHost = true;
          this.hostId = peerId;
          const code = peerId.slice(0, 8).toUpperCase();
          this._showWaitingRoom(true, code);
        }, err => {
          createBtn.disabled = false;
          statusEl.textContent = '建立失敗：' + err;
        });
      });

      joinBtn.addEventListener('click', () => {
        const code = joinInput.value.trim().toUpperCase();
        if (code.length < 6) { statusEl.textContent = '請輸入正確代碼'; return; }
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

      // Waiting room: click code to copy
      document.getElementById('wr-code').addEventListener('click', () => {
        const el = document.getElementById('wr-code');
        const code = el.textContent;
        navigator.clipboard?.writeText(code).then(() => {
          el.textContent = '已複製！';
          setTimeout(() => { el.textContent = code; }, 1200);
        });
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

      // Waiting room: start game (host only)
      document.getElementById('btn-start-game').addEventListener('click', () => {
        if (!this.isHost) return;
        const size = MAP_SIZES[this.roomSettings.mapSize] || MAP_SIZES.medium;
        MW = size.w; MH = size.h;
        const seed = randomSeed();
        this.map = generateMap(seed);
        let spIdx = 1;
        for (const [pid] of this.conns) {
          this._sendTo(pid, {
            type: 'welcome',
            seed,
            spawnIdx: spIdx % this.map.spawns.length,
            mapSize: this.roomSettings.mapSize,
            players: [],
          });
          spIdx++;
        }
        this._startGame();
      });

      // "加入 Bot" button in HUD – only used by host
      this.domBotBar   = document.getElementById('hud-bot-bar');
      this.domBotCount = document.getElementById('hud-bot-count');
      document.getElementById('btn-add-bot').addEventListener('click', () => {
        if (!this.running || !this.isHost) return;
        this._addBot();
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
        this.players.delete(pid);
        if (!this.running) {
          this.waitingPeerIds = this.waitingPeerIds.filter(id => id !== pid);
          if (this.isHost) {
            this._broadcast({ type: 'playerListUpdate', peerIds: [...this.waitingPeerIds] });
          }
          this._updateWaitingRoomUI();
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

    _onMsg(fromId, msg) {
      switch (msg.type) {
        case 'hello':
          // Client joined: send map seed + current players (or waiting room state)
          if (this.isHost) {
            if (this.running) {
              // Late joiner: game already in progress – send map info immediately
              const spawnIdx = this.conns.size % this.map.spawns.length;
              this._sendTo(fromId, {
                type: 'welcome',
                seed: this.map.seed,
                spawnIdx,
                mapSize: this.roomSettings.mapSize,
                players: [...this.players.entries()].map(([id, p]) => ({
                  id, x: p.x, y: p.y, angle: p.angle, hp: p.hp, isBot: p.isBot || false,
                })),
              });
              // Tell existing players about the newcomer
              this._broadcast({ type: 'playerJoin', id: fromId }, fromId);
            } else {
              // Waiting room: add peer to the waiting list and notify everyone
              if (!this.waitingPeerIds.includes(fromId)) {
                this.waitingPeerIds.push(fromId);
              }
              this._sendTo(fromId, {
                type: 'waitingAck',
                hostId: this.myId,
                settings: this.roomSettings,
                peerIds: [...this.waitingPeerIds],
              });
              this._broadcast({ type: 'playerListUpdate', peerIds: [...this.waitingPeerIds] }, fromId);
              this._updateWaitingRoomUI();
            }
          }
          break;

        case 'waitingAck':
          // We (client) entered the waiting room
          this.hostId = msg.hostId;
          this.waitingPeerIds = msg.peerIds;
          this.roomSettings = msg.settings;
          this._showWaitingRoom(false);
          this._updateWaitingRoomUI();
          this._updateWaitingSettings();
          break;

        case 'playerListUpdate':
          // Host updated the waiting room player list
          this.waitingPeerIds = msg.peerIds;
          this._updateWaitingRoomUI();
          break;

        case 'settingsUpdate':
          // Host changed room settings
          this.roomSettings = msg.settings;
          this._updateWaitingSettings();
          break;

        case 'welcome':
          // We (client) received map + spawn from host – start the game
          if (msg.mapSize) {
            const sz = MAP_SIZES[msg.mapSize];
            if (sz) { MW = sz.w; MH = sz.h; }
          }
          this.map = generateMap(msg.seed);
          const sp = this.map.spawns[msg.spawnIdx % this.map.spawns.length];
          this.players.set(this.myId, mkPlayer(this.myId, sp.x, sp.y));
          // Add existing players
          for (const pd of msg.players) {
            if (pd.id !== this.myId) {
              const existing = mkPlayer(pd.id, pd.x, pd.y);
              if (pd.isBot) existing.isBot = true;
              this.players.set(pd.id, existing);
            }
          }
          this._startGame();
          break;

        case 'playerJoin':
          if (!this.players.has(msg.id)) {
            const spIdx = this.players.size % this.map.spawns.length;
            const s = this.map.spawns[spIdx];
            const joined = mkPlayer(msg.id, s.x, s.y);
            if (msg.id.startsWith('bot-')) joined.isBot = true;
            this.players.set(msg.id, joined);
          }
          break;

        case 'state':
          if (msg.id !== this.myId) {
            let p = this.players.get(msg.id);
            if (!p) { p = mkPlayer(msg.id, msg.x, msg.y); this.players.set(msg.id, p); }
            p.x = msg.x; p.y = msg.y; p.angle = msg.angle; p.hp = msg.hp;
            p.dead = msg.dead;
            if (msg.isBot) p.isBot = true;
          }
          break;

        case 'shot':
          if (msg.id !== this.myId) {
            playShot(false);
            this.shotInds.push({ wx: msg.x, wy: msg.y, angle: msg.angle, ttl: IND_TTL });
            // Visual bullet trail from the shooter's perspective
            this._spawnBullet(msg.x, msg.y, msg.angle, false);
          }
          break;

        case 'hit':
          if (msg.target === this.myId) {
            const me = this.players.get(this.myId);
            if (me && !me.dead) {
              me.hp = Math.max(0, me.hp - msg.dmg);
              if (me.hp <= 0) this._die();
            }
          }
          break;

        case 'door':
          const d = this.map.doors.find(d => d.x === msg.x && d.y === msg.y);
          if (d) d.open = msg.open;
          this._redrawMap();
          break;

        case 'respawn':
          if (msg.id !== this.myId) {
            const p2 = this.players.get(msg.id);
            if (p2) { p2.x = msg.x; p2.y = msg.y; p2.hp = MAX_HP; p2.dead = false; }
          }
          break;
      }
    }

    // ══════════════════════════════════════════════════════════════════════
    // GAME LIFECYCLE
    // ══════════════════════════════════════════════════════════════════════

    _startGame() {
      // Spawn local player if not already created
      if (!this.players.has(this.myId)) {
        const spawnIdx = this.isHost ? 0 : (this.players.size % this.map.spawns.length);
        const sp = this.map.spawns[spawnIdx];
        this.players.set(this.myId, mkPlayer(this.myId, sp.x, sp.y));
      }

      this._redrawMap();

      // Show room code in HUD corner
      const code = this.myId.slice(0, 8).toUpperCase();
      this.domRoomCode.textContent = '房間: ' + code;
      this.domRoomCode.classList.add('show');

      // Show bot bar only for host
      if (this.isHost) {
        this.domBotBar.classList.add('show');
        this._updateBotCountDisplay();
      }

      // Hide lobby and waiting room, show canvas + HUD
      document.getElementById('lobby').style.display = 'none';
      document.getElementById('waiting-room').style.display = 'none';
      document.getElementById('canvas-wrap').style.display = 'block';
      this.domHud.style.display = 'block';

      this.running = true;
    }

    _updateBotCountDisplay() {
      if (this.domBotCount) {
        this.domBotCount.textContent = this.botCount + ' / ' + MAX_BOTS;
      }
      const addBtn = document.getElementById('btn-add-bot');
      if (addBtn) addBtn.disabled = this.botCount >= MAX_BOTS;
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

      document.getElementById('wr-settings-card').style.display = isHost ? 'flex' : 'none';
      document.getElementById('btn-start-game').style.display   = isHost ? 'block' : 'none';
      document.getElementById('wr-waiting-msg').style.display   = isHost ? 'none' : 'block';

      // Disable size buttons for non-host clients (read-only view)
      document.querySelectorAll('.size-btn').forEach(b => { b.disabled = !isHost; });

      this._updateWaitingRoomUI();
      this._updateWaitingSettings();
    }

    _updateWaitingRoomUI() {
      const el = document.getElementById('wr-players');
      if (!el) return;

      const hostId    = this.hostId || this.myId;
      const hostShort = hostId.slice(0, 8).toUpperCase();
      const hostIsMe  = hostId === this.myId;

      const entries = [
        `<div class="player-entry is-host${hostIsMe ? ' is-self' : ''}">` +
        `🎮 ${hostShort}` +
        `${hostIsMe ? '（你·房主）' : '（房主）'}</div>`,
      ];

      for (const pid of this.waitingPeerIds) {
        const short = pid.slice(0, 8).toUpperCase();
        const isMe  = pid === this.myId;
        entries.push(
          `<div class="player-entry${isMe ? ' is-self' : ''}">` +
          `👤 ${short}${isMe ? '（你）' : ''}</div>`
        );
      }

      el.innerHTML = entries.join('');

      // Update start button label with player count (host only)
      const startBtn = document.getElementById('btn-start-game');
      if (startBtn) {
        const total = 1 + this.waitingPeerIds.length;
        startBtn.textContent = `▶ 開始遊戲（${total} 人）`;
      }
    }

    _updateWaitingSettings() {
      document.querySelectorAll('.size-btn').forEach(b => {
        b.classList.toggle('active', b.dataset.size === this.roomSettings.mapSize);
      });
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
      this._renderHUD(me);
      this._renderJoysticks();
      this._syncState(dt, me);
    }

    // ── Movement ───────────────────────────────────────────────────────────
    _updateMovement(dt, me) {
      if (me.dead) return;

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

      playShot(true);
      this._spawnBullet(me.x, me.y, me.angle, true);

      // Raycast for hit detection
      const ray = castRay(this.map, me.x, me.y, me.angle);
      for (const [id, p] of this.players) {
        if (id === this.myId || p.dead) continue;
        // Project player onto ray direction
        const dx = p.x - me.x, dy = p.y - me.y;
        const cos = Math.cos(me.angle), sin = Math.sin(me.angle);
        const proj  = dx * cos + dy * sin;        // along ray
        const perp  = Math.abs(dx * sin - dy * cos); // perpendicular distance
        if (proj > 0 && proj <= ray.dist + P_RAD && perp <= P_RAD * 1.4) {
          const dmg = MAX_HP;
          if (p.isBot) {
            // Apply bot damage locally (bots have no PeerJS connection)
            this._applyBotDamage(id, dmg);
          } else {
            this._broadcast({ type: 'hit', target: id, dmg });
          }
          break;
        }
      }

      // Broadcast shot event
      this._broadcast({ type: 'shot', id: this.myId, x: me.x, y: me.y, angle: me.angle });
    }

    _applyBotDamage(botId, dmg) {
      const bot = this.players.get(botId);
      if (!bot || bot.dead) return;
      bot.hp = Math.max(0, bot.hp - dmg);
      if (bot.hp <= 0) {
        bot.dead = true;
        // Respawn bot after delay
        setTimeout(() => {
          if (!this.players.has(botId)) return;
          const spIdx = this.botCount % this.map.spawns.length;
          const sp = this.map.spawns[spIdx];
          bot.x = sp.x; bot.y = sp.y;
          bot.hp = MAX_HP;
          bot.dead = false;
          bot.botState = 'wander';
          bot.botTarget = null;
        }, RESPAWN_S * 1000);
      }
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
        closest.open = !closest.open;
        this._redrawMap();
        this._broadcast({ type: 'door', x: closest.x, y: closest.y, open: closest.open });
      }
    }

    // ── Death & Respawn ────────────────────────────────────────────────────
    _die() {
      const me = this.players.get(this.myId);
      if (!me || me.dead) return;
      me.dead = true;
      me.hp = 0;
      setTimeout(() => this._respawn(), RESPAWN_S * 1000);
    }

    _respawn() {
      const me = this.players.get(this.myId);
      if (!me) return;
      const spIdx = [...this.players.keys()].indexOf(this.myId) % this.map.spawns.length;
      const sp = this.map.spawns[spIdx];
      me.x = sp.x; me.y = sp.y;
      me.hp = MAX_HP;
      me.dead = false;
      this._broadcast({ type: 'respawn', id: this.myId, x: me.x, y: me.y });
    }

    // ── Indicators ─────────────────────────────────────────────────────────
    _updateIndicators(dt) {
      for (const s of this.shotInds) s.ttl -= dt;
      this.shotInds = this.shotInds.filter(s => s.ttl > 0);
    }

    // ── Bot: Add ───────────────────────────────────────────────────────────
    _addBot() {
      if (this.botCount >= MAX_BOTS) return;
      const botId   = 'bot-' + this.botCount;
      this.botCount += 1;
      const spIdx   = (this.players.size) % this.map.spawns.length;
      const sp      = this.map.spawns[spIdx];
      const bot     = mkPlayer(botId, sp.x, sp.y);
      bot.isBot        = true;
      bot.botState     = 'wander';     // 'wander' | 'chase'
      bot.botTarget    = null;         // {x, y} movement target
      bot.botTimer     = 0;            // time until next wander-target pick
      bot.botShootTimer = BOT_SHOOT_CD * this.botRng(); // stagger initial shot
      this.players.set(botId, bot);
      // Tell all connected peers about this new bot
      this._broadcast({ type: 'playerJoin', id: botId });
      this._updateBotCountDisplay();
    }

    // ── Bot: Update (host only) ────────────────────────────────────────────
    _updateBots(dt) {
      if (!this.isHost) return;

      for (const [id, bot] of this.players) {
        if (!bot.isBot || bot.dead) continue;

        // ── 1. Find nearest living human player ──────────────────────────
        let nearestDist = Infinity, nearestTarget = null;
        for (const [pid, p] of this.players) {
          if (p.isBot || p.dead) continue;
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
            this._movePlayer(bot, (tdx / d) * BOT_SPD * dt, (tdy / d) * BOT_SPD * dt);
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
            this._botShoot(bot);
            bot.botShootTimer = BOT_SHOOT_CD + (this.botRng() - 0.5) * 0.6;
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
      playShot(false);
      this._spawnBullet(bot.x, bot.y, bot.angle, false);

      // Hit detection against human players
      const ray = castRay(this.map, bot.x, bot.y, bot.angle);
      for (const [pid, p] of this.players) {
        if (p.isBot || p.dead) continue;
        const dx  = p.x - bot.x, dy = p.y - bot.y;
        const cos = Math.cos(bot.angle), sin = Math.sin(bot.angle);
        const proj = dx * cos + dy * sin;
        const perp = Math.abs(dx * sin - dy * cos);
        if (proj > 0 && proj <= ray.dist + P_RAD && perp <= P_RAD * 1.4) {
          if (pid === this.myId) {
            // Apply to local player directly
            const me = this.players.get(this.myId);
            if (me && !me.dead) {
              me.hp = Math.max(0, me.hp - MAX_HP);
              if (me.hp <= 0) this._die();
            }
          } else {
            // Apply to remote peer via message
            this._sendTo(pid, { type: 'hit', target: pid, dmg: MAX_HP });
          }
          break;
        }
      }

      // Broadcast shot indicator to all peers
      this._broadcast({
        type: 'shot', id: bot.id,
        x: bot.x, y: bot.y, angle: bot.angle,
      });
    }

    // ── Camera ─────────────────────────────────────────────────────────────
    _updateCamera(me) {
      this.world.x = Math.round(this.app.screen.width  / 2 - me.x);
      this.world.y = Math.round(this.app.screen.height / 2 - me.y);
    }

    // ── Render: Players ────────────────────────────────────────────────────
    _renderPlayers() {
      const g = this.playGfx;
      g.clear();

      for (const [id, p] of this.players) {
        const isSelf = id === this.myId;
        let col;
        if (p.dead)        col = C.DEAD_P;
        else if (isSelf)   col = C.SELF;
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
      const cx = W / 2, cy = H / 2;

      // 1. Fill render texture with opaque black
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

      // 3. Erase FOV cone
      if (!me.dead) {
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
      if (!this.shotInds.length) return;

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
        this.domDead.classList.add('show');
      } else {
        this.domDead.classList.remove('show');
      }
    }

    // ── Render: Joysticks ─────────────────────────────────────────────────
    _renderJoysticks() {
      const g = this.joyGfx;
      g.clear();

      const isMobile = 'ontouchstart' in window;
      if (!isMobile && !this.jL.on && !this.jR.on) return;

      const radius = 50, innerR = 22;
      const W = this.app.screen.width, H = this.app.screen.height;

      const drawStick = (j, baseX, baseY) => {
        const ox = j.on ? j.ox : baseX;
        const oy = j.on ? j.oy : baseY;
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
        g.beginFill(0xffffff, j.on ? 0.45 : 0.22);
        g.drawCircle(ox + nx, oy + ny, innerR);
        g.endFill();
      };

      // Show left joystick always on mobile, when active otherwise
      if (isMobile || this.jL.on) {
        drawStick(this.jL, 90, H - 110);
      }
      // Right joystick
      if (isMobile || this.jR.on) {
        drawStick(this.jR, W - 90, H - 110);
      }
    }

    // ── Network: State Sync ───────────────────────────────────────────────
    _syncState(dt, me) {
      this.syncTimer += dt * 1000;
      if (this.syncTimer < SYNC_MS) return;
      this.syncTimer = 0;
      if (!this.conns.size) return;
      this._broadcast({
        type: 'state',
        id: this.myId,
        x: me.x, y: me.y,
        angle: me.angle,
        hp: me.hp,
        dead: me.dead,
      });
      // Host also syncs all bot states so peers can render them
      if (this.isHost) {
        for (const [bid, bot] of this.players) {
          if (!bot.isBot) continue;
          this._broadcast({
            type: 'state',
            id: bid,
            x: bot.x, y: bot.y,
            angle: bot.angle,
            hp: bot.hp,
            dead: bot.dead,
            isBot: true,
          });
        }
      }
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // PLAYER FACTORY
  // ─────────────────────────────────────────────────────────────────────────

  function mkPlayer(id, x, y) {
    return { id, x, y, angle: 0, hp: MAX_HP, dead: false };
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
