/* Course Player runtime.
   Reveals gated content, runs knowledge checks, and reports to the LMS through a
   pluggable runtime that auto-detects:
     - SCORM 1.2 / 2004  (window.API / API_1484_11)
     - cmi5 / xAPI       (launched with endpoint+fetch+registration+activityId params)
     - standalone        (no LMS — preview)
   Every adapter exposes the same surface { init()->Promise<{resumed,finished}>, save,
   complete, quit, isFinished } so the course-flow code below is runtime-agnostic.
   Completion fires when every gate is passed, every KC attempted, every required media
   played, every required card opened — or, for a no-interaction lesson, when the end is
   reached. Graded lessons additionally report a score. */
(function () {
  "use strict";

  /* ===================== suspend_data sizing (SCORM 1.2) =====================
     SCORM 1.2 cmi.suspend_data is CMIString4096 — a 4096-character SPM, which
     LMSs commonly enforce in BYTES. JSON.stringify(state).length counts UTF-16
     code units, so a sort-heavy course can blow past 4096 bytes, the LMS
     silently truncates mid-string, and the next launch's JSON.parse throws ->
     ALL progress is lost. So we measure true UTF-8 bytes and degrade through a
     ladder, each rung still VALID JSON, never a truncated blob. */
  var SUSPEND_MAX_1_2 = 4096;
  var SUSPEND_BUDGET  = SUSPEND_MAX_1_2 - 96;   // margin for LMS-side quoting/overhead
  function utf8len(str){ var n=0,c; for (var i=0;i<str.length;i++){ c=str.charCodeAt(i);
    if (c<0x80) n+=1; else if (c<0x800) n+=2; else if (c>=0xD800 && c<=0xDBFF){ n+=4; i++; } else n+=3; } return n; }
  function packSorts(s){ if(!s) return s; var o={}; Object.keys(s).forEach(function(k){ var v=s[k]||{}; o[k]={ok:v.ok?1:0,got:v.got,max:v.max}; }); return o; }   // drop per-item picks, keep partial-credit got/max
  function packKcs(k){ if(!k) return k; var o={}; Object.keys(k).forEach(function(i){ o[i]={ok:(k[i]&&k[i].ok)?1:0}; }); return o; }     // drop chosen option, keep correctness
  // M12 — drop per-item picks/inputs from a partial-credit block's state, keep ok + got/max
  function packSeen(x){ if(!x) return x; var o={}; Object.keys(x).forEach(function(k){ var v=x[k]||{}; o[k]={ok:v.ok?1:0,got:v.got,max:v.max}; }); return o; }
  // simulation (SIM Studio) — a VIEW walkthrough completes when the learner reaches the
  // last frame. Pure + exported so node --test pins the completion boundary. Clamps the
  // reached index into [0, total-1]; a 0-frame sim is trivially done.
  function simProgress(total, reached){ var t=total|0, r=reached|0; if(t<1) return {at:0,done:true};
    if(r<0)r=0; if(r>t-1)r=t-1; return {at:r, done: r>=t-1}; }
  // section pager (opt-in via `*Paged:* on`) — a PAGE is complete (its "Next" button enables)
  // when every required interaction on it is done. Pure + exported so node --test pins the
  // advance-gating without a DOM. `flags` = one boolean per required interaction on the page
  // (true = done); a content-only page (no required interactions) is trivially complete.
  function pageComplete(flags){ for (var i=0;i<flags.length;i++){ if(!flags[i]) return false; } return true; }
  // C5 — question-bank randomization (pure + exported so node --test pins determinism).
  // mulberry32 seeded PRNG: a FRESH draw seeds from Date.now(), but the drawn indices +
  // option orders are what get PERSISTED (not the seed), so resume never re-runs the PRNG.
  function makeRng(seed){ var a = seed >>> 0; return function(){
    a = (a + 0x6D2B79F5) | 0;
    var t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
  // Fisher-Yates permutation of [0..n-1] using rng(); returns the new order.
  function seededShuffle(n, rng){ var a = []; for (var i=0;i<n;i++) a.push(i);
    for (var i=n-1;i>0;i--){ var j = Math.floor(rng()*(i+1)); var t=a[i]; a[i]=a[j]; a[j]=t; } return a; }
  // Draw n of poolSize items: the first n of a seeded shuffle, returned SORTED so the drawn
  // subset keeps authored order (option-shuffle supplies per-question variety). n>=pool → all.
  function drawPool(poolSize, n, rng){ var perm = seededShuffle(poolSize, rng);
    return perm.slice(0, Math.min(n, poolSize)).sort(function(a,b){ return a-b; }); }
  // Pack a bank's per-bank state: KEEP the drawn `pick` (resume MUST show the same questions
  // or the graded set changes) but drop the cosmetic option-shuffle order under byte pressure.
  function packBank(bk){ if(!bk) return bk; var o={}; Object.keys(bk).forEach(function(k){ var v=bk[k]||{}; o[k]={pick:v.pick}; }); return o; }
  // speedStreak — GRADED score: answered N of M correctly (identical shape to the other
  // game blocks). `marks` = [bool] one per answered round. Pure + exported.
  function ssScore(marks){ var got=0; for (var k=0;k<marks.length;k++){ if (marks[k]) got++; }
    return { got: got, max: marks.length, ok: marks.length>0 && got===marks.length }; }
  // whackAMole — FORMATIVE in-game score (never a grade): whacking a target earns a point,
  // whacking a decoy costs one, floored at 0. `moles` = [{target:bool, hit:bool}] (hit = the
  // learner whacked it). Returns {got, max=#targets, ok=(every target hit AND no decoy hit)}.
  // Pure + exported so node --test pins the scoring without a DOM. `ok` only feeds display/
  // resume — whackAMole is completion-only, so it never enters the graded aggregate.
  function wamScore(moles){
    var targets=0, tHit=0, dHit=0;
    for (var i=0;i<(moles||[]).length;i++){ var m=moles[i]||{};
      if (m.target){ targets++; if (m.hit) tHit++; } else if (m.hit) dHit++; }
    var got = tHit - dHit; if (got < 0) got = 0;
    return { got: got, max: targets, ok: targets>0 && tHit===targets && dHit===0 }; }
  // wordScramble - FORMATIVE win check: true iff every placed letter (in slot order) matches
  // the needed letter at that position AND every slot is filled. Pure + exported so
  // node --test pins the match logic without a DOM.
  function scSolved(need, placed){
    if (!need || !placed || need.length === 0 || placed.length !== need.length) return false;
    for (var i=0;i<need.length;i++){ if (placed[i] !== need[i]) return false; }
    return true;
  }
  // memoryMatch — FORMATIVE progress (never a grade): how many pairs the learner has matched.
  // `matched` = count of pairs found, `total` = pairs on the board. Returns {got, max, ok=(all
  // pairs found)}. Pure + exported so node --test pins it without a DOM; `ok`/`got` only feed
  // display + resume — memoryMatch is completion-only, so it never enters the graded aggregate.
  function mmScore(matched, total){ var g=matched|0, t=total|0; if (g<0) g=0; if (g>t) g=t;
    return { got: g, max: t, ok: t>0 && g===t }; }
  // dunkBooth — FORMATIVE arcade reward (replaces the retired Quiz Show, James 2026-07-27).
  // Answer an MCQ to EARN a throw, then release an oscillating timing meter inside the strike
  // zone to dunk the character. Each landed dunk NARROWS the zone (escalating difficulty). No
  // win/lose: completion is engagement (one throw released), the dunk tally is motivational
  // only — dbSeen never enters gradedScore()/xpTotals(). Three pure helpers, exported so node
  // --test pins the mechanic without a DOM.
  //   dunkZone — strike-zone WIDTH (% of the track) after `dunks` landed dunks: starts at
  //     `base` and loses `step` per dunk, floored at `min` so the game stays winnable. `dunks`
  //     clamped at 0.
  function dunkZone(dunks, base, step, min){
    var b=(base==null?40:base), s=(step==null?6:step), m=(min==null?12:min), d=dunks>0?dunks:0;
    var w=b-d*s; return w<m?m:w; }
  //   dunkHit — did a release at `pos` (0..100 along the track) land inside a CENTERED zone of
  //     width `zoneW`? Boundaries inclusive.
  function dunkHit(pos, zoneW){ var start=(100-zoneW)/2; return pos>=start && pos<=start+zoneW; }
  //   dunkProgress — completion-only record: done once at least one throw is released (a miss
  //     still completes — there is no failure state). Mirrors simProgress' {..,done} shape.
  function dunkProgress(throws){ var t=throws>0?throws:0; return { throws:t, done:t>=1 }; }
  // balloonPop — a 2-AXIS carnival board (distinct from dunkBooth's single-axis timing meter).
  // Answer an MCQ to EARN a dart, AIM a column (← →), and HOLD Space to run a VERTICAL power meter
  // that sweeps up/down; release throws the dart at that power. Low power → bottom row, high →
  // top; the released power must land inside that row's target BAND (gutters between = a miss).
  // Band WIDTH is the difficulty (center widest, top narrowest); clearing the board advances a
  // difficulty LEVEL (narrower bands + smaller targets + a bigger board, up to 4×4). No win/lose:
  // completion is engagement (one dart released, hit OR miss), so timing is never essential and the
  // center row is always winnable; the pop tally is motivational only — bpSeen never enters
  // gradedScore()/xpTotals(). Four pure helpers, exported so node --test pins the mechanic without
  // a DOM.
  //   powerAt — the power meter as an ACCELERATING ramp: it starts slow and speeds up (p = 100·u^EXP
  //     over `cycleMs`, u wrapping 0→1 then snapping back). So the low/near part of the bar is easy
  //     to stop on and the high/far part zooms past — the furthest targets are the hardest to catch.
  function powerAt(elapsed, cycleMs){ var c=cycleMs>0?cycleMs:1600, u=(((elapsed%c)+c)%c)/c;
    return 100*Math.pow(u, 2.2); }
  //   balloonLevel — board spec for `round` (boards cleared; 0 = first round) and `diff` (0 Easy /
  //     1 Standard / 2 Hard). The FIRST round is a forgiving 3×3; every ADDITIONAL round steps up to
  //     a 4×4 board (which the engine pairs with a finer aim step per column). `targetScale` +
  //     `hitR` (normalized landing tolerance) tighten with round+diff, floored so it stays winnable.
  //     Both args clamped at 0.
  function balloonLevel(round, diff){
    var rd = round>0?round:0, df = diff>0?diff:0, step = rd + df;
    var cols = rd>=1 ? 4 : 3, rows = cols;          // additional (cleared) rounds = 4×4
    var targetScale = Math.max(0.5, 1 - step*0.08);
    var frac = Math.max(0.24, 0.46 - step*0.03);    // hit radius as a fraction of a cell, floored
    return { round: rd, diff: df, cols: cols, rows: rows, targetScale: targetScale, hitR: frac / Math.max(cols, rows) };
  }
  //   aimLanding — where a throw at `angle` (deg, ± off vertical) and `power` (0..100) lands on the
  //     board, in normalized coords {x:0..1 left→right, y:0..1 bottom→top}. Aim sets X CONTINUOUSLY
  //     (so aim genuinely matters — you can land between columns and miss), power sets the height.
  function aimLanding(angle, power, maxAngle){ var ma=maxAngle>0?maxAngle:42;
    var x=0.5 + (angle/ma)*0.5, y=(power>0?power:0)/100;
    return { x: x<0?0:(x>1?1:x), y: y>1?1:y }; }
  //   hitTest — the un-popped balloon nearest the landing point within `hitR`, or null (a miss).
  //     `targets` = [{r,c,x,y}] normalized centers. Pure + exported so node --test pins it.
  function hitTest(lx, ly, targets, hitR){ var best=null, bd=hitR;
    for (var i=0;i<(targets||[]).length;i++){ var t=targets[i], dx=lx-t.x, dy=ly-t.y, d=Math.sqrt(dx*dx+dy*dy);
      if (d<=bd){ bd=d; best=t; } }
    return best; }
  //   popProgress — completion-only record: done once at least one dart is released (a miss still
  //     completes — there is no failure state). Mirrors dunkProgress' {..,done} shape.
  function popProgress(darts){ var d=darts>0?darts:0; return { darts:d, done:d>=1 }; }
  // shootingGallery — MOVING-TARGET arcade board (the distinct mechanic vs dunkBooth's timing meter
  // and balloonPop's static 2-axis board: here the targets SLIDE, so the skill is LEADING a moving
  // target). Answer an MCQ to EARN a shot, slide the crosshair left/right, and fire at whichever
  // lane's target is under it. A hit clears that lane; clearing every lane advances a difficulty
  // LEVEL (more lanes + faster targets + a tighter hit window). No win/lose: completion is engagement
  // (one shot fired, hit OR miss), so timing is never essential and the game stays winnable; the hit
  // tally is motivational only — sgSeen never enters gradedScore()/xpTotals(). Three pure helpers,
  // exported so node --test pins the mechanic without a DOM.
  //   galleryLevel — level spec for `round` (levels cleared; 0 = first) and `diff` (0 Easy / 1
  //     Standard / 2 Hard). There are always TWO water rows (aim top OR bottom); `perRow` DUCKS ride
  //     each row (more each cleared level, capped 5), and the engine gives every duck its own speed.
  //     The BOTTOM (near) row is easier; the TOP (far) row is a classic shooting-gallery challenge —
  //     faster ducks + a tighter hit window. Base `speed` (normalized row-widths/sec) rises and the
  //     base `hitR` (half-width hit window) tightens with round+diff, each floored so it stays
  //     winnable; difficulty adds speed/tightness, NOT ducks (clearing grows the flock). Both args
  //     clamped at 0. Returns per-row {row, speed, hitR}: row 0 = bottom/near, row 1 = top/far.
  function galleryLevel(round, diff){
    var rd = round>0?round:0, df = diff>0?diff:0, step = rd + df;
    var perRow = Math.min(5, 3 + rd);               // ducks per row; +1 per cleared level, capped 5
    var speed = 0.16 + step*0.04;                   // base normalized row-widths/sec; faster each level
    var hitR = Math.max(0.05, 0.12 - step*0.012);   // base half-width hit window, floored winnable
    return { round: rd, diff: df, perRow: perRow, rows: [
      { row: 0, speed: speed,      hitR: hitR },                       // bottom / near — easier
      { row: 1, speed: speed*1.6,  hitR: Math.max(0.04, hitR*0.65) }   // top / far — faster + tighter
    ]};
  }
  //   galleryHit — the nearest LIVE duck IN THE AIMED ROW under the crosshair `reticleX` within
  //     `hitR`, or null (a miss). `targets` = [{row, idx, x}] live normalized duck centers (0..1);
  //     only ducks whose `row` matches `reticleRow` are eligible, so aiming top vs bottom matters.
  //     Nearest wins. Pure + exported (mirrors balloonPop's hitTest, over a row-scoped crosshair).
  function galleryHit(reticleX, reticleRow, targets, hitR){ var best=null, bd=hitR;
    for (var i=0;i<(targets||[]).length;i++){ var t=targets[i];
      if (t.row !== reticleRow) continue;
      var d=Math.abs(reticleX - t.x);
      if (d<=bd){ bd=d; best=t; } }
    return best; }
  //   shotProgress — completion-only record: done once at least one shot is fired (a miss still
  //     completes — there is no failure state). Mirrors popProgress/dunkProgress' {..,done} shape.
  function shotProgress(shots){ var s=shots>0?shots:0; return { shots:s, done:s>=1 }; }
  // crossword — INPUT / navigation model (Slice D; not scoring). Ported from
  // dwmkerr/crosswords-js (MIT, (c) 2015 Dave Kerr): a current-cell + current-clue
  // (direction) model where letter entry advances ALONG the active clue (right for across,
  // DOWN for down) and Backspace steps behind. Reimplemented dependency-free against our
  // data-cells / data-dir DOM. Pure + exported so node --test pins the movement (the two
  // reported bugs: write-once cells, and across-only advance) without a DOM.
  //   clues: [{ dir:"across"|"down", cells:["r,c", ...] }]  (cells ordered along the direction)
  function buildCwModel(clues){
    var model = {};
    (clues || []).forEach(function(cl){
      (cl.cells || []).forEach(function(rc, idx){
        var m = model[rc] || (model[rc] = {});
        m[cl.dir] = { cells: cl.cells, idx: idx };
      });
    });
    return model;
  }
  // Resolve an action from cell `rc` while heading `dir`. Returns {rc,dir}; never throws and
  // returns the SAME cell (no move) when a move isn't possible. Actions: ahead/behind (along
  // the active clue), toggle (swap across<->down at an intersection), and the four arrows
  // (which also switch the active direction when the cell participates in that axis).
  function cwMove(model, rc, dir, action){
    var cell = model[rc] || {};
    function ahead(d){ var s=cell[d]; return (s && s.idx+1 < s.cells.length) ? { rc:s.cells[s.idx+1], dir:d } : null; }
    function behind(d){ var s=cell[d]; return (s && s.idx-1 >= 0) ? { rc:s.cells[s.idx-1], dir:d } : null; }
    if (action === "toggle") return { rc:rc, dir:(cell.across && cell.down) ? (dir==="across"?"down":"across") : dir };
    if (action === "ahead")  return ahead(dir)  || { rc:rc, dir:dir };
    if (action === "behind") return behind(dir) || { rc:rc, dir:dir };
    if (action === "right")  return ahead("across")  || { rc:rc, dir: cell.across ? "across" : dir };
    if (action === "left")   return behind("across") || { rc:rc, dir: cell.across ? "across" : dir };
    if (action === "down")   return ahead("down")    || { rc:rc, dir: cell.down ? "down" : dir };
    if (action === "up")     return behind("down")   || { rc:rc, dir: cell.down ? "down" : dir };
    return { rc:rc, dir:dir };
  }
  // hangman — FORMATIVE state (never a grade) for a secret word + the letters guessed so far.
  // Only A–Z letters are guessable; other characters (spaces/hyphens) are always shown. `answer`
  // and each `guesses` entry are compared case-insensitively. Returns {wrong (guessed letters not
  // in the answer), revealed (distinct answer letters guessed), needed (distinct answer letters),
  // lost (wrong>=maxWrong), won (every answer letter guessed AND not lost), over (won||lost)}.
  // Pure + exported so node --test pins the win/loss logic without a DOM.
  function hgState(answer, guesses, maxWrong){
    var ans = String(answer||"").toUpperCase();
    var need = {}, i, ch;
    for (i=0;i<ans.length;i++){ ch=ans[i]; if (ch>="A" && ch<="Z") need[ch]=true; }
    var g = {}; guesses = guesses||[];
    for (i=0;i<guesses.length;i++){ var u=String(guesses[i]||"").toUpperCase(); if (u) g[u.charAt(0)]=true; }
    var wrong=0, revealed=0, needed=0, k;
    for (k in need){ if (need.hasOwnProperty(k)){ needed++; if (g[k]) revealed++; } }
    for (k in g){ if (g.hasOwnProperty(k) && !need[k]) wrong++; }
    var max = (maxWrong|0) || 6;
    var lost = wrong >= max;
    var won = needed>0 && revealed===needed && !lost;
    return { wrong: wrong, revealed: revealed, needed: needed, lost: lost, won: won, over: won||lost }; }
  // wheelOfFortune — FORMATIVE state (never a grade) for the hidden puzzle phrase + the letters
  // guessed so far. Only A–Z letters are guessable; other characters (spaces/punctuation) are
  // always shown. Compared case-insensitively. Returns {revealed (distinct puzzle letters guessed),
  // needed (distinct puzzle letters), solved (every distinct letter guessed)}. Pure + exported so
  // node --test pins the solve logic without a DOM. Unlike hangman there is NO loss figure — the
  // game is forgiving (a wrong guess just doesn't reveal); completion is solving OR the bank drying.
  function wofState(puzzle, guessed){
    var ans = String(puzzle||"").toUpperCase();
    var need = {}, i, ch;
    for (i=0;i<ans.length;i++){ ch=ans.charAt(i); if (ch>="A" && ch<="Z") need[ch]=true; }
    var g = {}; guessed = guessed||[];
    for (i=0;i<guessed.length;i++){ var u=String(guessed[i]||"").toUpperCase(); if (u) g[u.charAt(0)]=true; }
    var revealed=0, needed=0, k;
    for (k in need){ if (need.hasOwnProperty(k)){ needed++; if (g[k]) revealed++; } }
    return { revealed: revealed, needed: needed, solved: needed>0 && revealed===needed }; }
  // speedStreak — COSMETIC combo points for ONE answer (never part of the grade). A correct
  // answer scores a base value × a streak-so-far multiplier × an optional speed bonus
  // (fraction of the per-question time still on the clock, 0 when untimed); a wrong answer
  // scores 0 and breaks the streak. Pure + exported so node --test pins the math without a DOM.
  var SS_BASE = 100;
  function ssCombo(correct, streakBefore, timeFrac){
    if (!correct) return 0;
    var mult = 1 + 0.5 * (streakBefore > 0 ? streakBefore : 0);
    var bonus = 1 + (timeFrac > 0 ? timeFrac : 0);
    return Math.round(SS_BASE * mult * bonus);
  }
  // Confetti celebration (gamification #6) — decide whether a `reason` may fire given the
  // course config + whether it already fired. One-shot triggers (pass/complete) fire once;
  // a level-up recurs (each tier crossing is genuine), so it takes no once-guard. Pure +
  // exported so node --test pins the trigger logic (the canvas burst itself is DOM/rAF-only).
  function celebrateAllowed(cfg, reason, fired){
    if (!cfg) return false;
    if (reason === "pass") return !!cfg.pass && !fired;
    if (reason === "complete") return !!cfg.complete && !fired;
    if (reason === "level") return !!cfg.level;
    return false;
  }
  /* ==================== interaction engine (pure core, E1) ====================
     The `interaction` block is a tiny declarative state machine authored as
     content: named elements with visual states, a typed variable store, and an
     ORDERED `when/do/if(/else)` rule list. This is the pure half — condition
     evaluation, action application, and the event-cascade step — exported so
     node --test pins the semantics without a DOM; the DOM wiring below calls
     these same functions. Cascades (a rule's actions firing `change`/`state`
     events that match other rules) are processed breadth-first under a hard
     iteration cap, so a rule cycle degrades to a stopped cascade, never a hang.
     Cross-references were validated at build time (src/interaction.py), so the
     runtime trusts the config. */
  var IX_CASCADE_CAP = 100;
  function ixNum(x){ var n = typeof x === "number" ? x : parseFloat(x); return isNaN(n) ? 0 : n; }
  function ixValue(v, vars){ return (v && typeof v === "object") ? vars[v.var] : v; }   // {var:"x"} = a variable reference
  function ixCondOk(c, vars, states){
    if (c.el !== undefined){ var hit = states[c.el] === c.is; return c.not ? !hit : hit; }
    var a = vars[c.var], b = ixValue(c.value, vars);
    switch (c.op){
      case "==": return a === b || String(a) === String(b);
      case "!=": return !(a === b || String(a) === String(b));
      case ">":  return ixNum(a) >  ixNum(b);
      case ">=": return ixNum(a) >= ixNum(b);
      case "<":  return ixNum(a) <  ixNum(b);
      case "<=": return ixNum(a) <= ixNum(b);
    }
    return false;
  }
  // Mutates `st` ({vars, states, done, got, max}); returns the events the changes emit.
  // Only a REAL change emits (setting a state/variable to its current value is silent),
  // which is what keeps ping-pong rules (toggles) finite in practice.
  function ixApplyActions(acts, st){
    var evts = [];
    (acts || []).forEach(function(a){
      if (a.el !== undefined){
        if (st.states[a.el] !== a.state){ st.states[a.el] = a.state; evts.push({ event:"state", target:a.el }); }
      } else if (a.var !== undefined){
        var cur = st.vars[a.var], val = ixValue(a.value, st.vars), nv = cur;
        if (a.op === "set") nv = val;
        else if (a.op === "add") nv = ixNum(cur) + ixNum(val);
        else if (a.op === "sub") nv = ixNum(cur) - ixNum(val);
        else if (a.op === "toggle") nv = !cur;
        if (nv !== cur){ st.vars[a.var] = nv; evts.push({ event:"change", target:a.var }); }
      } else if (a.done){
        st.done = true;
        if (a.got !== undefined) st.got = ixNum(ixValue(a.got, st.vars));
        if (a.max !== undefined) st.max = ixNum(a.max);
      }
    });
    return evts;
  }
  // Feed one event through the ordered rule list, cascading emitted events until quiet
  // (or the cap). Rule order is semantics: same-event rules run top to bottom.
  function ixStep(cfg, st, ev){
    var queue = [ev], guard = 0;
    while (queue.length){
      if (++guard > IX_CASCADE_CAP) break;
      var e = queue.shift();
      (cfg.rules || []).forEach(function(r){
        var w = r.when || {};
        if (w.event !== e.event) return;
        if (w.target !== undefined && w.target !== e.target) return;
        var hit = (r["if"] || []).every(function(c){ return ixCondOk(c, st.vars, st.states); });
        ixApplyActions(hit ? r["do"] : r["else"], st).forEach(function(x){ queue.push(x); });
      });
    }
    return st;
  }
  function ixInitState(cfg){
    var vars = {}, states = {};
    (cfg.variables || []).forEach(function(v){ vars[v.name] = v.init; });
    (cfg.elements || []).forEach(function(el){ states[el.id] = el.initial || (el.states && el.states[0]) || "normal"; });
    return { vars: vars, states: states, done: false, got: null, max: null };
  }

  // Return the largest representation of `state` that fits the 1.2 byte budget.
  function fitSuspend(state){
    var rungs = [
      state,                                                                              // full (incl. loc)
      { g:state.g, k:state.k, m:state.m, o:state.o, s:state.s, mt:state.mt, sq:state.sq, fl:state.fl, dd:state.dd, ht:state.ht, ws:state.ws, cw:state.cw, gs:state.gs, qb:state.qb, ss:state.ss, wm:state.wm, mm:state.mm, hg:state.hg, wof:state.wof, sm:state.sm, db:state.db, bp:state.bp, sg:state.sg, pl:state.pl, rf:state.rf, sc:state.sc, sh:state.sh, ix:state.ix, b:state.b },             // drop cosmetic resume pointer
      { g:state.g, k:state.k, m:state.m, o:state.o, s:packSorts(state.s), mt:packSeen(state.mt), sq:packSeen(state.sq), fl:packSeen(state.fl), dd:packSeen(state.dd), ht:packSeen(state.ht), ws:packSeen(state.ws), cw:packSeen(state.cw), gs:packSeen(state.gs), qb:packSeen(state.qb), ss:packSeen(state.ss), wm:packSeen(state.wm), mm:packSeen(state.mm), hg:packSeen(state.hg), wof:packSeen(state.wof), sm:packSeen(state.sm), db:packSeen(state.db), bp:packSeen(state.bp), sg:packSeen(state.sg), pl:state.pl, rf:packSeen(state.rf), sc:packSeen(state.sc), sh:packSeen(state.sh), ix:packSeen(state.ix), b:packBank(state.b) },               // drop sort/match/seq/fill/drag/hotspot/wordsearch/crossword/gameshow/quizboard/speedstreak picks + whack-a-mole hit detail + memory-match/hangman/wheel-of-fortune/dunk-booth/balloon-pop/shooting-gallery detail + interaction var/state detail + bank option order
      { g:state.g, k:packKcs(state.k), m:state.m, o:state.o, s:packSorts(state.s), mt:packSeen(state.mt), sq:packSeen(state.sq), fl:packSeen(state.fl), dd:packSeen(state.dd), ht:packSeen(state.ht), ws:packSeen(state.ws), cw:packSeen(state.cw), gs:packSeen(state.gs), qb:packSeen(state.qb), ss:packSeen(state.ss), wm:packSeen(state.wm), mm:packSeen(state.mm), hg:packSeen(state.hg), wof:packSeen(state.wof), sm:packSeen(state.sm), db:packSeen(state.db), bp:packSeen(state.bp), sg:packSeen(state.sg), pl:state.pl, rf:packSeen(state.rf), sc:packSeen(state.sc), sh:packSeen(state.sh), ix:packSeen(state.ix), b:packBank(state.b) }        // drop KC option detail (bank `pick` still kept — resume needs it)
    ];
    var last = "";
    for (var i=0;i<rungs.length;i++){ last = JSON.stringify(rungs[i]); if (utf8len(last) <= SUSPEND_BUDGET) return last; }
    return last;   // smallest rung; still valid JSON even if a pathological course exceeds the budget
  }

  /* ============================ KC scoring (pure) ============================
     Extracted so the multi-select/retry/grading decisions are unit-testable in
     node without a DOM (tests/test_player.js) — the browser handlers below call
     these too, so a test guards the live logic, not a copy. */
  // multi-select is correct iff EVERY option's correctness matches whether it was
  // selected (all the right ones, none of the wrong ones). `corrects[oi]` = true if
  // option oi is a correct answer; `sel` = the list of selected option indexes.
  function multiAllCorrect(corrects, sel){
    return corrects.every(function(c,oi){ return c === (sel.indexOf(oi) >= 0); });
  }
  // hotspot — click every correct region and no wrong ones. `corrects[i]` = spot i is a
  // target; `sel` = the list of clicked spot indexes. PARTIAL credit over the target set:
  // got = (targets clicked) − (wrong spots clicked), floored at 0; max = number of targets;
  // ok only when every target is clicked and nothing wrong is. Pure + exported so node
  // --test pins the scoring without a DOM (mirrors tallyExact/multiAllCorrect).
  function scoreHotspot(corrects, sel){
    var selSet = {}; (sel||[]).forEach(function(x){ selSet[x] = 1; });
    var max = 0, hit = 0, wrong = 0;
    corrects.forEach(function(c,i){
      if (c){ max++; if (selSet[i]) hit++; }
      else if (selSet[i]) wrong++;
    });
    return { got: Math.max(0, hit - wrong), max: max, ok: hit === max && wrong === 0 };
  }
  // a KC answer is terminal (locks) when it's correct, the course is one-shot
  // (maxTries falsy), or the learner has used their last attempt; else it retries.
  function kcLocks(ok, tries, maxTries){ return ok || !maxTries || tries >= maxTries; }
  // graded score as a 0..100 integer percent (0 when there are no KCs).
  function scorePct(correct, total){ return total ? Math.round(correct/total*100) : 0; }
  // parse a packed multi-select rung's `opt` ("0,2") back to option indexes [0,2].
  // A degraded/packed rung (no opt) yields [] — the rung resumes as a bare correct.
  function parseMultiSel(optStr){
    return String(optStr).split(",").filter(function(x){ return x !== ""; }).map(Number);
  }
  // Branching scenario routing (M14): resolve a choice's `data-goto` value to a scene
  // index within `sceneIds`. Returns -1 when the target is empty or unknown — the
  // caller treats that as a terminal/ending choice (no onward scene). Pure + exported
  // so `node --test` can pin the routing without a DOM.
  function resolveScene(gotoVal, sceneIds){
    if (!gotoVal) return -1;
    return (sceneIds || []).indexOf(gotoVal);
  }
  // M13 — aggregate a graded course's KC outcomes into an OVERALL score plus per-section
  // (objective) SUBSCORES. Pure + exported so node tests pin the scoring/gating math
  // without a DOM (the live gradedScore() below feeds it the DOM-derived items).
  //   items:      [{obj:<string|null>, ok:<bool>, got?:<num>, max?:<num>}]  one per graded block
  //   passMark:   overall pass threshold (0..100)
  //   objectives: [{id,name,pass}]  graded sections (pass may be null = report, no gate)
  // When objectives is non-empty, ONLY items carrying an obj are summative (counted) — inline
  // ones are formative; with NO objectives every item counts (pre-M13 graded courses unchanged).
  // An item may carry PARTIAL credit: got/max points (M12 matching/sequencing/fill-in-the-blank);
  // a boolean KC is 1/1. Overall passes iff raw >= passMark AND every threshold'd objective is met.
  function aggregateScore(items, passMark, objectives){
    objectives = objectives || []; items = items || [];
    var hasObj = objectives.length > 0;
    var per = {};
    objectives.forEach(function(o){ per[o.id] = { c:0, t:0 }; });
    var oc = 0, ot = 0;
    items.forEach(function(it){
      var summative = hasObj ? !!it.obj : true;
      if (!summative) return;
      // M12 — fractional partial credit {got,max} when present; a boolean KC is got/max = ok/1.
      var mx = (it.max != null) ? it.max : 1, gt = (it.got != null) ? it.got : (it.ok ? 1 : 0);
      ot += mx; oc += gt;
      if (it.obj && per[it.obj]) { per[it.obj].t += mx; per[it.obj].c += gt; }
    });
    var raw = scorePct(oc, ot);
    var objs = objectives.map(function(o){
      var pb = per[o.id] || { c:0, t:0 };
      var r = scorePct(pb.c, pb.t);
      var pass = (o.pass === null || o.pass === undefined) ? null : o.pass;
      return { id:o.id, name:o.name, raw:r, min:0, max:100, scaled:(r/100).toFixed(2),
               pass:pass, passed:(pass === null || r >= pass) };
    });
    var allObjPass = objs.every(function(o){ return o.passed; });
    return { raw:raw, min:0, max:100, scaled:(raw/100).toFixed(2),
             passed:(raw >= passMark && allObjPass), objectives:objs };
  }
  /* ===================== review-what-you-missed (formative recap) ================
     From per-block records the DOM layer scrapes at completion, keep only the ones
     the learner ATTEMPTED but did not get fully right (`ok` already means "fully
     correct" for every block type — a boolean KC is ok/!ok, a partial block is
     got===max). Order is preserved (the DOM layer passes records in document order).
     Rows with neither a question nor an answer are dropped; an entry left with no
     rows (e.g. a declarative interaction that carries no clean answer) keeps a single
     revisit row so the recap still names it. Pure + exported so node --test pins the
     filter/shape without a DOM. */
  function reviewEntries(records){
    var out = [];
    (records || []).forEach(function(r){
      if (!r || !r.attempted || r.ok) return;
      var rows = (r.rows || []).filter(function(x){ return x && (x.q || x.a); });
      if (!rows.length) rows = [{ q: "", a: "" }];   // name it even with no answer to show
      out.push({ head: r.head || "", rows: rows });
    });
    return out;
  }
  /* ===================== points/XP overlay (gamification #3) =====================
     A PURELY MOTIVATIONAL layer: it never touches the graded score, the completion
     gate, or the LMS score — it re-derives an XP total + a level TIER from the SAME
     block-state the player already persists in suspend_data (so it survives resume
     for free, no extra state key). Each scorable block earns points weighted by a
     category (check / question / game); partial-credit blocks award pro-rata. Pure +
     exported so node --test pins the math without a DOM. */
  var XP_DEFAULT_W = { check: 10, question: 15, game: 20 };
  var XP_DEFAULT_TIERS = [["Novice", 0.0], ["Proficient", 0.5], ["Skilled", 0.8], ["Expert", 1.0]];
  // Map a block KIND to its XP weight category. KCs + categorize = a "check"; the M12
  // question types = "question"; the word games = "game" (harder → worth more).
  function xpCat(kind){
    if (kind === "kc" || kind === "sort") return "check";
    if (kind === "ws" || kind === "cw" || kind === "gs" || kind === "qb" || kind === "ss") return "game";
    return "question";   // mt, sq, fl, dd, ht
  }
  function xpWeight(kind, weights){ weights = weights || XP_DEFAULT_W; return weights[xpCat(kind)] || 0; }
  // Points earned for ONE resolved block. Partial-credit blocks carry {got,max} →
  // pro-rata; a boolean block ({ok}) is all-or-nothing. A missing result earns 0.
  function xpForResult(kind, res, weights){
    if (!res) return 0;
    var w = xpWeight(kind, weights);
    if (typeof res.got === "number" && typeof res.max === "number" && res.max > 0)
      return Math.round(w * res.got / res.max);
    return res.ok ? w : 0;
  }
  // Sum earned + total-earnable XP across the scorable blocks. `specs` = one entry per
  // block kind: {kind, seen:<the *Seen map>, count:<node count>}. Earnable = weight ×
  // count; earned = the resolved results. Pure + exported.
  function xpTotals(specs, weights){
    specs = specs || []; var earned = 0, possible = 0;
    specs.forEach(function(sp){
      var w = xpWeight(sp.kind, weights);
      possible += w * (sp.count || 0);
      var sm = sp.seen || {};
      Object.keys(sm).forEach(function(k){ earned += xpForResult(sp.kind, sm[k], weights); });
    });
    return { earned: earned, possible: possible };
  }
  // Resolve a completion FRACTION (earned/earnable, 0..1) to a level tier. Returns the
  // highest tier whose threshold the fraction has reached. Pure + exported.
  function tierFor(frac, tiers){
    tiers = (tiers && tiers.length) ? tiers : XP_DEFAULT_TIERS;
    var name = tiers[0][0], index = 0;
    for (var i = 0; i < tiers.length; i++){ if (frac + 1e-9 >= tiers[i][1]){ name = tiers[i][0]; index = i; } }
    return { name: name, index: index };
  }
  // M12 — score an ordered set of picks against their correct answers, elementwise.
  // A blank/null pick is always wrong. Returns PARTIAL credit {got, max, ok}. Pure +
  // exported for node tests; matching and sequencing both use it.
  function tallyExact(picks, answers){
    picks = picks || []; answers = answers || [];
    var max = answers.length, got = 0;
    for (var k=0;k<max;k++){ if (picks[k] != null && picks[k] !== "" && picks[k] === answers[k]) got++; }
    return { got: got, max: max, ok: max > 0 && got === max };
  }
  // M12 fill-in-the-blank — LENIENT normalization: trim, collapse inner whitespace, lowercase.
  function normFill(s){ return String(s == null ? "" : s).trim().replace(/\s+/g, " ").toLowerCase(); }
  // Score text-entry blanks against a per-blank accept-list. A blank input is wrong; a
  // non-empty input is right iff its normalized form is in the normalized accept-list.
  // PARTIAL credit {got, max, ok}. Pure + exported.
  function fillScore(inputs, answerSets){
    inputs = inputs || []; answerSets = answerSets || [];
    var max = answerSets.length, got = 0;
    for (var k=0;k<max;k++){
      var got_in = normFill(inputs[k]);
      if (got_in === "") continue;
      var accept = (answerSets[k] || []).map(normFill);
      if (accept.indexOf(got_in) >= 0) got++;
    }
    return { got: got, max: max, ok: max > 0 && got === max };
  }

  var HAS_DOM = typeof window !== "undefined" && typeof document !== "undefined";

  /* ============================ SCORM 1.2 / 2004 adapter ============================ */
  function makeScorm() {
    var api = null, ver = null, started = 0, finished = false, terminated = false, lastState = null;
    function find(win) {
      var n = 0;
      while (win && n++ < 12) {
        if (win.API_1484_11) { ver = "2004"; return win.API_1484_11; }
        if (win.API)        { ver = "1.2";  return win.API; }
        if (win.parent && win.parent !== win) { win = win.parent; continue; }
        break;
      }
      return null;
    }
    function locate() { api = find(window); if (!api && window.opener) api = find(window.opener); return api; }
    var K = {
      status:  function(){ return ver==="2004" ? "cmi.completion_status" : "cmi.core.lesson_status"; },
      suspend: function(){ return "cmi.suspend_data"; },
      exit:    function(){ return ver==="2004" ? "cmi.exit" : "cmi.core.exit"; },
      time:    function(){ return ver==="2004" ? "cmi.session_time" : "cmi.core.session_time"; },
      sRaw:    function(){ return ver==="2004" ? "cmi.score.raw" : "cmi.core.score.raw"; },
      sMin:    function(){ return ver==="2004" ? "cmi.score.min" : "cmi.core.score.min"; },
      sMax:    function(){ return ver==="2004" ? "cmi.score.max" : "cmi.core.score.max"; },
      name:    function(){ return ver==="2004" ? "cmi.learner_name" : "cmi.core.student_name"; }
    };
    function lastErr(){ try { return ver==="2004" ? api.GetLastError() : api.LMSGetLastError(); } catch(e){ return "?"; } }
    function get(k){ try { return (ver==="2004" ? api.GetValue(k) : api.LMSGetValue(k)) || ""; } catch(e){ return ""; } }
    function set(k,v){ try { var ok = ver==="2004" ? api.SetValue(k,String(v)) : api.LMSSetValue(k,String(v));
      var e = lastErr(); if (e && e!=="0") console.warn("[player] SetValue rejected", k, "=", v, "err", e); return ok;
    } catch(e){ console.warn("[player] SetValue threw", k, e); return false; } }
    function commit(){ try { ver==="2004" ? api.Commit("") : api.LMSCommit(""); } catch(e){} }
    function fmtTime(ms){ var s=Math.max(0,Math.round(ms/1000)), h=Math.floor(s/3600), m=Math.floor((s%3600)/60), sec=s%60;
      if (ver==="2004") return "PT"+(h?h+"H":"")+(m?m+"M":"")+sec+"S";
      function p(n){return (n<10?"0":"")+n;} return p(h)+":"+p(m)+":"+p(sec)+".00"; }

    return {
      kind: function(){ return ver ? "scorm "+ver : "scorm"; },
      init: function () {
        if (!locate()) { console.info("[player] no SCORM LMS"); return Promise.resolve(null); }
        started = Date.now();
        try { ver==="2004" ? api.Initialize("") : api.LMSInitialize(""); } catch(e){ console.warn("[player] init", e); }
        var st = get(K.status()).toLowerCase();
        finished = (st==="completed" || st==="passed");
        if (!finished && st!=="incomplete") set(K.status(), "incomplete");
        commit();
        var resumed = null; try { resumed = JSON.parse(get(K.suspend())||"null"); } catch(e){}
        return Promise.resolve({ resumed: resumed, finished: finished });
      },
      isFinished: function(){ return finished; },
      learnerName: function(){ return get(K.name()); },      // C8 — read-only LMS-supplied name
      save: function (state) {
        lastState = state;
        // 2004 suspend_data SPM is 64000 — large enough to keep full state; 1.2 must fit ~4096 bytes.
        var s = ver==="2004" ? JSON.stringify(state) : fitSuspend(state);
        set(K.suspend(), s); commit();
      },
      complete: function (score) {
        if (score) { set(K.sRaw(),score.raw); set(K.sMin(),score.min); set(K.sMax(),score.max);
          if (ver==="2004") set("cmi.score.scaled",score.scaled);
          if (ver==="2004"){ set("cmi.completion_status","completed"); set("cmi.success_status", score.passed?"passed":"failed"); }
          else set("cmi.core.lesson_status", score.passed?"passed":"failed");
          // M13 — per-section subscores as SCORM objectives (2004: scaled + success_status; 1.2: raw + status)
          var objs = score.objectives || [];
          for (var oi=0; oi<objs.length; oi++){ var o=objs[oi], op="cmi.objectives."+oi+".";
            set(op+"id", o.id); set(op+"score.raw", o.raw); set(op+"score.min", o.min); set(op+"score.max", o.max);
            if (ver==="2004"){ set(op+"score.scaled", o.scaled); set(op+"success_status", o.passed?"passed":"failed"); set(op+"completion_status","completed"); }
            else set(op+"status", o.passed?"passed":"failed"); }
        } else { if (ver==="2004"){ set("cmi.completion_status","completed"); set("cmi.success_status","passed"); }
          else set("cmi.core.lesson_status","completed"); }
        finished = true; commit();
      },
      interaction: function (n, id, learner, correct) {
        var p = "cmi.interactions."+n+".";
        set(p+"id", id||("kc"+n)); set(p+"type","choice");
        if (ver==="2004"){ set(p+"learner_response",learner); set(p+"result",correct?"correct":"incorrect"); }
        else { set(p+"student_response",learner); set(p+"result",correct?"correct":"wrong"); }
      },
      quit: function () {
        if (!api || terminated) return; terminated = true;
        try { set(K.time(), fmtTime(Date.now()-started));
          set(K.exit(), finished ? (ver==="2004"?"normal":"") : "suspend"); commit();
          ver==="2004" ? api.Terminate("") : api.LMSFinish(""); } catch(e){ console.warn("[player] quit", e); }
      }
    };
  }

  /* ============================ cmi5 / xAPI adapter ============================ */
  var CMI5 = {
    CAT:   "https://w3id.org/xapi/cmi5/context/categories/cmi5",
    MOVEON:"https://w3id.org/xapi/cmi5/context/categories/moveon",
    SID:   "https://w3id.org/xapi/cmi5/context/extensions/sessionid",
    V: { init:"http://adlnet.gov/expapi/verbs/initialized", completed:"http://adlnet.gov/expapi/verbs/completed",
         passed:"http://adlnet.gov/expapi/verbs/passed", failed:"http://adlnet.gov/expapi/verbs/failed",
         terminated:"http://adlnet.gov/expapi/verbs/terminated" },
    EXT_SUBSCORES:"https://course-builder.local/xapi/extensions/subscores"  // M13 per-section subscores
  };
  function cmi5Params() {
    var q = {}; (location.search.replace(/^\?/,"").split("&")).forEach(function(p){
      if (!p) return; var i = p.indexOf("="); var k = decodeURIComponent(p.slice(0,i)); var v = decodeURIComponent(p.slice(i+1)); q[k]=v; });
    if (q.endpoint && q.fetch && q.registration && q.activityId) return q;
    return null;
  }
  function makeCmi5(q) {
    var endpoint = q.endpoint.replace(/\/?$/,"/"), fetchUrl = q.fetch, reg = q.registration, activityId = q.activityId;
    var actor; try { actor = JSON.parse(q.actor); } catch(e){ actor = { account:{ name:q.actor||"learner" } }; }
    var token = "", ctxT = {}, mode = "Normal", mastery = null, returnURL = null;
    var sid = (window.crypto && crypto.randomUUID) ? crypto.randomUUID() : (Date.now()+"-"+Math.random().toString(16).slice(2));
    var started = 0, finished = false, terminated = false, completedSent = false, lastState = null;

    function isoDur(ms){ var s=Math.max(0,Math.round(ms/1000)),h=Math.floor(s/3600),m=Math.floor((s%3600)/60),sec=s%60;
      return "PT"+(h?h+"H":"")+(m?m+"M":"")+sec+"S"; }
    // xAPI Alternate (CORS) Request Syntax: cmi5 content is cross-origin to the LRS, and a
    // normal POST with Authorization/X-Experience-API-Version headers triggers a CORS preflight
    // most LRS endpoints reject — so every call is a form-encoded POST with ?method=<VERB>,
    // and headers/query-params/body ride as form fields. keepalive lets it survive unload.
    function form(p){ var o=[]; Object.keys(p).forEach(function(k){ if (p[k]!=null) o.push(encodeURIComponent(k)+"="+encodeURIComponent(p[k])); }); return o.join("&"); }
    function lrs(method, path, params, content){
      if (!token) return Promise.resolve();   // no valid auth — don't fire malformed (Basic ) requests
      var f = {}; if (params) Object.keys(params).forEach(function(k){ f[k]=params[k]; });
      f.Authorization = token; f["X-Experience-API-Version"] = "1.0.3";
      if (content != null) { f["Content-Type"] = "application/json"; f.content = JSON.stringify(content); }
      return fetch(endpoint + path + "?method=" + method, { method:"POST",
        headers:{ "Content-Type":"application/x-www-form-urlencoded" }, body: form(f), keepalive:true })
        .catch(function(e){ console.warn("[player] LRS " + method + " " + path, e); });
    }
    function stateParams(id){ return { stateId:id, activityId:activityId, agent:JSON.stringify(actor), registration:reg }; }
    function ctx(moveon){ var c = JSON.parse(JSON.stringify(ctxT||{})); c.registration = reg;
      c.contextActivities = c.contextActivities || {};
      var cats = (c.contextActivities.category||[]).slice(); cats.push({id:CMI5.CAT}); if (moveon) cats.push({id:CMI5.MOVEON});
      c.contextActivities.category = cats; c.extensions = c.extensions || {}; c.extensions[CMI5.SID] = sid; return c; }
    function stmt(verb, disp, result, moveon){ var s = { actor:actor, verb:{id:verb, display:{"en-US":disp}},
      object:{ id:activityId, objectType:"Activity" }, context:ctx(moveon), timestamp:new Date().toISOString() };
      if (result) s.result = result; return s; }
    function sendStmt(s){ return lrs("POST", "statements", null, s); }

    return {
      kind: function(){ return "cmi5"; },
      init: function () {
        started = Date.now();
        return fetch(fetchUrl, { method:"POST" }).then(function(r){ return r.json(); }).then(function(j){
          var t = j && (j["auth-token"] || j.token);
          if (!t) {   // single-use token already spent (relaunch of a stale session) or an error response
            console.error("[player] cmi5 fetch returned no auth-token — relaunch with a FRESH registration. Response:", j);
            throw new Error("cmi5: no auth-token");
          }
          token = /^(Basic|Bearer)\s/i.test(t) ? t : ("Basic "+t);          // SCORM Cloud & most LRS: "Basic <token>"
          return lrs("GET", "activities/state", stateParams("LMS.LaunchData"));
        }).then(function(r){ return r && r.ok ? r.json() : {}; }).then(function(ld){
          ctxT = ld.contextTemplate || {}; mode = ld.launchMode || "Normal";
          mastery = (typeof ld.masteryScore==="number") ? ld.masteryScore : null; returnURL = ld.returnURL || null;
          return lrs("GET", "activities/state", stateParams("course.progress"));
        }).then(function(r){ return r && r.ok ? r.json().catch(function(){return null;}) : null; }).then(function(prog){
          finished = !!(prog && prog.done); lastState = prog && prog.state || null;
          return sendStmt(stmt(CMI5.V.init, "initialized")).then(function(){ return { resumed:lastState, finished:finished, mastery:mastery }; });
        }).catch(function(e){ console.warn("[player] cmi5 init failed", e); return { resumed:null, finished:false }; });
      },
      isFinished: function(){ return finished; },
      returnURL: function(){ return returnURL; },
      learnerName: function(){                                // C8 — best-effort from the xAPI actor
        if (!actor) return "";
        if (actor.name) return actor.name;
        if (actor.account && actor.account.name) return actor.account.name;
        return "";
      },
      save: function (state) { lastState = state;
        lrs("PUT", "activities/state", stateParams("course.progress"), { state:state, done:finished }); },
      complete: function (score) {
        if (mode !== "Normal" || completedSent) return; completedSent = true; finished = true;
        var dur = isoDur(Date.now()-started);
        sendStmt(stmt(CMI5.V.completed, "completed", { completion:true, duration:dur }, true));
        if (score) { var sc = { scaled:Number(score.scaled), raw:score.raw, min:score.min, max:score.max };
          var res = { success:!!score.passed, score:sc, duration:dur };
          // M13 — per-section subscores ride as a result extension (cmi5 has no cmi.objectives)
          var objs = score.objectives || [];
          if (objs.length){ var ext = {};
            for (var oi=0; oi<objs.length; oi++){ var o=objs[oi];
              ext[o.id] = { name:o.name, scaled:Number(o.scaled), raw:o.raw, min:o.min, max:o.max, passed:!!o.passed }; }
            res.extensions = {}; res.extensions[CMI5.EXT_SUBSCORES] = ext; }
          sendStmt(stmt(score.passed?CMI5.V.passed:CMI5.V.failed, score.passed?"passed":"failed", res, true)); }
        lrs("PUT", "activities/state", stateParams("course.progress"), { state:lastState, done:true });
      },
      interaction: function(){ /* cmi5 captures KC outcomes in the score/statements; per-item xAPI optional */ },
      quit: function () { if (terminated) return; terminated = true;
        sendStmt(stmt(CMI5.V.terminated, "terminated", { duration:isoDur(Date.now()-started) })); }
    };
  }

  /* ============================ runtime selection ============================ */
  function makeRuntime() {
    var scorm = makeScorm();
    return scorm.init().then(function (s) {
      if (s) return { rt: scorm, info: s };                 // a SCORM LMS answered
      var q = cmi5Params();
      if (q) { var c = makeCmi5(q); return c.init().then(function (i) { return { rt:c, info:i }; }); }
      return { rt: null, info: { resumed:null, finished:false } };   // standalone
    });
  }

  /* ============================ Course flow ============================ */
  function ready(fn){ document.readyState!=="loading" ? fn() : document.addEventListener("DOMContentLoaded", fn); }

  /* ---- Phase-1 dynamism: reveal visual blocks as they enter the viewport ----
   * Progressive enhancement, OPT-IN: the hidden initial state applies only under the
   * .nv-anim root class, which we add ONLY when motion is allowed AND IntersectionObserver
   * exists — so no-JS / reduced-motion / any failure always renders fully visible. The
   * multi-item blocks (process steps, timeline milestones, comparison panels, cards)
   * stagger their children in sequence for a motion-graphics feel; prose stays put.
   * Gated blocks are left to the existing continue-gate fade so the two never fight. */
  var REVEAL_SEQ = ".nv-process,.nv-timeline,.nv-comparison,.nv-cardgrid,.nv-flashgrid";
  var REVEAL_BLOCK = ".nv-infographic";
  function revealDelay(i){ return Math.min(i, 10) * 70; }   // per-child stagger (ms), capped

  function setupReveal(){
    if (typeof document === "undefined" || typeof IntersectionObserver === "undefined") return;
    if (window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches) return;
    function ungated(el){ return !el.closest || !el.closest(".nv-gated"); }
    var seqEls = Array.prototype.slice.call(document.querySelectorAll(REVEAL_SEQ)).filter(ungated);
    var blockEls = Array.prototype.slice.call(document.querySelectorAll(REVEAL_BLOCK)).filter(ungated);
    if (!seqEls.length && !blockEls.length) return;
    try {
      document.documentElement.classList.add("nv-anim");            // enables the hidden->reveal CSS
      seqEls.forEach(function(el){ el.classList.add("nv-reveal", "nv-reveal-seq"); });
      blockEls.forEach(function(el){ el.classList.add("nv-reveal"); });
      var io = new IntersectionObserver(function(entries){
        entries.forEach(function(e){
          if (!e.isIntersecting) return;
          var el = e.target;
          if (el.classList.contains("nv-reveal-seq")){
            Array.prototype.slice.call(el.children).forEach(function(c, k){
              setTimeout(function(){ c.classList.add("nv-in"); }, revealDelay(k));
            });
          }
          el.classList.add("nv-in");
          io.unobserve(el);
        });
      }, { threshold: 0.12, rootMargin: "0px 0px -6% 0px" });
      seqEls.concat(blockEls).forEach(function(el){ io.observe(el); });
    } catch (err) {
      document.documentElement.classList.remove("nv-anim");         // any failure -> reveal everything
    }
  }
  if (HAS_DOM) ready(setupReveal);

  if (HAS_DOM) ready(function () {
    makeRuntime().then(function (sel) {
      var RT = sel.rt, resumed = sel.info && sel.info.resumed;

      // C5 — question-bank pre-pass. BEFORE the collectors below, draw N of each bank's pool
      // and REMOVE the undrawn children, so every existing selector/counter/gradedScore sees
      // exactly the drawn subset with NO further changes. Also shuffle each drawn KC's option
      // order. On resume, reuse the persisted draw + option order (resume-stable); a fresh
      // launch draws anew. (Re-draw on the in-session Retry button is a planned follow-up.)
      var banks = Array.prototype.slice.call(document.querySelectorAll("[data-bank]"));
      var bankState = {};
      if (banks.length) {
        var savedBanks = (resumed && resumed.b) || {};
        banks.forEach(function (bank, bi) {
          var kids = Array.prototype.slice.call(bank.children);
          var draw = parseInt(bank.getAttribute("data-draw") || String(kids.length), 10);
          var saved = savedBanks[bi];
          var pick = (saved && saved.pick) ? saved.pick
            : drawPool(kids.length, draw, makeRng((Date.now() ^ (bi * 0x9E3779B1)) >>> 0));
          var optOrders = (saved && saved.opt) || {};
          var keep = {}; pick.forEach(function (k) { keep[k] = true; });
          kids.forEach(function (node, k) {
            if (!keep[k]) { bank.removeChild(node); return; }
            var opts = Array.prototype.slice.call(node.querySelectorAll(".nv-kc-opt"));
            if (opts.length) {
              var order = optOrders[k] || seededShuffle(opts.length, makeRng((Date.now() ^ (bi * 131 + k * 977)) >>> 0));
              optOrders[k] = order;
              var anchor = opts[opts.length - 1].nextSibling;   // submit/feedback node after the options
              order.forEach(function (oi) { node.insertBefore(opts[oi], anchor); });
            }
          });
          bankState[bi] = { pick: pick, opt: optOrders };
        });
      }

      var gates = Array.prototype.slice.call(document.querySelectorAll(".nv-continue"));
      var kcs   = Array.prototype.slice.call(document.querySelectorAll(".nv-kc"));
      var media = Array.prototype.slice.call(document.querySelectorAll("[data-require='1']"));
      var reqOpens = Array.prototype.slice.call(document.querySelectorAll('[data-require-open="1"]'));
      var sorts = Array.prototype.slice.call(document.querySelectorAll("[data-sort]"));
      var matches = Array.prototype.slice.call(document.querySelectorAll("[data-match]"));  // M12
      var sequences = Array.prototype.slice.call(document.querySelectorAll("[data-seq]"));  // M12
      var fills = Array.prototype.slice.call(document.querySelectorAll("[data-fill]"));  // M12
      var drags = Array.prototype.slice.call(document.querySelectorAll("[data-drag]"));  // dragDrop
      var hotspots = Array.prototype.slice.call(document.querySelectorAll("[data-hotspot]"));  // hotspot (click-image)
      var wordsearches = Array.prototype.slice.call(document.querySelectorAll("[data-wordsearch]"));  // wordSearch
      var crosswords = Array.prototype.slice.call(document.querySelectorAll("[data-crossword]"));  // crossword
      var gameshows = Array.prototype.slice.call(document.querySelectorAll("[data-gameshow]"));  // gameShow
      var quizboards = Array.prototype.slice.call(document.querySelectorAll("[data-quizboard]"));  // quizBoard (Jeopardy)
      var speedstreaks = Array.prototype.slice.call(document.querySelectorAll("[data-speedstreak]"));  // speedStreak (fast run)
      var whackamoles = Array.prototype.slice.call(document.querySelectorAll("[data-whackamole]"));  // whackAMole (formative, completion-only)
      var memorymatches = Array.prototype.slice.call(document.querySelectorAll("[data-memorymatch]"));  // memoryMatch (formative, completion-only)
      var hangmen = Array.prototype.slice.call(document.querySelectorAll("[data-hangman]"));  // hangman (formative, completion-only)
      var wheels = Array.prototype.slice.call(document.querySelectorAll("[data-wheeloffortune]"));  // wheelOfFortune (formative, completion-only)
      var interactions = Array.prototype.slice.call(document.querySelectorAll("[data-interaction]"));  // E1 declarative interaction engine
      var sims = Array.prototype.slice.call(document.querySelectorAll("[data-sim]"));  // simulation (SIM Studio; formative VIEW, completion-only)
      var dunkbooths = Array.prototype.slice.call(document.querySelectorAll("[data-dunkbooth]"));  // dunkBooth (arcade reward; formative, completion-only)
      var balloons = Array.prototype.slice.call(document.querySelectorAll("[data-balloonpop]"));  // balloonPop (arcade reward; formative, completion-only)
      var galleries = Array.prototype.slice.call(document.querySelectorAll("[data-shootinggallery]"));  // shootingGallery (arcade reward; formative, completion-only)
      var polls = Array.prototype.slice.call(document.querySelectorAll("[data-poll]"));  // poll (no-right-answer check-in, non-graded)
      var reflections = Array.prototype.slice.call(document.querySelectorAll("[data-reflection]"));  // C7 reflection (free text, non-graded, completion-only)
      var wordscrambles = Array.prototype.slice.call(document.querySelectorAll("[data-wordscramble]"));  // wordScramble (formative, completion-only)
      var spothazards = Array.prototype.slice.call(document.querySelectorAll("[data-spothazard]"));  // spotHazard (formative, completion-only)
      var flips = Array.prototype.slice.call(document.querySelectorAll(".nv-flip"));
      var tabsets = Array.prototype.slice.call(document.querySelectorAll("[data-tabs]"));
      var bar   = document.querySelector(".nv-progress > span");
      var prog  = document.querySelector(".nv-progress");
      var endEl = document.querySelector(".nv-course-end");
      var exitBtn = document.querySelector(".nv-exit");

      var graded = document.body.getAttribute("data-graded") === "1";
      var passMark = parseInt(document.body.getAttribute("data-pass") || "80", 10);
      // Align the graded pass threshold with the LMS masteryScore when one is supplied
      // (cmi5 LaunchData; scaled 0..1 per spec, tolerate a 0..100 value too). Authored
      // data-pass is the fallback when the LMS sends none.
      var lmsMastery = (sel.info && typeof sel.info.mastery === "number") ? sel.info.mastery : null;
      if (lmsMastery !== null) passMark = lmsMastery <= 1 ? Math.round(lmsMastery * 100) : Math.round(lmsMastery);
      var maxTries = parseInt(document.body.getAttribute("data-retry") || "0", 10);  // 0 = one-shot
      // Slice B — scored-feedback TIMING mode (opt-in via `*Feedback:* instant|deferred`).
      //   instant : per-question retry (maxTries defaulted to 2 by md_import) + reveal-on-wrong.
      //   deferred: items stay changeable within a *Paged:* section; a "Submit section" control
      //             locks + scores each section (feedback held to the end-of-course review). It
      //             REQUIRES the section pager, so it is keyed on the data-paged intent attribute
      //             here (the pager re-confirms below; if the course has <2 sections DEFERRED is
      //             stood down so nothing gets stuck). Absent (FB="") → terminal per-item checks.
      var FB = document.body.getAttribute("data-feedback") || "";
      var INSTANT = FB === "instant";
      var DEFERRED = FB === "deferred" && document.body.getAttribute("data-paged") === "1";
      // M13 — completion gate (graded courses gate a failing score by default; data-gate="0"
      // = build/author turned it off) + per-section subscore objectives.
      var GATE = document.body.getAttribute("data-gate") !== "0";
      var OBJECTIVES = [];
      try { OBJECTIVES = JSON.parse(document.body.getAttribute("data-objectives") || "[]") || []; }
      catch(e){ OBJECTIVES = []; }
      var lessonIdx = parseInt(document.body.getAttribute("data-lesson") || "1", 10);
      var lessonCount = parseInt(document.body.getAttribute("data-lessons") || "1", 10);
      var notLast = lessonCount > 1 && lessonIdx < lessonCount;

      // points/XP overlay (gamification #3) — a purely motivational HUD, opt-in via the
      // course-level `*Points:* on` directive (render emits data-xp + a hidden .nv-xp HUD).
      // Absent → XP stays null and this whole layer is inert. Config = {w:weights, t:tiers}.
      var XP = null;
      try { var _xj = document.body.getAttribute("data-xp"); if (_xj) XP = JSON.parse(_xj); }
      catch(e){ XP = null; }
      var xpHud = XP ? document.querySelector(".nv-xp") : null;
      var xpPtsEl = xpHud && xpHud.querySelector(".nv-xp-pts");
      var xpTierEl = xpHud && xpHud.querySelector(".nv-xp-tier");
      var xpTierIdx = -1;   // last shown tier index; -1 = not yet rendered (suppresses the resume flourish)

      // confetti celebration overlay (gamification #6) — opt-in via `*Celebrate:* on`
      // (render emits data-celebrate = {pass,level,complete}). Purely cosmetic: a zero-dep
      // canvas burst on the enabled moments, honoring prefers-reduced-motion. Absent → inert.
      var CELEB = null;
      try { var _cj = document.body.getAttribute("data-celebrate"); if (_cj) CELEB = JSON.parse(_cj); }
      catch(e){ CELEB = null; }
      var celebFired = { pass:false, complete:false };   // once-guards; a level-up recurs, no guard
      var confettiActive = false, confettiSeed = 0x1234567;
      var reduceMotion = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);

      // completion certificate (C8) — opt-in via `*Certificate:* on` (render emits
      // data-certificate="1" + data-cert-title). Purely a client-rendered artifact shown
      // once on completion; no server, no metered API, no suspend_data footprint. Absent → inert.
      var CERT_ON = document.body.getAttribute("data-certificate") === "1";
      var CERT_TITLE = document.body.getAttribute("data-cert-title") || "Certificate of Completion";
      var certShown = false;   // once-guard: never re-show automatically (the learner can still print)

      var hasInteractive = gates.length + kcs.length + media.length + reqOpens.length + sorts.length + matches.length + sequences.length + fills.length + drags.length + hotspots.length + wordsearches.length + crosswords.length > 0;
      var kcSeen = {}, kcTries = {}, mediaSeen = {}, openSeen = {}, sortSeen = {}, matchSeen = {}, seqSeen = {}, fillSeen = {}, dragSeen = {}, hotSeen = {}, wsSeen = {}, cwSeen = {}, gsSeen = {}, qbSeen = {}, ssSeen = {}, wamSeen = {}, mmSeen = {}, hgSeen = {}, woffSeen = {}, ixSeen = {}, simSeen = {}, dbSeen = {}, bpSeen = {}, sgSeen = {}, pollSeen = {}, reflectionSeen = {}, scSeen = {}, shSeen = {}, reachedEnd = false, loc = null;
      var gsResetters = [];   // gameShow holds per-block closure state (answered map, revealed slice) → each wiring registers a reset() here for the graded-retry path
      var ssResetters = [];   // speedStreak likewise holds closure state (answered map, streak/score, timer) → reset() registered here for graded-retry
      var qbResetters = [];   // quizBoard likewise holds closure state (answered tiles, open panel) → reset() registered here for graded-retry
      var ixResetters = [];   // interaction engine holds closure state (the {vars,states} machine) → reset() re-inits + re-fires `start` for graded-retry
      var completed = !!(sel.info && sel.info.finished);
      var restoring = false;

      // Required-interaction predicates, keyed by DOM node. Section paging and in-flow
      // Continue gates both read this same registry so there is one definition of "done."
      var interactiveNodes = [];
      function regNode(node, doneFn){ if (node) interactiveNodes.push({ node: node, done: doneFn }); }
      gates.forEach(function(g){ regNode(g, function(){ return g.dataset.passed === "1"; }); });
      kcs.forEach(function(kc, i){ regNode(kc, function(){ return !!kcSeen[i]; }); });
      media.forEach(function(el, i){ regNode(el, function(){ return !!mediaSeen["m" + i]; }); });
      reqOpens.forEach(function(el){ regNode(el, function(){ return !!openSeen[el.getAttribute("data-modal")]; }); });
      sorts.forEach(function(el, i){ regNode(el, function(){ return !!sortSeen["s" + i]; }); });
      matches.forEach(function(el, i){ regNode(el, function(){ return !!matchSeen["mt" + i]; }); });
      sequences.forEach(function(el, i){ regNode(el, function(){ return !!seqSeen["sq" + i]; }); });
      fills.forEach(function(el, i){ regNode(el, function(){ return !!fillSeen["fl" + i]; }); });
      drags.forEach(function(el, i){ regNode(el, function(){ return !!dragSeen["dd" + i]; }); });
      hotspots.forEach(function(el, i){ regNode(el, function(){ return !!hotSeen["ht" + i]; }); });
      wordsearches.forEach(function(el, i){ regNode(el, function(){ return !!wsSeen["ws" + i]; }); });
      crosswords.forEach(function(el, i){ regNode(el, function(){ return !!cwSeen["cw" + i]; }); });
      gameshows.forEach(function(el, i){ regNode(el, function(){ return !!gsSeen["gs" + i]; }); });
      quizboards.forEach(function(el, i){ regNode(el, function(){ return !!qbSeen["qb" + i]; }); });
      speedstreaks.forEach(function(el, i){ regNode(el, function(){ return !!ssSeen["ss" + i]; }); });
      whackamoles.forEach(function(el, i){ regNode(el, function(){ return !!wamSeen["wm" + i]; }); });
      memorymatches.forEach(function(el, i){ regNode(el, function(){ return !!mmSeen["mm" + i]; }); });
      hangmen.forEach(function(el, i){ regNode(el, function(){ return !!hgSeen["hg" + i]; }); });
      wheels.forEach(function(el, i){ regNode(el, function(){ return !!woffSeen["wof" + i]; }); });
      interactions.forEach(function(el, i){ regNode(el, function(){ return !!ixSeen["ix" + i]; }); });
      sims.forEach(function(el, i){ regNode(el, function(){ return !!simSeen["sm" + i]; }); });
      dunkbooths.forEach(function(el, i){ regNode(el, function(){ return !!dbSeen["db" + i]; }); });
      balloons.forEach(function(el, i){ regNode(el, function(){ return !!bpSeen["bp" + i]; }); });
      galleries.forEach(function(el, i){ regNode(el, function(){ return !!sgSeen["sg" + i]; }); });

      function save(){ if (restoring || !RT) return;
        var payload = { g:gates.reduce(function(a,g,i){ if(g.dataset.passed==="1")a.push(i); return a; },[]),
          k:kcSeen, m:Object.keys(mediaSeen), o:Object.keys(openSeen), s:sortSeen, mt:matchSeen, sq:seqSeen, fl:fillSeen, dd:dragSeen, ws:wsSeen, cw:cwSeen, gs:gsSeen, qb:qbSeen, ss:ssSeen, ix:ixSeen, loc:loc };
        if (hotspots.length) payload.ht = hotSeen;   // only hotspot courses carry `ht` (byte-identical otherwise)
        if (banks.length) payload.b = bankState;   // C5 — only bank courses carry `b` (byte-identical otherwise)
        if (whackamoles.length) payload.wm = wamSeen;   // only whack-a-mole courses carry `wm` (byte-identical otherwise)
        if (memorymatches.length) payload.mm = mmSeen;   // only memory-match courses carry `mm` (byte-identical otherwise)
        if (hangmen.length) payload.hg = hgSeen;   // only hangman courses carry `hg` (byte-identical otherwise)
        if (wheels.length) payload.wof = woffSeen;   // only wheel-of-fortune courses carry `wof` (byte-identical otherwise)
        if (sims.length) payload.sm = simSeen;   // only simulation courses carry `sm` (byte-identical otherwise)
        if (dunkbooths.length) payload.db = dbSeen;   // only dunk-booth courses carry `db` (byte-identical otherwise)
        if (balloons.length) payload.bp = bpSeen;   // only balloon-pop courses carry `bp` (byte-identical otherwise)
        if (galleries.length) payload.sg = sgSeen;   // only shooting-gallery courses carry `sg` (byte-identical otherwise)
        if (polls.length) payload.pl = pollSeen;   // only poll courses carry `pl` (byte-identical otherwise)
        if (reflections.length) payload.rf = reflectionSeen;   // only reflection courses carry `rf` (byte-identical otherwise)
        if (wordscrambles.length) payload.sc = scSeen;   // only word-scramble courses carry `sc` (byte-identical otherwise)
        if (spothazards.length) payload.sh = shSeen;   // only spot-hazard courses carry `sh` (byte-identical otherwise)
        if (PAGED) payload.pg = curPage;   // section pager — only paged courses carry `pg` (byte-identical otherwise)
        RT.save(payload); }
      function gradedScore(){
        // Feed the pure aggregator one item per KC: its section objective (data-obj) + whether
        // the learner's final answer was correct. With objectives, only tagged KCs are summative.
        var items = kcs.map(function(kc,i){
          return { obj: kc.getAttribute("data-obj") || null, ok: !!(kcSeen[i] && kcSeen[i].ok) }; });
        // M12 — matching/sequencing/fill blocks contribute FRACTIONAL {got,max} credit, but ONLY
        // when tagged into a graded *Section:* (data-obj present). Untagged blocks stay formative.
        function addPartials(nodes, seen, prefix){
          nodes.forEach(function(el,i){ var obj = el.getAttribute("data-obj"); if (!obj) return;
            var r = seen[prefix+i]; if (!r) return;
            items.push({ obj: obj, ok: !!r.ok, got: r.got, max: r.max }); });
        }
        addPartials(sorts, sortSeen, "s");   // Slice C — categorize/classification, scored when tagged into a graded *Section:*
        addPartials(matches, matchSeen, "mt");
        addPartials(sequences, seqSeen, "sq");
        addPartials(fills, fillSeen, "fl");
        addPartials(drags, dragSeen, "dd");
        addPartials(hotspots, hotSeen, "ht");
        addPartials(wordsearches, wsSeen, "ws");
        addPartials(crosswords, cwSeen, "cw");
        addPartials(gameshows, gsSeen, "gs");
        addPartials(quizboards, qbSeen, "qb");
        addPartials(speedstreaks, ssSeen, "ss");
        addPartials(interactions, ixSeen, "ix");
        return aggregateScore(items, passMark, OBJECTIVES);
      }

      // C8 — completion certificate. Built entirely via DOM APIs (never innerHTML string
      // concat) because the learner name comes from the LMS/xAPI actor — an untrusted
      // source — so every dynamic value goes through .textContent, never HTML parsing.
      function showCertificate(){
        if (!CERT_ON || certShown) return; certShown = true;
        var name = (RT && RT.learnerName && RT.learnerName()) || "";
        var titleEl = document.querySelector(".nv-title");
        var courseTitle = (titleEl && titleEl.textContent) || document.title || "";
        var logoImg = document.querySelector(".nv-topbar img");
        var dateStr = new Date().toLocaleDateString(undefined, { year:"numeric", month:"long", day:"numeric" });

        var overlay = document.createElement("div");
        overlay.className = "nv-cert-overlay"; overlay.setAttribute("role","dialog");
        overlay.setAttribute("aria-label", CERT_TITLE); overlay.setAttribute("aria-modal","true");

        var card = document.createElement("div"); card.className = "nv-cert-card";
        var closeBtn = document.createElement("button");
        closeBtn.type = "button"; closeBtn.className = "nv-cert-close";
        closeBtn.setAttribute("aria-label","Close"); closeBtn.textContent = "×";
        closeBtn.addEventListener("click", function(){ overlay.remove(); });

        var inner = document.createElement("div"); inner.className = "nv-cert-inner";
        if (logoImg && logoImg.src) {
          var logo = document.createElement("img");
          logo.className = "nv-cert-logo"; logo.src = logoImg.src; logo.alt = "";
          inner.appendChild(logo);
        }
        function row(cls, text){
          var d = document.createElement("div"); d.className = cls; d.textContent = text;
          inner.appendChild(d); return d;
        }
        row("nv-cert-kicker", CERT_TITLE);
        var nameEl = row("nv-cert-name", name || "Your Name");
        nameEl.id = "nv-cert-name";
        if (!name) {
          // no LMS-supplied name — let the learner type their own directly on the certificate
          nameEl.contentEditable = "true"; nameEl.spellcheck = false;
          nameEl.classList.add("nv-cert-name--editable");
          nameEl.addEventListener("focus", function(){
            if (nameEl.textContent === "Your Name") nameEl.textContent = "";
          });
        }
        row("nv-cert-body", "has successfully completed");
        row("nv-cert-course", courseTitle);
        row("nv-cert-date", dateStr);

        var actions = document.createElement("div"); actions.className = "nv-cert-actions";
        var printBtn = document.createElement("button");
        printBtn.type = "button"; printBtn.className = "nv-btn nv-cert-print";
        printBtn.textContent = "🖨 Print / Save as PDF";
        printBtn.addEventListener("click", function(){ window.print(); });
        actions.appendChild(printBtn);

        card.appendChild(closeBtn); card.appendChild(inner); card.appendChild(actions);
        overlay.appendChild(card); document.body.appendChild(overlay);
      }

      function enableEndButton(){
        if (!exitBtn) return;
        exitBtn.disabled = false;
        // SCORM 1.2 has no next-SCO API, so a multi-SCO "lesson" can't navigate
        // onward from here — don't promise it. Exit cleanly; the LMS menu drives
        // sequencing.
        // A6 — a standalone single-SCO quiz/course ends with a plain "Finish"; the final SCO
        // of a multi-lesson course keeps "Finish course" (it completes the whole course).
        exitBtn.textContent = notLast ? "Lesson complete — continue from the menu" : (lessonCount <= 1 ? "Finish" : "Finish course");
      }
      // Fire a zero-dependency confetti burst (gamification #6). Cosmetic + ephemeral: an
      // ad-hoc full-viewport <canvas> animates ~1.5s then removes itself. Honors reduced-motion
      // (no burst), never persists, and is Math.random-free (a per-fire seed → makeRng), so it
      // touches neither the graded score, the completion gate, nor suspend_data. If a burst is
      // already running, or canvas/rAF is unavailable, it no-ops.
      function confettiColors(){
        var out = [];
        try { var cs = window.getComputedStyle(document.body);
          ["--brand-accent","--brand-correct","--brand-heading","--brand-accent-ink","--brand-light"].forEach(function(v){
            var c = cs.getPropertyValue(v).trim(); if (c) out.push(c); }); } catch(e){}
        return out.length ? out : ["#1EB16A","#f5a623","#4a90d9","#e94b3c","#f8e71c"];
      }
      function fireConfetti(){
        if (!CELEB || reduceMotion || confettiActive) return;
        var body = document.body; if (!body) return;
        var cv = document.createElement("canvas");
        if (!cv.getContext || !window.requestAnimationFrame) return;   // ancient LMS webview → skip silently
        confettiActive = true;
        cv.className = "nv-confetti"; cv.setAttribute("aria-hidden", "true");
        var w = cv.width = window.innerWidth || 800, h = cv.height = window.innerHeight || 600;
        body.appendChild(cv);
        var ctx = cv.getContext("2d");
        var colors = confettiColors();
        confettiSeed = (confettiSeed + 0x9E3779B1) | 0;   // vary each fire, no Math.random
        var rng = makeRng(confettiSeed), parts = [], N = 130;
        for (var i=0;i<N;i++){ parts.push({
          x: w*(0.15 + 0.7*rng()), y: -20 - h*0.25*rng(),
          vx: (rng()-0.5)*6, vy: 3 + rng()*5, sz: 5 + rng()*7,
          rot: rng()*6.283, vr: (rng()-0.5)*0.34, col: colors[i % colors.length] }); }
        var start = null, DUR = 1500;
        function frame(ts){
          if (start === null) start = ts;
          var el = ts - start, a = Math.max(0, 1 - el/DUR);
          ctx.clearRect(0,0,w,h);
          for (var i=0;i<parts.length;i++){ var p = parts[i];
            p.x += p.vx; p.y += p.vy; p.vy += 0.12; p.rot += p.vr;
            ctx.save(); ctx.translate(p.x, p.y); ctx.rotate(p.rot);
            ctx.globalAlpha = a; ctx.fillStyle = p.col;
            ctx.fillRect(-p.sz/2, -p.sz/2, p.sz, p.sz*0.6); ctx.restore(); }
          if (el < DUR) window.requestAnimationFrame(frame);
          else { if (cv.parentNode) cv.parentNode.removeChild(cv); confettiActive = false; }
        }
        window.requestAnimationFrame(frame);
      }
      // Gate a celebration by config + resume state, then fire. Suppressed entirely during
      // restore (a resumed pass/complete/level must not re-burst — mirrors the XP resume guard).
      function celebrate(reason){
        if (!CELEB || restoring) return;
        var fired = reason === "pass" ? celebFired.pass : (reason === "complete" ? celebFired.complete : false);
        if (!celebrateAllowed(CELEB, reason, fired)) return;
        if (reason === "pass") celebFired.pass = true;
        else if (reason === "complete") celebFired.complete = true;
        fireConfetti();
      }
      // Re-derive the XP total + level tier from the CURRENT block state and paint the HUD.
      // Called after every block resolves (via updateProgress) and once after restore — so
      // resume shows the right total with no persisted XP. A tier increase flashes a subtle
      // level-up (skipped on the first paint / resume, when xpTierIdx is still -1).
      function renderXp(){
        if (!XP || !xpHud) return;
        var t = xpTotals([
          { kind:"kc", seen:kcSeen, count:kcs.length },
          { kind:"sort", seen:sortSeen, count:sorts.length },
          { kind:"mt", seen:matchSeen, count:matches.length },
          { kind:"sq", seen:seqSeen, count:sequences.length },
          { kind:"fl", seen:fillSeen, count:fills.length },
          { kind:"dd", seen:dragSeen, count:drags.length },
          { kind:"ht", seen:hotSeen, count:hotspots.length },
          { kind:"ws", seen:wsSeen, count:wordsearches.length },
          { kind:"cw", seen:cwSeen, count:crosswords.length },
          { kind:"gs", seen:gsSeen, count:gameshows.length },
          { kind:"qb", seen:qbSeen, count:quizboards.length },
          { kind:"ss", seen:ssSeen, count:speedstreaks.length }
        ], XP.w);
        if (t.possible <= 0) { xpHud.hidden = true; return; }   // nothing scorable → no dead HUD
        xpHud.hidden = false;
        var tier = tierFor(t.earned / t.possible, XP.t);
        if (xpPtsEl) xpPtsEl.textContent = t.earned;
        if (xpTierEl) xpTierEl.textContent = tier.name;
        if (xpTierIdx >= 0 && tier.index > xpTierIdx){
          xpHud.classList.remove("nv-xp--up");
          void xpHud.offsetWidth;                 // restart the flash if two tiers cross fast
          xpHud.classList.add("nv-xp--up");
          celebrate("level");                     // gamification #6 — confetti on a genuine tier-up (not first paint/resume)
        }
        xpTierIdx = tier.index;
      }
      function updateProgress(){
        var total = gates.length + kcs.length + media.length + reqOpens.length + sorts.length + matches.length + sequences.length + fills.length + drags.length + hotspots.length + wordsearches.length + crosswords.length + gameshows.length + quizboards.length + speedstreaks.length + whackamoles.length + memorymatches.length + hangmen.length + wheels.length + interactions.length + sims.length + dunkbooths.length + balloons.length + galleries.length + polls.length + reflections.length + wordscrambles.length + spothazards.length || 1;
        var done = gates.filter(function(g){return g.dataset.passed==="1";}).length
          + Object.keys(kcSeen).length + Object.keys(mediaSeen).length + Object.keys(openSeen).length
          + Object.keys(sortSeen).length + Object.keys(matchSeen).length + Object.keys(seqSeen).length + Object.keys(fillSeen).length + Object.keys(dragSeen).length + Object.keys(hotSeen).length + Object.keys(wsSeen).length + Object.keys(cwSeen).length + Object.keys(gsSeen).length + Object.keys(qbSeen).length + Object.keys(ssSeen).length + Object.keys(wamSeen).length + Object.keys(mmSeen).length + Object.keys(hgSeen).length + Object.keys(woffSeen).length + Object.keys(ixSeen).length + Object.keys(simSeen).length + Object.keys(dbSeen).length + Object.keys(bpSeen).length + Object.keys(sgSeen).length + Object.keys(pollSeen).length + Object.keys(reflectionSeen).length + Object.keys(scSeen).length + Object.keys(shSeen).length;
        var pct = Math.min(100, Math.round(done/total*100));
        if (bar) bar.style.width = pct + "%";
        if (prog) prog.setAttribute("aria-valuenow", pct);
        if (XP) renderXp();
        refreshContinueGates();
        maybeCelebratePass();
        save(); maybeComplete();
        refreshPager();   // re-evaluate each page's Next-button gate (no-op unless paged)
      }
      // gamification #6 — fire confetti the first time a graded course crosses the pass mark.
      // Checked on every progress tick (cheap); the once-guard + `restoring` guard keep it to a
      // single burst and suppress it on resume. Only meaningful when there's something summative.
      function maybeCelebratePass(){
        if (!CELEB || !CELEB.pass || restoring || celebFired.pass) return;
        if (!(graded && (OBJECTIVES.length || kcs.length))) return;
        if (gradedScore().passed) celebrate("pass");
      }
      function maybeComplete(){
        if (completed) { enableEndButton(); updateReview(); return; }
        var ok = gates.every(function(g){return g.dataset.passed==="1";})
          && kcs.length===Object.keys(kcSeen).length && media.length===Object.keys(mediaSeen).length
          && reqOpens.length===Object.keys(openSeen).length && sorts.length===Object.keys(sortSeen).length
          && matches.length===Object.keys(matchSeen).length
          && sequences.length===Object.keys(seqSeen).length
          && fills.length===Object.keys(fillSeen).length
          && drags.length===Object.keys(dragSeen).length
          && hotspots.length===Object.keys(hotSeen).length
          && wordsearches.length===Object.keys(wsSeen).length
          && crosswords.length===Object.keys(cwSeen).length
          && gameshows.length===Object.keys(gsSeen).length
          && quizboards.length===Object.keys(qbSeen).length
          && speedstreaks.length===Object.keys(ssSeen).length
          && whackamoles.length===Object.keys(wamSeen).length
          && memorymatches.length===Object.keys(mmSeen).length
          && hangmen.length===Object.keys(hgSeen).length
          && wheels.length===Object.keys(woffSeen).length
          && interactions.length===Object.keys(ixSeen).length
          && sims.length===Object.keys(simSeen).length
          && dunkbooths.length===Object.keys(dbSeen).length
          && balloons.length===Object.keys(bpSeen).length
          && galleries.length===Object.keys(sgSeen).length
          && polls.length===Object.keys(pollSeen).length
          && reflections.length===Object.keys(reflectionSeen).length
          && wordscrambles.length===Object.keys(scSeen).length
          && spothazards.length===Object.keys(shSeen).length
          && (hasInteractive || reachedEnd);
        if (!ok) return;
        // A graded course that the learner FAILED must not complete (cmi5
        // CompletedAndPassed would never satisfy → they'd be stuck). Offer a
        // retry instead and hold completion until they reach the pass mark.
        // M13 — unless gating is off (data-gate="0"), in which case the course
        // completes regardless of score (the score is still reported).
        // M12→M13 — gate whenever there is something SUMMATIVE to score: any graded
        // objective (a KC or a matching/sequencing/fill block tagged into a graded
        // *Section:*) OR the KC-fallback. The `kcs.length` disjunct keeps a graded course
        // with only formative interactive blocks from gating on an empty score (→ stuck).
        if (graded && GATE && (OBJECTIVES.length || kcs.length) && !gradedScore().passed) { offerRetry(); return; }
        completed = true; if (RT) RT.complete(graded ? gradedScore() : null);
        if (graded && RT && RT.interaction) { var n=0; kcs.forEach(function(kc,i){ var r=kcSeen[i]; if(r) RT.interaction(n++, kc.getAttribute("data-kc-id")||("kc"+i), String(r.opt), r.ok); }); }
        if (bar) bar.style.width = "100%"; if (prog) prog.setAttribute("aria-valuenow", 100); enableEndButton();
        celebrate("complete");                    // gamification #6 — confetti on reaching 100% (suppressed on resume)
        if (!restoring) showCertificate();         // C8 — never auto-pop on a resumed/already-complete relaunch
        updateReview();                            // formative recap of any missed questions
      }

      // Graded retry: clear quiz state so the learner can re-attempt to reach mastery.
      var retryBtn = null;
      function resetQuiz(){
        Object.keys(kcSeen).forEach(function(k){ delete kcSeen[k]; });
        Object.keys(kcTries).forEach(function(k){ delete kcTries[k]; });
        Object.keys(sortSeen).forEach(function(k){ delete sortSeen[k]; });
        Object.keys(matchSeen).forEach(function(k){ delete matchSeen[k]; });
        Object.keys(seqSeen).forEach(function(k){ delete seqSeen[k]; });
        Object.keys(fillSeen).forEach(function(k){ delete fillSeen[k]; });
        Object.keys(wsSeen).forEach(function(k){ delete wsSeen[k]; });
        Object.keys(cwSeen).forEach(function(k){ delete cwSeen[k]; });
        Object.keys(gsSeen).forEach(function(k){ delete gsSeen[k]; });
        Object.keys(qbSeen).forEach(function(k){ delete qbSeen[k]; });
        Object.keys(ssSeen).forEach(function(k){ delete ssSeen[k]; });
        Object.keys(dragSeen).forEach(function(k){ delete dragSeen[k]; });
        Object.keys(hotSeen).forEach(function(k){ delete hotSeen[k]; });
        kcs.forEach(function(kc){
          var isMulti=kc.classList.contains("nv-kc--multi");
          Array.prototype.slice.call(kc.querySelectorAll(".nv-kc-opt")).forEach(function(o){ o.classList.remove("correct","incorrect","is-disabled","is-selected"); o.disabled=false; var mk=o.querySelector(".nv-kc-mark"); if(mk)mk.remove(); if(isMulti)o.setAttribute("aria-pressed","false"); });
          var sub=kc.querySelector(".nv-kc-submit"); if(sub)sub.disabled=false;
          var fb=kc.querySelector(".nv-kc-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        sorts.forEach(function(sort){
          Array.prototype.slice.call(sort.querySelectorAll(".nv-sort-item")).forEach(function(li){ li.classList.remove("correct","incorrect","is-locked"); });
          Array.prototype.slice.call(sort.querySelectorAll(".nv-sort-pick")).forEach(function(p){ p.disabled=false; p.value=""; });
          var b=sort.querySelector(".nv-sort-check"); if(b)b.disabled=false;
          var fb=sort.querySelector(".nv-sort-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        matches.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-match-item")).forEach(function(li){ li.classList.remove("correct","incorrect","is-locked"); });
          Array.prototype.slice.call(el.querySelectorAll(".nv-match-pick")).forEach(function(p){ p.disabled=false; p.value=""; });
          var b=el.querySelector(".nv-match-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-match-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        sequences.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-seq-item")).forEach(function(li){ li.classList.remove("correct","incorrect","is-locked"); });
          Array.prototype.slice.call(el.querySelectorAll(".nv-seq-pick")).forEach(function(p){ p.disabled=false; p.value=""; });
          var b=el.querySelector(".nv-seq-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-seq-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        fills.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-fill-item")).forEach(function(li){ li.classList.remove("correct","incorrect","is-locked"); });
          Array.prototype.slice.call(el.querySelectorAll(".nv-fill-input")).forEach(function(inp){ inp.disabled=false; inp.value=""; });
          var b=el.querySelector(".nv-fill-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-fill-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        drags.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-drag-item")).forEach(function(li){ li.classList.remove("correct","incorrect","is-locked"); var p=li.querySelector(".nv-drag-pick"); if(p){ p.disabled=false; p.value=""; } });
          Array.prototype.slice.call(el.querySelectorAll(".nv-drag-zone")).forEach(function(z){ z.classList.remove("nv-drag-over","nv-drag-filled"); });
          var b=el.querySelector(".nv-drag-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-drag-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        hotspots.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot")).forEach(function(sp){ sp.classList.remove("correct","incorrect","is-selected","is-locked"); sp.disabled=false; sp.setAttribute("aria-pressed","false"); });
          var b=el.querySelector(".nv-hotspot-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-hotspot-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        wordsearches.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-ws-cell")).forEach(function(c){ c.classList.remove("nv-ws-sel","nv-ws-found"); });
          Array.prototype.slice.call(el.querySelectorAll(".nv-ws-word")).forEach(function(w){ w.classList.remove("found"); });
          var b=el.querySelector(".nv-ws-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-ws-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        crosswords.forEach(function(el){
          Array.prototype.slice.call(el.querySelectorAll(".nv-cw-input")).forEach(function(inp){ inp.disabled=false; inp.value=""; inp.classList.remove("correct","incorrect","is-active"); if (inp.parentNode) inp.parentNode.classList.remove("in-clue"); });
          Array.prototype.slice.call(el.querySelectorAll(".nv-cw-clue")).forEach(function(li){ li.classList.remove("solved","is-active"); });
          var b=el.querySelector(".nv-cw-check"); if(b)b.disabled=false;
          var fb=el.querySelector(".nv-cw-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
        gsResetters.forEach(function(fn){ fn(); });   // gameShow: closure-held answered state + wheel/panels
        qbResetters.forEach(function(fn){ fn(); });   // quizBoard: closure-held answered tiles + open panel
        ssResetters.forEach(function(fn){ fn(); });   // speedStreak: closure-held answered state + streak/score + timer
        Object.keys(ixSeen).forEach(function(k){ delete ixSeen[k]; });
        ixResetters.forEach(function(fn){ fn(); });   // interaction engine: re-init the {vars,states} machine + re-fire `start`
        completed=false; loc=null;
        if (PAGED) showPage(0);   // section pager — a graded retry returns to the first page
        updateProgress();
      }
      function offerRetry(){
        var gs = gradedScore();
        if (!retryBtn){
          retryBtn = document.createElement("button");
          retryBtn.type = "button"; retryBtn.className = "nv-btn nv-retry-quiz";
          retryBtn.addEventListener("click", function(){
            if (retryBtn && retryBtn.parentNode) retryBtn.parentNode.removeChild(retryBtn);
            retryBtn = null; resetQuiz();
            (kcs[0]||document.querySelector(".nv-main")||document.body).scrollIntoView({behavior:"smooth",block:"start"});
          });
        }
        retryBtn.innerHTML = '<span class="nv-sr-only" role="status">You scored '+gs.raw+'%, need '+passMark+'% to pass. </span>Retry quiz';
        if (!retryBtn.parentNode){
          if (exitBtn && exitBtn.parentNode) exitBtn.parentNode.insertBefore(retryBtn, exitBtn);
          else (endEl||document.body).appendChild(retryBtn);
        }
      }

      // ---- Review what you missed (formative recap) --------------------------
      // At completion, scrape every graded interactive into plain {el,attempted,ok,
      // head,rows} records (reusing the SAME seen maps + the correct answers that
      // already live in the DOM), hand them to the pure reviewEntries() filter, and
      // if any survive attach a collapsible recap listing each missed question and
      // its correct answer. Ephemeral + resume-safe: rebuilt from the live DOM each
      // call (a retry can change the miss set), stores nothing of its own.
      var reviewBtn = null, reviewPanel = null; var REVIEW_ID = "nv-review-panel";
      function rvText(el){ return el ? (el.textContent || "").replace(/\s+/g, " ").trim() : ""; }
      function rvOptAt(panel, optSel){   // the correct-option label of one MCQ panel (data-answer index)
        var opts = Array.prototype.slice.call(panel.querySelectorAll(optSel));
        var ai = parseInt(panel.getAttribute("data-answer") || "0", 10);
        return opts[ai] ? rvText(opts[ai]) : ""; }
      function rvWheel(el, panelSel, qSel, optSel){   // gameShow/quizBoard/speedStreak: q → correct option, per panel
        return Array.prototype.slice.call(el.querySelectorAll(panelSel)).map(function(p){
          return { q: rvText(p.querySelector(qSel)), a: rvOptAt(p, optSel) }; }); }
      function scrapeReview(){
        var recs = [];
        function add(el, seen, head, rows){ recs.push({ el:el, attempted:!!seen, ok:!!(seen && seen.ok), head:head, rows:rows }); }
        kcs.forEach(function(el,i){
          var correct = Array.prototype.slice.call(el.querySelectorAll('.nv-kc-opt[data-correct="1"]')).map(rvText).join(", ");
          add(el, kcSeen[i], "Knowledge check", [{ q: rvText(el.querySelector(".nv-kc-prompt")), a: correct }]); });
        matches.forEach(function(el,i){
          var idText = {}; Array.prototype.slice.call(el.querySelectorAll(".nv-match-pick option")).forEach(function(o){ if (o.value) idText[o.value] = rvText(o); });
          add(el, matchSeen["mt"+i], "Matching", Array.prototype.slice.call(el.querySelectorAll(".nv-match-item")).map(function(li){
            return { q: rvText(li.querySelector(".nv-match-label")), a: idText[li.getAttribute("data-answer")] || "" }; })); });
        sequences.forEach(function(el,i){
          var rows = Array.prototype.slice.call(el.querySelectorAll(".nv-seq-item")).map(function(li){
            var pos = parseInt(li.getAttribute("data-pos") || "0", 10);
            return { q: rvText(li.querySelector(".nv-seq-label")), a: "Position " + pos, _p: pos }; });
          rows.sort(function(a,b){ return a._p - b._p; });
          add(el, seqSeen["sq"+i], "Sequence", rows); });
        fills.forEach(function(el,i){
          add(el, fillSeen["fl"+i], "Fill in the blank", Array.prototype.slice.call(el.querySelectorAll(".nv-fill-item")).map(function(li){
            var ans = []; try { ans = JSON.parse(li.getAttribute("data-answers") || "[]") || []; } catch(e){ ans = []; }
            return { q: rvText(li.querySelector(".nv-fill-text")), a: ans.join(" / ") }; })); });
        drags.forEach(function(el,i){
          var zoneTitle = {}; Array.prototype.slice.call(el.querySelectorAll(".nv-drag-zone")).forEach(function(z){ zoneTitle[z.getAttribute("data-zone")] = rvText(z.querySelector(".nv-drag-zone-title")); });
          add(el, dragSeen["dd"+i], "Drag and drop", Array.prototype.slice.call(el.querySelectorAll(".nv-drag-item")).map(function(li){
            return { q: rvText(li.querySelector(".nv-drag-label")), a: zoneTitle[li.getAttribute("data-target")] || "" }; })); });
        hotspots.forEach(function(el,i){
          add(el, hotSeen["ht"+i], "Hotspot", Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot")).filter(function(sp){ return sp.getAttribute("data-correct")==="1"; }).map(function(sp){
            return { q: rvText(sp.querySelector(".nv-hotspot-label")), a: "Correct area to click" }; })); });
        wordsearches.forEach(function(el,i){
          add(el, wsSeen["ws"+i], "Word search", Array.prototype.slice.call(el.querySelectorAll(".nv-ws-word")).map(function(li){
            var clue = rvText(li.querySelector(".nv-ws-clue")).replace(/^[—-]\s*/, "");
            return { q: clue || "Find this word", a: rvText(li.querySelector(".nv-ws-term")) }; })); });
        crosswords.forEach(function(el,i){
          add(el, cwSeen["cw"+i], "Crossword", Array.prototype.slice.call(el.querySelectorAll(".nv-cw-clue")).map(function(li){
            return { q: rvText(li), a: li.getAttribute("data-answer") || "" }; })); });
        gameshows.forEach(function(el,i){ add(el, gsSeen["gs"+i], "Game-show quiz", rvWheel(el, ".nv-gs-panel", ".nv-gs-q", ".nv-gs-optlabel")); });
        quizboards.forEach(function(el,i){ add(el, qbSeen["qb"+i], "Quiz board", rvWheel(el, ".nv-qb-panel", ".nv-qb-q", ".nv-qb-optlabel")); });
        speedstreaks.forEach(function(el,i){ add(el, ssSeen["ss"+i], "Speed round", rvWheel(el, ".nv-ss-panel", ".nv-ss-q", ".nv-ss-optlabel")); });
        interactions.forEach(function(el,i){ add(el, ixSeen["ix"+i], "Interactive activity", [{ q: rvText(el.querySelector(".nv-ix-prompt")), a: "" }]); });
        recs.sort(function(a,b){ var p = a.el.compareDocumentPosition(b.el); return (p & 4) ? -1 : ((p & 2) ? 1 : 0); });  // 4=FOLLOWING, 2=PRECEDING → document order
        return reviewEntries(recs);
      }
      function renderReview(entries){
        var wrap = document.createElement("section");
        wrap.id = REVIEW_ID; wrap.className = "nv-review-panel"; wrap.hidden = true;
        wrap.setAttribute("aria-label", "Review what you missed");
        var h = document.createElement("h2"); h.className = "nv-review-title"; h.textContent = "Review what you missed"; wrap.appendChild(h);
        var ol = document.createElement("ol"); ol.className = "nv-review-list";
        entries.forEach(function(en){
          var li = document.createElement("li"); li.className = "nv-review-entry";
          var hd = document.createElement("div"); hd.className = "nv-review-head"; hd.textContent = en.head; li.appendChild(hd);
          en.rows.forEach(function(row){
            var qa = document.createElement("div"); qa.className = "nv-review-qa";
            if (row.q){ var q = document.createElement("span"); q.className = "nv-review-q"; q.textContent = row.q; qa.appendChild(q); }
            var a = document.createElement("span"); a.className = "nv-review-a";
            a.textContent = row.a ? ("Correct answer: " + row.a) : "Revisit this activity.";
            qa.appendChild(a); li.appendChild(qa);
          });
          ol.appendChild(li);
        });
        wrap.appendChild(ol); return wrap;
      }
      function updateReview(){
        var entries = scrapeReview();
        if (!entries.length){   // a perfect run (or nothing gradeable) → no button/panel
          if (reviewBtn && reviewBtn.parentNode) reviewBtn.parentNode.removeChild(reviewBtn);
          if (reviewPanel && reviewPanel.parentNode) reviewPanel.parentNode.removeChild(reviewPanel);
          reviewBtn = reviewPanel = null; return;
        }
        var host = endEl || document.body;
        if (!reviewBtn){
          reviewBtn = document.createElement("button");
          reviewBtn.type = "button"; reviewBtn.className = "nv-btn nv-review-btn";
          reviewBtn.setAttribute("aria-expanded", "false"); reviewBtn.setAttribute("aria-controls", REVIEW_ID);
          reviewBtn.addEventListener("click", function(){
            var open = reviewBtn.getAttribute("aria-expanded") === "true";
            reviewBtn.setAttribute("aria-expanded", open ? "false" : "true");
            if (reviewPanel){ reviewPanel.hidden = open; if (!open) reviewPanel.scrollIntoView({ behavior:"smooth", block:"nearest" }); }
          });
        }
        reviewBtn.innerHTML = '<span class="nv-sr-only" role="status">You missed ' + entries.length + ' — </span>🔍 Review what you missed (' + entries.length + ')';
        var wasOpen = reviewBtn.getAttribute("aria-expanded") === "true";
        var fresh = renderReview(entries); fresh.hidden = !wasOpen;   // rebuild fresh (a retry may change the miss set), keep open state
        if (reviewPanel && reviewPanel.parentNode) reviewPanel.parentNode.replaceChild(fresh, reviewPanel);
        reviewPanel = fresh;
        var anchor = (exitBtn && exitBtn.parentNode === host) ? exitBtn : null;   // order: review button → panel → exit
        host.insertBefore(reviewBtn, anchor);
        host.insertBefore(reviewPanel, anchor);
      }

      function revealAfter(gate){
        var all = Array.prototype.slice.call(document.querySelectorAll(".nv-gated"));
        for (var gi=0; gi<all.length; gi++){
          var r = all[gi];
          if ((gate.compareDocumentPosition(r) & Node.DOCUMENT_POSITION_FOLLOWING) && !r.classList.contains("revealed")){
            r.classList.add("revealed"); return r;
          }
        }
        return null;
      }
      function isAfter(a, b){ return !a || !!(a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING); }
      function isBefore(a, b){ return !b || !!(a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING); }
      function gateChunkItems(gate){
        var main = document.querySelector(".nv-main");
        if (!main) return { view: [], req: [] };
        var gi = gates.indexOf(gate), prev = gi > 0 ? gates[gi - 1] : null;
        function inChunk(node){ return node && node !== gate && isAfter(prev, node) && isBefore(node, gate); }
        function topContentNode(node){
          if (!inChunk(node)) return false;
          if (node.classList && node.classList.contains("nv-continue")) return false;
          var p = node.parentElement;
          while (p && p !== main) {
            if (p.classList && (p.classList.contains("nv-section") || p.classList.contains("nv-block"))) return false;
            p = p.parentElement;
          }
          return true;
        }
        var view = Array.prototype.slice.call(main.querySelectorAll(".nv-section, .nv-block")).filter(topContentNode);
        var req = interactiveNodes.filter(function(e){ return e.node !== gate && inChunk(e.node); });
        return { view: view, req: req };
      }
      function setGateHint(gate, text){
        var hint = gate.querySelector(".nv-continue-status");
        if (!hint) {
          hint = document.createElement("div");
          hint.className = "nv-continue-status";
          hint.setAttribute("role", "status");
          gate.appendChild(hint);
        }
        hint.textContent = text || "";
      }
      function gateReady(gate){
        if (gate.dataset.passed === "1") return true;
        var view = gate.__viewNodes || [];
        var req = gate.__reqNodes || [];
        var viewed = view.every(function(node){ return node.dataset.nvViewed === "1"; });
        var done = req.every(function(e){ return e.done(); });
        gate.dataset.viewed = viewed ? "1" : "0";
        gate.dataset.interacted = done ? "1" : "0";
        return viewed && done;
      }
      function refreshContinueGates(){
        gates.forEach(function(gate){
          var btn = gate.querySelector(".nv-btn");
          if (!btn || !gate.__readyTracked) return;
          var ready = gateReady(gate);
          if (gate.dataset.passed === "1") {
            btn.disabled = true;
            gate.classList.remove("is-locked");
            gate.classList.add("is-passed");
            setGateHint(gate, "");
            return;
          }
          btn.disabled = !ready;
          gate.classList.toggle("is-locked", !ready);
          gate.classList.toggle("is-ready", ready);
          if (ready) setGateHint(gate, "Ready to continue.");
          else if (gate.dataset.interacted !== "1") setGateHint(gate, "Complete the activity above to continue.");
          else setGateHint(gate, "Review the section above to continue.");
        });
      }
      function setupContinueGates(){
        if (!gates.length) return;
        var viewNodes = [];
        gates.forEach(function(gate){
          var chunk = gateChunkItems(gate);
          gate.__viewNodes = chunk.view;
          gate.__reqNodes = chunk.req;
          gate.__readyTracked = true;
          chunk.view.forEach(function(node){ if (viewNodes.indexOf(node) < 0) viewNodes.push(node); });
        });
        if ("IntersectionObserver" in window) {
          var io = new IntersectionObserver(function(entries){
            entries.forEach(function(entry){
              if (entry.isIntersecting) {
                entry.target.dataset.nvViewed = "1";
                io.unobserve(entry.target);
              }
            });
            refreshContinueGates();
          }, { threshold: 0.01, rootMargin: "0px 0px -8% 0px" });
          viewNodes.forEach(function(node){ io.observe(node); });
        } else {
          viewNodes.forEach(function(node){ node.dataset.nvViewed = "1"; });
        }
        refreshContinueGates();
      }
      function passGate(gate,i){
        if (!restoring && !gateReady(gate)) { refreshContinueGates(); return; }
        gate.dataset.passed="1"; var b=gate.querySelector(".nv-btn"); if(b)b.disabled=true; var r=revealAfter(gate); loc={t:"g",i:i}; refreshContinueGates(); return r;
      }
      // a11y: append an off-screen "(correct answer)"/"(incorrect)" tag to a locked
      // option so a screen-reader user gets the verdict that's otherwise color-only.
      // Idempotent — clears any prior tag first (graded retry re-locks the same options).
      function srMarkOpt(o){ var ex=o.querySelector(".nv-kc-mark"); if(ex)ex.remove();
        var t = o.classList.contains("correct") ? " (correct answer)" : (o.classList.contains("incorrect") ? " (incorrect)" : "");
        if(t){ var s=document.createElement("span"); s.className="nv-sr-only nv-kc-mark"; s.textContent=t; o.appendChild(s); } }
      // terminal KC render: mark choice, reveal correct if wrong, lock, show feedback, record.
      // `silent` (deferred mode) → record + disable, but SUPPRESS the correct/incorrect reveal and
      // feedback (held to the end-of-course review). oi may be -1 (section submitted with no pick).
      function lockKc(kc,i,oi,ok,silent){ var opts=Array.prototype.slice.call(kc.querySelectorAll(".nv-kc-opt")), fb=kc.querySelector(".nv-kc-fb"), opt=opts[oi];
        if(!silent){
          if(opt) opt.classList.add(ok?"correct":"incorrect");
          if(!ok) opts.forEach(function(o){ if(o.dataset.correct==="1")o.classList.add("correct"); });
        }
        opts.forEach(function(o){ o.classList.add("is-disabled"); o.disabled=true; if(!silent) srMarkOpt(o); });
        if(!silent && fb){ var m = ok?fb.getAttribute("data-fb-correct"):fb.getAttribute("data-fb-incorrect");
          fb.innerHTML='<span class="nv-sr-only">'+(ok?"Correct. ":"Incorrect. ")+'</span>'+(ok?(m||""):("Not quite."+(m?" "+m:""))); fb.classList.remove("ok","no"); fb.classList.add("show", ok?"ok":"no"); }  // A7: visible negative lead-in on terminal-incorrect
        kcSeen[i]={opt:oi,ok:ok}; loc={t:"kc",i:i}; }
      // terminal multi-select render: reveal the full correct set, flag wrong picks, lock, record.
      function lockKcMulti(kc,i,sel,ok,silent){ var opts=Array.prototype.slice.call(kc.querySelectorAll(".nv-kc-opt")), fb=kc.querySelector(".nv-kc-fb"), submit=kc.querySelector(".nv-kc-submit");
        opts.forEach(function(o,oi){ var want=o.dataset.correct==="1", got=sel.indexOf(oi)>=0;
          o.setAttribute("aria-pressed", got?"true":"false");
          if(!silent){
            if(want) o.classList.add("correct");               // always show the correct answers
            else if(got) o.classList.add("incorrect");         // a wrong pick the learner made
          }
          o.classList.add("is-disabled"); o.disabled=true; if(!silent) srMarkOpt(o); });
        if(submit) submit.disabled=true;
        if(!silent && fb){ var m = ok?fb.getAttribute("data-fb-correct"):fb.getAttribute("data-fb-incorrect");
          fb.innerHTML='<span class="nv-sr-only">'+(ok?"Correct. ":"Incorrect. ")+'</span>'+(ok?(m||""):("Not quite."+(m?" "+m:""))); fb.classList.remove("ok","no"); fb.classList.add("show", ok?"ok":"no"); }  // A7: visible negative lead-in on terminal-incorrect
        kcSeen[i]={opt:sel.join(","),ok:ok,multi:1}; loc={t:"kc",i:i}; }

      /* Modals */
      var modals = {}, lastFocus = null;
      var FOCUSABLE = 'a[href], button:not([disabled]), input:not([disabled]), select:not([disabled]), textarea:not([disabled]), video, audio, iframe, [tabindex]:not([tabindex="-1"])';
      Array.prototype.slice.call(document.querySelectorAll(".nv-modal")).forEach(function(m){ modals[m.id]=m; });
      // inert + aria-hidden the page chrome behind an open dialog so AT/Tab can't reach it
      function setInert(el, on){ if(!el)return; if(on){ el.setAttribute("inert",""); el.setAttribute("aria-hidden","true"); } else { el.removeAttribute("inert"); el.removeAttribute("aria-hidden"); } }
      function bgInert(modal, on){
        setInert(document.querySelector(".nv-topbar"), on);
        var main=document.querySelector(".nv-main"); if(!main)return;
        Array.prototype.slice.call(main.children).forEach(function(ch){ if(ch!==modal) setInert(ch, on); });
      }
      function openModal(id){ var m=modals[id]; if(!m)return; lastFocus=document.activeElement; m.hidden=false; document.body.classList.add("nv-modal-open"); bgInert(m, true); var c=m.querySelector(".nv-modal-close"); if(c)c.focus(); }
      function closeModal(m){ if(!m||m.hidden)return; m.hidden=true; bgInert(m, false); if(!document.querySelector(".nv-modal:not([hidden])"))document.body.classList.remove("nv-modal-open");
        var av=m.querySelector("video, audio"); if(av){try{av.pause();}catch(e){}} if(lastFocus){try{lastFocus.focus();}catch(e){}} }
      Array.prototype.slice.call(document.querySelectorAll("[data-modal]")).forEach(function(t){ t.addEventListener("click", function(){ var id=t.getAttribute("data-modal"); openModal(id); if(t.getAttribute("data-require-open")==="1"){ openSeen[id]=true; updateProgress(); } }); });
      Object.keys(modals).forEach(function(id){ var m=modals[id]; m.addEventListener("click", function(e){ if(e.target===m)closeModal(m); });
        var c=m.querySelector(".nv-modal-close"); if(c)c.addEventListener("click", function(){ closeModal(m); });
        m.addEventListener("keydown", function(e){ if(e.key!=="Tab")return;
          var f=Array.prototype.slice.call(m.querySelectorAll(FOCUSABLE)).filter(function(el){ return el.offsetParent!==null || el===document.activeElement; });
          if(!f.length)return; var first=f[0],last=f[f.length-1];
          if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();} else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();} }); });
      document.addEventListener("keydown", function(e){ if(e.key==="Escape")closeModal(document.querySelector(".nv-modal:not([hidden])")); });

      setupContinueGates();
      media.forEach(function(el,i){ el.addEventListener("ended", function(){ mediaSeen["m"+i]=true; updateProgress(); }); });
      gates.forEach(function(gate,i){ var b=gate.querySelector(".nv-btn"); if(!b)return; b.addEventListener("click", function(){ var r=passGate(gate,i); updateProgress(); (r||gate).scrollIntoView({behavior:"smooth",block:"start"}); if(r){ try{ r.focus(); }catch(e){} } }); });
      kcs.forEach(function(kc,i){ var opts=Array.prototype.slice.call(kc.querySelectorAll(".nv-kc-opt")), fb=kc.querySelector(".nv-kc-fb");
        if (kc.classList.contains("nv-kc--multi")){                               // multi-select: toggle + submit
          var submit = kc.querySelector(".nv-kc-submit");
          opts.forEach(function(opt){ opt.addEventListener("click", function(){
            if (kcSeen[i]) return;                                                // locked
            var on = opt.getAttribute("aria-pressed")==="true";
            opt.setAttribute("aria-pressed", on?"false":"true"); opt.classList.toggle("is-selected", !on);
          }); });
          if (submit && DEFERRED) submit.hidden = true;    // deferred: no per-item submit; the section "Submit section" scores it
          else if (submit) submit.addEventListener("click", function(){
            if (kcSeen[i]) return;
            var sel=[]; opts.forEach(function(o,oi){ if(o.getAttribute("aria-pressed")==="true") sel.push(oi); });
            if (!sel.length){                                                     // empty submit: prompt politely, don't silently no-op
              if (fb){ fb.textContent="Select at least one option, then choose Submit."; fb.classList.remove("ok","no"); fb.classList.add("show"); }
              return; }
            kcTries[i] = (kcTries[i]||0) + 1;
            var ok = multiAllCorrect(opts.map(function(o){ return o.dataset.correct==="1"; }), sel);
            if (kcLocks(ok, kcTries[i], maxTries)) { lockKcMulti(kc,i,sel,ok); updateProgress(); }
            else {                                                                // retry: keep picks, prompt again
              if (fb){ var left = maxTries - kcTries[i];
                fb.innerHTML = '<span class="nv-sr-only">Incorrect. </span>' +
                  (fb.getAttribute("data-fb-incorrect") || "Not quite.") +
                  ' <em class="nv-kc-retry">Try again — ' + left + ' attempt' + (left===1?'':'s') + ' left.</em>';
                fb.classList.remove("ok"); fb.classList.add("show","no"); }
            }
          });
          return;
        }
        opts.forEach(function(opt,oi){ opt.addEventListener("click", function(){
          if (kcSeen[i] || opt.classList.contains("is-disabled")) return;        // terminal, or an eliminated wrong choice
          if (DEFERRED){                                                          // changeable single pick; scored at Submit section
            opts.forEach(function(o){ o.classList.remove("is-selected"); o.setAttribute("aria-pressed","false"); });
            opt.classList.add("is-selected"); opt.setAttribute("aria-pressed","true"); return;
          }
          kcTries[i] = (kcTries[i]||0) + 1;
          var ok = opt.dataset.correct === "1";
          if (kcLocks(ok, kcTries[i], maxTries)) { lockKc(kc,i,oi,ok); updateProgress(); }   // terminal
          else {                                                                  // retry: eliminate this choice, prompt again
            opt.classList.add("incorrect","is-disabled"); opt.disabled=true; srMarkOpt(opt);
            if (fb){ var left = maxTries - kcTries[i];
              fb.innerHTML = '<span class="nv-sr-only">Incorrect. </span>' +
                (fb.getAttribute("data-fb-incorrect") || "Not quite.") +
                ' <em class="nv-kc-retry">Try again — ' + left + ' attempt' + (left===1?'':'s') + ' left.</em>';
              fb.classList.remove("ok"); fb.classList.add("show","no"); }
          }
        }); }); });

      /* Flashcards — flip toggles aria-pressed (button => Enter/Space free); non-gating.
         The off-screen face is aria-hidden so AT never reads the answer before the flip. */
      flips.forEach(function(fc){ var front=fc.querySelector(".nv-flip-front"), back=fc.querySelector(".nv-flip-back");
        if(back) back.setAttribute("aria-hidden","true");
        fc.addEventListener("click", function(){
          var flipped = fc.getAttribute("aria-pressed")!=="true";
          fc.setAttribute("aria-pressed", flipped ? "true" : "false");
          if(front) front.setAttribute("aria-hidden", flipped ? "true" : "false");
          if(back)  back.setAttribute("aria-hidden", flipped ? "false" : "true");
        }); });

      /* Tabs — same content model as accordion, but one panel visible at a time.
         Arrow/Home/End navigation follows the ARIA tab pattern; non-gating. */
      tabsets.forEach(function(tabs){
        var btns = Array.prototype.slice.call(tabs.querySelectorAll('[role="tab"]'));
        var panels = Array.prototype.slice.call(tabs.querySelectorAll('[role="tabpanel"]'));
        function show(idx, focus){
          btns.forEach(function(btn, i){
            var on = i === idx;
            btn.setAttribute("aria-selected", on ? "true" : "false");
            btn.tabIndex = on ? 0 : -1;
            if (panels[i]) panels[i].hidden = !on;
          });
          if (focus && btns[idx]) btns[idx].focus();
        }
        btns.forEach(function(btn, idx){
          btn.addEventListener("click", function(){ show(idx, false); });
          btn.addEventListener("keydown", function(e){
            var next = idx;
            if (e.key === "ArrowRight" || e.key === "ArrowDown") next = (idx + 1) % btns.length;
            else if (e.key === "ArrowLeft" || e.key === "ArrowUp") next = (idx + btns.length - 1) % btns.length;
            else if (e.key === "Home") next = 0;
            else if (e.key === "End") next = btns.length - 1;
            else if (e.key === " " || e.key === "Enter") { e.preventDefault(); show(idx, false); return; }
            if (next !== idx) { e.preventDefault(); show(next, true); }
          });
        });
      });

      /* Branching scenarios (M14) — one scene at a time; a choice reveals its feedback,
         then Continue routes to the choice's `data-goto` target scene. A scenario with
         NO targets renders static (no [data-branching]) and is never touched here, so
         linear scenarios keep working. Self-contained: not wired into completion (same
         as the linear scenario, which never gated progress either). */
      Array.prototype.slice.call(document.querySelectorAll(".nv-scenario[data-branching]")).forEach(function(scn){
        var scenes = Array.prototype.slice.call(scn.querySelectorAll(".nv-scn-scene"));
        var sceneIds = scenes.map(function(s){ return s.getAttribute("data-scene-id"); });
        var restart = scn.querySelector(".nv-scn-restart");
        function show(idx){
          scenes.forEach(function(s,i){ s.hidden = (i !== idx); });
          var cur = scenes[idx]; if (!cur) return;
          Array.prototype.slice.call(cur.querySelectorAll(".nv-scn-choice")).forEach(function(b){ b.disabled=false; b.parentNode.classList.remove("is-picked"); });
          Array.prototype.slice.call(cur.querySelectorAll(".nv-scn-fb")).forEach(function(f){ f.hidden=true; });
          var nav = cur.querySelector(".nv-scn-nav"); if (nav) nav.hidden=true;
          cur.scrollIntoView({behavior:"smooth", block:"nearest"});
          try{ cur.focus(); }catch(e){}
        }
        scenes.forEach(function(scene){
          var choices = Array.prototype.slice.call(scene.querySelectorAll(".nv-scn-choice"));
          var nav = scene.querySelector(".nv-scn-nav");
          var contBtn = nav ? nav.querySelector(".nv-scn-continue") : null;
          choices.forEach(function(btn){
            btn.addEventListener("click", function(){
              if (btn.disabled) return;
              choices.forEach(function(o){ o.disabled=true; o.parentNode.classList.remove("is-picked"); });
              btn.parentNode.classList.add("is-picked");
              var fb = btn.parentNode.querySelector(".nv-scn-fb"); if (fb) fb.hidden=false;
              if (restart) restart.hidden=false;             // now that they've started, allow a reset
              var target = resolveScene(btn.getAttribute("data-goto"), sceneIds);
              if (nav && contBtn && target >= 0){            // an onward scene: offer Continue
                nav.hidden=false;
                contBtn.onclick = function(){ show(target); };
              } else if (nav){                               // an ending: no onward scene
                nav.hidden=true;
              }
            });
          });
        });
        if (restart) restart.addEventListener("click", function(){ show(0); });
        // start on the first scene (render emits every scene `hidden`).
        scenes.forEach(function(s,i){ s.hidden = (i !== 0); });
        if (restart) restart.hidden=true;
      });

      /* Categorize / sorting — Check validates each select against its target, then locks + folds into completion */
      // Slice B (instant mode) — score a block's CURRENT answer WITHOUT locking, so a wrong Check
      // can retry. Each mirrors its lock's grading exactly (same DOM reads). Returns {ok,got,max}.
      function gradeSort(sort){
        var items = Array.prototype.slice.call(sort.querySelectorAll(".nv-sort-item"));
        var got = 0; items.forEach(function(li){ var p=li.querySelector(".nv-sort-pick"); if(p && p.value!=="" && p.value===li.getAttribute("data-target")) got++; });
        return { got: got, max: items.length, ok: items.length>0 && got===items.length };
      }
      function gradeMatch(el){ var items = Array.prototype.slice.call(el.querySelectorAll(".nv-match-item"));
        return tallyExact(items.map(function(li){ var p=li.querySelector(".nv-match-pick"); return p?p.value:""; }), items.map(function(li){ return li.getAttribute("data-answer"); })); }
      function gradeSeq(el){ var items = Array.prototype.slice.call(el.querySelectorAll(".nv-seq-item"));
        return tallyExact(items.map(function(li){ var p=li.querySelector(".nv-seq-pick"); return p?p.value:""; }), items.map(function(li){ return li.getAttribute("data-pos"); })); }
      function gradeFill(el){ var items = Array.prototype.slice.call(el.querySelectorAll(".nv-fill-item"));
        return fillScore(items.map(function(li){ var inp=li.querySelector(".nv-fill-input"); return inp?inp.value:""; }), items.map(fillAnswers)); }
      function gradeDrag(el){ var items = Array.prototype.slice.call(el.querySelectorAll(".nv-drag-item"));
        return tallyExact(items.map(function(li){ var p=li.querySelector(".nv-drag-pick"); return p?p.value:""; }), items.map(function(li){ return li.getAttribute("data-target"); })); }
      function gradeHotspot(el){ var spotsEls = Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot"));
        var sel = []; spotsEls.forEach(function(sp,n){ if (sp.getAttribute("aria-pressed")==="true") sel.push(n); });
        return scoreHotspot(spotsEls.map(function(sp){ return sp.getAttribute("data-correct")==="1"; }), sel); }
      // True when this Check attempt is TERMINAL (lock + reveal): correct, or non-instant one-shot,
      // or the learner just used their last instant attempt. Mirrors kcLocks — interactive retry is
      // an INSTANT-mode behavior (a plain *Retry:* alone leaves interactive blocks one-shot).
      function interactiveLocks(ok, tries){ return kcLocks(ok, tries, INSTANT ? maxTries : 0); }
      // Instant-mode retry nudge: the tally (no per-row reveal — that would give away the answer) +
      // attempts remaining. Does NOT lock; inputs stay editable for the next attempt.
      function showInteractiveRetry(fb, tally, left){
        if (!fb) return;
        fb.innerHTML = '<span class="nv-sr-only">Incorrect. </span>' + (tally||"") +
          '<em class="nv-kc-retry">Try again — ' + left + ' attempt' + (left===1?'':'s') + ' left.</em>';
        fb.classList.remove("ok"); fb.classList.add("show","no");
      }
      // Instant-mode terminal reveal (decision #1: "visibly mark correct pair/position"). On the
      // final wrong attempt, append the correct answer to each MISSED row. Gated to instant via the
      // lock's `reveal` flag, so classic one-shot terminals stay behavior-identical. Idempotent.
      function optText(sel, val){ var t = val; if (sel) Array.prototype.slice.call(sel.options).forEach(function(o){ if (o.value === val) t = o.textContent; }); return t; }
      function revealHint(li, text){
        if (!li || li.querySelector(".nv-ans-reveal")) return;
        var tag = document.createElement("span"); tag.className = "nv-ans-reveal";
        tag.textContent = "Correct: " + text;   // self-describing for both sighted + SR users
        li.appendChild(tag);
      }
      // `silent` (deferred mode) → grade + record + lock the inputs, but SUPPRESS the per-row
      // correct/incorrect reveal and the feedback line (feedback is held to the end-of-course review).
      function lockSort(sort, i, silent, reveal){
        var items = Array.prototype.slice.call(sort.querySelectorAll(".nv-sort-item"));
        var allOk = true, got = 0;
        items.forEach(function(li){
          var pick = li.querySelector(".nv-sort-pick");
          // An unanswered item (empty value) is always wrong — never let "" === "" (an
          // item authored with no target) auto-pass an untouched select.
          var ok = pick && pick.value !== "" && pick.value === li.getAttribute("data-target");
          li.classList.remove("correct","incorrect");
          if (silent){ li.classList.add("is-locked"); if (pick) pick.disabled = true; }
          else { li.classList.add(ok ? "correct" : "incorrect", "is-locked");
            if (reveal && !ok) revealHint(li, optText(pick, li.getAttribute("data-target"))); }
          if (ok) got++; else allOk = false;   // Slice C — per-item tally for partial credit
        });
        if (!silent){ var fb = sort.querySelector(".nv-sort-fb");
          if (fb){ var m = allOk ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
            fb.innerHTML = '<span class="nv-sr-only">'+(allOk?"Correct. ":"Incorrect. ")+'</span>'+
              (m || (allOk ? "Correct!" : "Some items aren't in the right category.")); fb.classList.remove("ok","no"); fb.classList.add("show", allOk ? "ok" : "no"); } }
        var btn = sort.querySelector(".nv-sort-check"); if (btn) btn.disabled = true;
        sortSeen["s"+i] = { ok: allOk, got: got, max: items.length, picks: items.map(function(li){ var p=li.querySelector(".nv-sort-pick"); return p?p.value:""; }) };
        loc = { t:"s", i:i };
      }
      // Restore a completed sort WITHOUT re-grading from the DOM — used when suspend_data
      // was degraded (picks dropped to fit the 1.2 budget) so we can't recompute, but the
      // saved `ok` keeps completion + pass/fail intact.
      function markSortDone(sort, i, rec){
        var ok = !!rec.ok;
        var fb = sort.querySelector(".nv-sort-fb");
        if (fb){ var m = ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
          fb.innerHTML = '<span class="nv-sr-only">'+(ok?"Correct. ":"Incorrect. ")+'</span>'+
            (m || (ok ? "Correct!" : "Some items aren't in the right category.")); fb.classList.remove("ok","no"); fb.classList.add("show", ok ? "ok" : "no"); }
        var btn = sort.querySelector(".nv-sort-check"); if (btn) btn.disabled = true;
        sortSeen["s"+i] = { ok: ok, got: rec.got, max: rec.max };   // Slice C — keep partial-credit got/max on degraded resume
      }
      // categorize renders drag-first (`nv-sort--nomenus`), and until S344 NOTHING in this
      // file implemented it: the zones, the draggable items and the "Show placement menus"
      // toggle were all dead markup, and the hint told the learner to drag. Same layer as
      // dragDrop, second call — see wirePlacement.
      sorts.forEach(function(el,i){
        wirePlacement(el, { prefix: "sort", zoneAttr: "data-sort-zone",
                            locked: function(){ return !!sortSeen["s"+i]; } });
      });
      sorts.forEach(function(sort,i){ var btn = sort.querySelector(".nv-sort-check"); var tries = 0;
        if (btn && DEFERRED) btn.hidden = true;   // deferred: scored at Submit section, not per item
        else if (btn) btn.addEventListener("click", function(){ if (sortSeen["s"+i]) return;
          tries++; var res = gradeSort(sort);
          if (interactiveLocks(res.ok, tries)) { lockSort(sort,i,false,INSTANT); updateProgress(); }   // terminal → reveal
          else showInteractiveRetry(sort.querySelector(".nv-sort-fb"), "You placed "+res.got+" of "+res.max+" correctly. ", maxTries - tries);
        }); });

      // A3/A4 — one-to-one pickers can't reuse a value. After any change, disable each
      // already-chosen option in the OTHER selects of the block (never the empty placeholder,
      // never the option currently selected in that same select). Sequence is always 1:1;
      // matching opts in only when render tagged it data-unique (distinct right-side values).
      function enforceUniquePicks(block, sel){
        var picks = Array.prototype.slice.call(block.querySelectorAll(sel));
        function refresh(){
          var taken = {};
          picks.forEach(function(p){ if (p.value) taken[p.value] = true; });
          picks.forEach(function(p){
            Array.prototype.slice.call(p.options).forEach(function(o){
              if (o.value === "") return;                       // keep the "Choose…"/"#" placeholder
              o.disabled = !!taken[o.value] && o.value !== p.value;
            });
          });
        }
        picks.forEach(function(p){ p.addEventListener("change", refresh); });
        refresh();
      }

      // M12 — matching: PARTIAL-credit scoring. Each row's pick must equal its data-answer.
      function showMatchFb(el, res){
        var fb = el.querySelector(".nv-match-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got!=null && res.max!=null) ? ("You matched "+res.got+" of "+res.max+" correctly. ") : "";
        fb.innerHTML = '<span class="nv-sr-only">'+(res.ok?"Correct. ":"Incorrect. ")+'</span>'+
          tally + (msg || (res.ok ? "All matched!" : "Some matches aren't right."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function lockMatch(el, i, silent, reveal){
        var items = Array.prototype.slice.call(el.querySelectorAll(".nv-match-item"));
        var picks = items.map(function(li){ var p=li.querySelector(".nv-match-pick"); return p?p.value:""; });
        var answers = items.map(function(li){ return li.getAttribute("data-answer"); });
        var res = tallyExact(picks, answers);
        items.forEach(function(li,n){
          var okOne = picks[n] !== "" && picks[n] === answers[n];
          li.classList.remove("correct","incorrect");
          if (silent){ li.classList.add("is-locked"); var p=li.querySelector(".nv-match-pick"); if(p) p.disabled = true; }
          else { li.classList.add(okOne ? "correct" : "incorrect", "is-locked");
            if (reveal && !okOne) revealHint(li, optText(li.querySelector(".nv-match-pick"), answers[n])); }
        });
        if (!silent) showMatchFb(el, res);
        var btn = el.querySelector(".nv-match-check"); if (btn) btn.disabled = true;
        matchSeen["mt"+i] = { ok: res.ok, got: res.got, max: res.max, picks: picks };
        loc = { t:"mt", i:i };
      }
      // Restore a completed match without re-grading (picks dropped to fit suspend_data).
      function markMatchDone(el, i, rec){
        showMatchFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        var btn = el.querySelector(".nv-match-check"); if (btn) btn.disabled = true;
        matchSeen["mt"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      matches.forEach(function(el,i){ var btn = el.querySelector(".nv-match-check"); var tries = 0;
        if (el.getAttribute("data-unique") === "1") enforceUniquePicks(el, ".nv-match-pick");  // A4 — 1:1 only
        if (btn && DEFERRED) btn.hidden = true;   // deferred: scored at Submit section
        else if (btn) btn.addEventListener("click", function(){ if (matchSeen["mt"+i]) return;
          tries++; var res = gradeMatch(el);
          if (interactiveLocks(res.ok, tries)) { lockMatch(el,i,false,INSTANT); updateProgress(); }   // terminal → reveal
          else showInteractiveRetry(el.querySelector(".nv-match-fb"), "You matched "+res.got+" of "+res.max+" correctly. ", maxTries - tries);
        }); });

      // M12 — sequencing: PARTIAL-credit scoring. Each step's picked position must equal data-pos.
      function showSeqFb(el, res){
        var fb = el.querySelector(".nv-seq-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got!=null && res.max!=null) ? ("You placed "+res.got+" of "+res.max+" correctly. ") : "";
        fb.innerHTML = '<span class="nv-sr-only">'+(res.ok?"Correct. ":"Incorrect. ")+'</span>'+
          tally + (msg || (res.ok ? "Correct order!" : "Some steps aren't in the right place."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function lockSeq(el, i, silent, reveal){
        var items = Array.prototype.slice.call(el.querySelectorAll(".nv-seq-item"));
        var picks = items.map(function(li){ var p=li.querySelector(".nv-seq-pick"); return p?p.value:""; });
        var answers = items.map(function(li){ return li.getAttribute("data-pos"); });
        var res = tallyExact(picks, answers);
        items.forEach(function(li,n){
          var okOne = picks[n] !== "" && picks[n] === answers[n];
          li.classList.remove("correct","incorrect");
          if (silent){ li.classList.add("is-locked"); var p=li.querySelector(".nv-seq-pick"); if(p) p.disabled = true; }
          else { li.classList.add(okOne ? "correct" : "incorrect", "is-locked");
            if (reveal && !okOne) revealHint(li, "position " + answers[n]); }
        });
        if (!silent) showSeqFb(el, res);
        var btn = el.querySelector(".nv-seq-check"); if (btn) btn.disabled = true;
        seqSeen["sq"+i] = { ok: res.ok, got: res.got, max: res.max, picks: picks };
        loc = { t:"sq", i:i };
      }
      function markSeqDone(el, i, rec){
        showSeqFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        var btn = el.querySelector(".nv-seq-check"); if (btn) btn.disabled = true;
        seqSeen["sq"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      sequences.forEach(function(el,i){ var btn = el.querySelector(".nv-seq-check"); var tries = 0;
        enforceUniquePicks(el, ".nv-seq-pick");  // A3 — sequence positions are always 1:1
        if (btn && DEFERRED) btn.hidden = true;   // deferred: scored at Submit section
        else if (btn) btn.addEventListener("click", function(){ if (seqSeen["sq"+i]) return;
          tries++; var res = gradeSeq(el);
          if (interactiveLocks(res.ok, tries)) { lockSeq(el,i,false,INSTANT); updateProgress(); }   // terminal → reveal
          else showInteractiveRetry(el.querySelector(".nv-seq-fb"), "You placed "+res.got+" of "+res.max+" correctly. ", maxTries - tries);
        }); });

      // M12 — fill-in-the-blank: PARTIAL-credit, LENIENT accept-list matching (normFill).
      function fillAnswers(li){ try { return JSON.parse(li.getAttribute("data-answers") || "[]") || []; } catch(e){ return []; } }
      function showFillFb(el, res){
        var fb = el.querySelector(".nv-fill-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got!=null && res.max!=null) ? ("You answered "+res.got+" of "+res.max+" correctly. ") : "";
        fb.innerHTML = '<span class="nv-sr-only">'+(res.ok?"Correct. ":"Incorrect. ")+'</span>'+
          tally + (msg || (res.ok ? "All correct!" : "Some blanks aren't right."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function lockFill(el, i, silent, reveal){
        var items = Array.prototype.slice.call(el.querySelectorAll(".nv-fill-item"));
        var inputs = items.map(function(li){ var inp=li.querySelector(".nv-fill-input"); return inp?inp.value:""; });
        var answerSets = items.map(fillAnswers);
        var res = fillScore(inputs, answerSets);
        items.forEach(function(li,n){
          var got_in = normFill(inputs[n]);
          var okOne = got_in !== "" && answerSets[n].map(normFill).indexOf(got_in) >= 0;
          li.classList.remove("correct","incorrect");
          if (silent) li.classList.add("is-locked");
          else { li.classList.add(okOne ? "correct" : "incorrect", "is-locked");
            if (reveal && !okOne) revealHint(li, (answerSets[n] && answerSets[n][0]) || ""); }
          var inp=li.querySelector(".nv-fill-input"); if(inp) inp.disabled = true;
        });
        if (!silent) showFillFb(el, res);
        var btn = el.querySelector(".nv-fill-check"); if (btn) btn.disabled = true;
        fillSeen["fl"+i] = { ok: res.ok, got: res.got, max: res.max, inputs: inputs };
        loc = { t:"fl", i:i };
      }
      function markFillDone(el, i, rec){
        showFillFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        Array.prototype.slice.call(el.querySelectorAll(".nv-fill-input")).forEach(function(inp){ inp.disabled = true; });
        var btn = el.querySelector(".nv-fill-check"); if (btn) btn.disabled = true;
        fillSeen["fl"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      fills.forEach(function(el,i){ var btn = el.querySelector(".nv-fill-check"); var tries = 0;
        if (btn && DEFERRED) btn.hidden = true;   // deferred: scored at Submit section
        else if (btn) btn.addEventListener("click", function(){ if (fillSeen["fl"+i]) return;
          tries++; var res = gradeFill(el);
          if (interactiveLocks(res.ok, tries)) { lockFill(el,i,false,INSTANT); updateProgress(); }   // terminal → reveal
          else showInteractiveRetry(el.querySelector(".nv-fill-fb"), "You answered "+res.got+" of "+res.max+" correctly. ", maxTries - tries);
        }); });

      /* dragDrop — PARTIAL-credit like matching. The per-label <select> is the source of
         truth (keyboard + touch accessible); native pointer drag just sets it. Each label
         placed in its correct zone (pick === data-target) scores 1 of N. */
      function showDragFb(el, res){
        var fb = el.querySelector(".nv-drag-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got!=null && res.max!=null) ? ("You placed "+res.got+" of "+res.max+" correctly. ") : "";
        fb.innerHTML = '<span class="nv-sr-only">'+(res.ok?"Correct. ":"Incorrect. ")+'</span>'+
          tally + (msg || (res.ok ? "All placed!" : "Some labels aren't on the right target."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function lockDrag(el, i, silent, reveal){
        var items = Array.prototype.slice.call(el.querySelectorAll(".nv-drag-item"));
        var picks = items.map(function(li){ var p=li.querySelector(".nv-drag-pick"); return p?p.value:""; });
        var answers = items.map(function(li){ return li.getAttribute("data-target"); });
        var res = tallyExact(picks, answers);
        items.forEach(function(li,n){
          var okOne = picks[n] !== "" && picks[n] === answers[n];
          li.classList.remove("correct","incorrect");
          if (silent) li.classList.add("is-locked");
          else { li.classList.add(okOne ? "correct" : "incorrect", "is-locked");
            if (reveal && !okOne) revealHint(li, optText(li.querySelector(".nv-drag-pick"), answers[n])); }
          li.setAttribute("draggable","false");
          var p=li.querySelector(".nv-drag-pick"); if(p) p.disabled = true;
        });
        if (!silent) showDragFb(el, res);
        var btn = el.querySelector(".nv-drag-check"); if (btn) btn.disabled = true;
        dragSeen["dd"+i] = { ok: res.ok, got: res.got, max: res.max, picks: picks };
        loc = { t:"dd", i:i };
      }
      // Restore a completed dragDrop without re-grading (picks dropped to fit suspend_data).
      function markDragDone(el, i, rec){
        showDragFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        Array.prototype.slice.call(el.querySelectorAll(".nv-drag-pick")).forEach(function(p){ p.disabled = true; });
        var btn = el.querySelector(".nv-drag-check"); if (btn) btn.disabled = true;
        dragSeen["dd"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      // hotspot — click the correct region(s) of the image, then Check. Set-match with
      // PARTIAL credit (scoreHotspot); each spot the learner classifies right = 1 of N.
      function showHotspotFb(el, res){
        var fb = el.querySelector(".nv-hotspot-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got!=null && res.max!=null) ? ("You found "+res.got+" of "+res.max+" correct area"+(res.max===1?"":"s")+". ") : "";
        fb.innerHTML = '<span class="nv-sr-only">'+(res.ok?"Correct. ":"Incorrect. ")+'</span>'+
          tally + (msg || (res.ok ? "All correct areas found!" : "That isn't the right set of areas."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function lockHotspot(el, i, silent){
        var spotsEls = Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot"));
        var corrects = spotsEls.map(function(sp){ return sp.getAttribute("data-correct")==="1"; });
        var sel = []; spotsEls.forEach(function(sp,n){ if (sp.getAttribute("aria-pressed")==="true") sel.push(n); });
        var res = scoreHotspot(corrects, sel);
        spotsEls.forEach(function(sp,n){
          var pressed = sp.getAttribute("aria-pressed")==="true";
          var okOne = pressed === corrects[n];   // right whether it SHOULD or SHOULDN'T be clicked
          sp.classList.remove("correct","incorrect");
          if (silent) sp.classList.add("is-locked");
          else { sp.classList.add(okOne ? "correct" : "incorrect", "is-locked");
            if (corrects[n]) sp.classList.add("is-target"); }   // reveal the target areas (suppressed until review in deferred)
          sp.disabled = true;
        });
        if (!silent) showHotspotFb(el, res);
        var btn = el.querySelector(".nv-hotspot-check"); if (btn) btn.disabled = true;
        hotSeen["ht"+i] = { ok: res.ok, got: res.got, max: res.max, sel: sel };
        loc = { t:"ht", i:i };
      }
      // Restore a completed hotspot without re-grading (selection dropped under byte pressure).
      function markHotspotDone(el, i, rec){
        showHotspotFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot")).forEach(function(sp){ sp.disabled = true; if (sp.getAttribute("data-correct")==="1") sp.classList.add("is-target"); });
        var btn = el.querySelector(".nv-hotspot-check"); if (btn) btn.disabled = true;
        hotSeen["ht"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      /* ---------------- Placement layer — ONE implementation, TWO blocks ----------------
         dragDrop and categorize are the SAME mechanic over different class prefixes: chips
         whose <select> is the source of truth, mirrored into drop zones, with a "Show
         placement menus" toggle as the keyboard/AT path. It is wired once here and called
         twice below rather than implemented twice (James, S344: categorize "duplicates
         something that already exists in the current form of our app" — and origin/main
         carries a second, separate implementation for exactly this, which is what we are
         NOT taking).

         ⚠ Grading is deliberately OUTSIDE this layer. gradeDrag()/gradeSort() still read the
         <select> values, so placement can change without touching a graded path. The layer
         only ever sets a select's value and mirrors it visually. */
      function wirePlacement(el, cfg){
        var p = cfg.prefix;                       // "drag" | "sort"
        var zoneAttr = cfg.zoneAttr;              // dragDrop: data-zone · categorize: data-sort-zone
        var locked = cfg.locked;                  // () => is this block already graded/locked?
        var itemSel = ".nv-" + p + "-item", pickSel = ".nv-" + p + "-pick";
        var zoneSel = ".nv-" + p + "-zone", slotSel = ".nv-" + p + "-slot";
        var labelSel = ".nv-" + p + "-label";
        var placedCls = "nv-" + p + "-placed", filledCls = "nv-" + p + "-filled";
        var overCls = "nv-" + p + "-over", nomenusCls = "nv-" + p + "--nomenus";

        // Reflect a label's chosen zone into the zones view (visual only; the <select> stays
        // authoritative). Moves the chip's mirror into the target zone's slot.
        function placeChip(li, zid){
          var zones = Array.prototype.slice.call(el.querySelectorAll(zoneSel));
          zones.forEach(function(z){
            var slot = z.querySelector(slotSel); if(!slot) return;
            var mine = slot.querySelector('[data-for="'+li.getAttribute("data-cid")+'"]');
            if (mine && z.getAttribute(zoneAttr) !== zid) { slot.removeChild(mine); if(!slot.querySelector("."+placedCls)) z.classList.remove(filledCls); }
          });
          // recolor the source chip so PLACED labels are visually distinct from ones still to place
          li.classList.toggle("is-placed", !!zid);
          if (!zid) return;
          var zone = el.querySelector(zoneSel+'['+zoneAttr+'="'+zid+'"]'); if(!zone) return;
          var slot = zone.querySelector(slotSel); if(!slot) return;
          if (!slot.querySelector('[data-for="'+li.getAttribute("data-cid")+'"]')){
            var tag = document.createElement("button");
            tag.type = "button";
            tag.className = placedCls; tag.setAttribute("data-for", li.getAttribute("data-cid"));
            tag.title = "Click to take this back"; tag.setAttribute("aria-label", "Remove "+((li.querySelector(labelSel)||{}).textContent||"")+" from this target");
            tag.innerHTML = '<span class="'+placedCls+'-txt"></span><span class="'+placedCls+'-x" aria-hidden="true">\u00d7</span>';
            tag.querySelector("."+placedCls+"-txt").textContent = (li.querySelector(labelSel)||{}).textContent || "";
            slot.appendChild(tag); zone.classList.add(filledCls);
          }
        }
        // Take a placed label back out of its zone (change of mind) — clears the <select> and
        // the visual mirror + un-dims the source chip. No-op once the block is graded/locked.
        function unplaceChip(cid){
          if (locked()) return;
          var li = el.querySelector(itemSel+'[data-cid="'+cid+'"]'); if(!li) return;
          var pk = li.querySelector(pickSel); if(pk) pk.value = "";
          placeChip(li, "");
        }

        // give each chip a stable id so the visual mirror can track it
        Array.prototype.slice.call(el.querySelectorAll(itemSel)).forEach(function(li,n){ li.setAttribute("data-cid","c"+n); });
        // toggle the per-label placement menus (hidden by default; keyboard/AT path on demand)
        var mtog = el.querySelector(".nv-" + p + "-menus-toggle");
        if (mtog) mtog.addEventListener("click", function(){
          var on = el.classList.toggle(nomenusCls) === false;   // class REMOVED => menus shown
          mtog.setAttribute("aria-pressed", on ? "true" : "false");
          mtog.textContent = on ? "Hide placement menus" : "Show placement menus";
        });
        // click a placed label (in its zone) to take it back — change of mind
        el.addEventListener("click", function(e){
          var tag = e.target.closest ? e.target.closest("."+placedCls) : null;
          if (tag && el.contains(tag)) { e.preventDefault(); unplaceChip(tag.getAttribute("data-for")); }
        });
        // keyboard/touch: the <select> drives placement + the visual mirror
        Array.prototype.slice.call(el.querySelectorAll(itemSel)).forEach(function(li){
          var pk=li.querySelector(pickSel);
          if(pk) pk.addEventListener("change", function(){ if(locked()) return; placeChip(li, pk.value); });
        });
        // pointer drag: dropping a chip on a zone sets that chip's <select> value
        var dragging = null;
        Array.prototype.slice.call(el.querySelectorAll(itemSel)).forEach(function(li){
          li.addEventListener("dragstart", function(e){ if(locked()){ e.preventDefault(); return; } dragging = li; if(e.dataTransfer){ e.dataTransfer.effectAllowed="move"; try{ e.dataTransfer.setData("text/plain", li.getAttribute("data-cid")); }catch(err){} } });
          li.addEventListener("dragend", function(){ dragging = null; Array.prototype.slice.call(el.querySelectorAll(zoneSel)).forEach(function(z){ z.classList.remove(overCls); }); });
        });
        Array.prototype.slice.call(el.querySelectorAll(zoneSel)).forEach(function(z){
          z.addEventListener("dragover", function(e){ if(locked()) return; e.preventDefault(); if(e.dataTransfer) e.dataTransfer.dropEffect="move"; z.classList.add(overCls); });
          z.addEventListener("dragleave", function(){ z.classList.remove(overCls); });
          z.addEventListener("drop", function(e){ if(locked()) return; e.preventDefault(); z.classList.remove(overCls);
            if(!dragging) return; var pk=dragging.querySelector(pickSel); if(pk){ pk.value = z.getAttribute(zoneAttr); placeChip(dragging, pk.value); } });
        });
      }

      drags.forEach(function(el,i){
        wirePlacement(el, { prefix: "drag", zoneAttr: "data-zone",
                            locked: function(){ return !!dragSeen["dd"+i]; } });
        var btn = el.querySelector(".nv-drag-check"); var tries = 0;
        if (btn && DEFERRED) btn.hidden = true;   // deferred: scored at Submit section
        else if (btn) btn.addEventListener("click", function(){ if (dragSeen["dd"+i]) return;
          tries++; var res = gradeDrag(el);
          if (interactiveLocks(res.ok, tries)) { lockDrag(el,i,false,INSTANT); updateProgress(); }   // terminal → reveal
          else showInteractiveRetry(el.querySelector(".nv-drag-fb"), "You placed "+res.got+" of "+res.max+" correctly. ", maxTries - tries);
        });
      });

      /* hotspot — click the correct region(s) of a screenshot. Each spot is a positioned
         <button> toggle (aria-pressed); the Check button scores set-match with partial credit. */
      hotspots.forEach(function(el,i){
        Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot")).forEach(function(sp){
          sp.addEventListener("click", function(){
            if (hotSeen["ht"+i]) return;   // locked after Check
            var on = sp.getAttribute("aria-pressed")==="true";
            sp.setAttribute("aria-pressed", on ? "false" : "true");
            sp.classList.toggle("is-selected", !on);
          });
        });
        var btn = el.querySelector(".nv-hotspot-check"); var tries = 0;
        if (btn && DEFERRED) btn.hidden = true;   // deferred: scored at Submit section
        else if (btn) btn.addEventListener("click", function(){ if (hotSeen["ht"+i]) return;
          tries++; var res = gradeHotspot(el);
          if (interactiveLocks(res.ok, tries)) { lockHotspot(el,i); updateProgress(); }   // terminal → reveal
          else showInteractiveRetry(el.querySelector(".nv-hotspot-fb"), "You found "+res.got+" of "+res.max+" correct area"+(res.max===1?"":"s")+". ", maxTries - tries);
        });
      });

      /* wordSearch — find hidden words in a letter grid. PARTIAL credit (found N of M).
         Two ways to select, both self-contained (no library): drag across a straight run of
         cells (mouse OR touch, via Pointer Events), or click the first letter then the last
         (keyboard-operable — cells are <button>s so Enter fires a click). The player reads the
         letters along the selected line and matches them FORWARD OR REVERSED to a target word;
         placements aren't needed client-side. A Check button locks + scores found/total. */
      function wsScore(found, targets){
        var got = 0; for (var t=0;t<targets.length;t++){ if (found[targets[t]]) got++; }
        return { got: got, max: targets.length, ok: targets.length > 0 && got === targets.length };
      }
      function showWsFb(el, res){
        var fb = el.querySelector(".nv-ws-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got != null && res.max != null) ? ("You found " + res.got + " of " + res.max + ". ") : "";
        fb.innerHTML = '<span class="nv-sr-only">' + (res.ok ? "Correct. " : "Incorrect. ") + '</span>' +
          tally + (msg || (res.ok ? "All found!" : "Some words are still hidden."));
        fb.classList.remove("ok", "no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function markWsWord(el, word){ var li = el.querySelector('.nv-ws-word[data-word="' + word + '"]'); if (li) li.classList.add("found"); }
      function lockWs(el, i, found, targets){
        var res = wsScore(found, targets);
        showWsFb(el, res);
        var btn = el.querySelector(".nv-ws-check"); if (btn) btn.disabled = true;
        wsSeen["ws" + i] = { ok: res.ok, got: res.got, max: res.max, found: Object.keys(found) };
        loc = { t: "ws", i: i };
      }
      // Restore a completed wordSearch without re-grading (the found list may have been dropped
      // to fit suspend_data): re-cross-off whatever found words survived + lock.
      function markWsDone(el, i, rec){
        showWsFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        (rec.found || []).forEach(function(w){ markWsWord(el, w); });
        var btn = el.querySelector(".nv-ws-check"); if (btn) btn.disabled = true;
        wsSeen["ws" + i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      wordsearches.forEach(function(el, i){
        var gridEl = el.querySelector(".nv-ws-grid"); if (!gridEl) return;
        var cellAt = {};
        Array.prototype.slice.call(el.querySelectorAll(".nv-ws-cell")).forEach(function(c){ cellAt[c.getAttribute("data-r") + "," + c.getAttribute("data-c")] = c; });
        var targets = Array.prototype.slice.call(el.querySelectorAll(".nv-ws-word")).map(function(w){ return w.getAttribute("data-word"); });
        var found = {};           // WORD -> true
        var anchor = null;        // {r,c} first endpoint of a click-to-click selection
        var path = [];            // cells in the current tentative line
        var downRC = null, isDrag = false, justDragged = false;

        function rc(cell){ return { r: +cell.getAttribute("data-r"), c: +cell.getAttribute("data-c") }; }
        function clearSel(){ path.forEach(function(c){ c.classList.remove("nv-ws-sel"); }); path = []; }
        function showPath(cells){ clearSel(); path = cells || []; path.forEach(function(c){ c.classList.add("nv-ws-sel"); }); }
        function lineCells(a, b){
          var dr = b.r - a.r, dc = b.c - a.c, adr = Math.abs(dr), adc = Math.abs(dc);
          if (!(dr === 0 || dc === 0 || adr === adc)) return null;   // must be a straight 8-way line
          var len = Math.max(adr, adc) + 1, sr = (dr > 0 ? 1 : (dr < 0 ? -1 : 0)), sc = (dc > 0 ? 1 : (dc < 0 ? -1 : 0)), out = [];
          for (var k = 0; k < len; k++){ var cc = cellAt[(a.r + sr * k) + "," + (a.c + sc * k)]; if (!cc) return null; out.push(cc); }
          return out;
        }
        function evaluate(){
          if (path.length < 2){ clearSel(); return; }
          var str = ""; path.forEach(function(c){ str += c.textContent; });
          var rev = str.split("").reverse().join(""), hit = null;
          for (var t = 0; t < targets.length; t++){ var w = targets[t]; if (!found[w] && (w === str || w === rev)){ hit = w; break; } }
          if (hit){ found[hit] = true; path.forEach(function(c){ c.classList.add("nv-ws-found"); }); markWsWord(el, hit); }
          clearSel();
        }
        function cellUnder(e){
          var t = e.target && e.target.closest ? e.target.closest(".nv-ws-cell") : null;
          if (t) return t;
          var u = document.elementFromPoint(e.clientX, e.clientY);   // during a fast drag
          return u && u.closest ? u.closest(".nv-ws-cell") : null;
        }
        gridEl.addEventListener("pointerdown", function(e){
          if (wsSeen["ws" + i]) return;
          var cell = cellUnder(e); if (!cell) return;
          downRC = rc(cell); isDrag = false; justDragged = false;
        });
        gridEl.addEventListener("pointermove", function(e){
          if (wsSeen["ws" + i] || !downRC) return;
          var cell = cellUnder(e); if (!cell) return;
          var here = rc(cell);
          if (here.r === downRC.r && here.c === downRC.c) return;    // still on the start cell
          isDrag = true;
          showPath(lineCells(downRC, here) || []);
        });
        document.addEventListener("pointerup", function(){
          if (wsSeen["ws" + i] || !downRC) { downRC = null; return; }
          if (isDrag){ evaluate(); justDragged = true; anchor = null; }
          downRC = null; isDrag = false;
        });
        gridEl.addEventListener("pointercancel", function(){ downRC = null; isDrag = false; clearSel(); });
        gridEl.addEventListener("click", function(e){
          if (wsSeen["ws" + i]) return;
          if (justDragged){ justDragged = false; return; }           // swallow the click a mouse drag emits
          var cell = e.target && e.target.closest ? e.target.closest(".nv-ws-cell") : null; if (!cell) return;
          if (!anchor){ anchor = rc(cell); showPath([cell]); return; }
          showPath(lineCells(anchor, rc(cell)) || []); evaluate(); anchor = null;
        });
        var wbtn = el.querySelector(".nv-ws-check");
        if (wbtn) wbtn.addEventListener("click", function(){ if (wsSeen["ws" + i]) return; lockWs(el, i, found, targets); updateProgress(); });
      });

      /* crossword — type answers into a numbered interlocking grid. PARTIAL credit
         (words solved / total). White cells are native <input>s (keyboard/touch), so the
         interaction needs no library; a Check button reads each clue's cells, compares the
         typed letters to the answer, marks each clue solved/unsolved, then locks. */
      function cwInputs(el){ return Array.prototype.slice.call(el.querySelectorAll(".nv-cw-input")); }
      function cwInputAt(el){ var m={}; cwInputs(el).forEach(function(inp){ m[inp.getAttribute("data-r")+","+inp.getAttribute("data-c")]=inp; }); return m; }
      function cwWordSolved(inputMap, clue){
        var cells = (clue.getAttribute("data-cells")||"").split(" "), answer = clue.getAttribute("data-answer")||"", got = "";
        for (var k=0;k<cells.length;k++){ var inp = inputMap[cells[k]]; got += ((inp && inp.value) || "").toUpperCase().replace(/[^A-Z]/g,""); }
        return got.length===answer.length && got===answer;
      }
      function cwScore(el){
        var inputMap = cwInputAt(el), clues = Array.prototype.slice.call(el.querySelectorAll(".nv-cw-clue")), got = 0;
        clues.forEach(function(c){ if (cwWordSolved(inputMap, c)){ got++; } });
        return { got: got, max: clues.length, ok: clues.length>0 && got===clues.length };
      }
      function showCwFb(el, res){
        var fb = el.querySelector(".nv-cw-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got != null && res.max != null) ? ("You solved " + res.got + " of " + res.max + ". ") : "";
        fb.innerHTML = '<span class="nv-sr-only">' + (res.ok ? "Correct. " : "Incorrect. ") + '</span>' +
          tally + (msg || (res.ok ? "All solved!" : "Some answers are still incomplete."));
        fb.classList.remove("ok", "no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      function cwCollect(el){ var m={}; cwInputs(el).forEach(function(inp){ var v=(inp.value||"").toUpperCase().replace(/[^A-Z]/g,""); if(v) m[inp.getAttribute("data-r")+","+inp.getAttribute("data-c")]=v; }); return m; }
      function cwMark(el){
        var inputMap = cwInputAt(el);
        Array.prototype.slice.call(el.querySelectorAll(".nv-cw-clue")).forEach(function(c){
          var ok = cwWordSolved(inputMap, c); c.classList.toggle("solved", ok);
          (c.getAttribute("data-cells")||"").split(" ").forEach(function(rc){ var inp=inputMap[rc]; if(!inp) return;
            if (ok) inp.classList.add("correct");
            else if ((inp.value||"").trim()) inp.classList.add("incorrect"); });
        });
      }
      function lockCw(el, i){
        cwMark(el);
        var res = cwScore(el);
        showCwFb(el, res);
        cwInputs(el).forEach(function(inp){ inp.disabled = true; });
        var btn = el.querySelector(".nv-cw-check"); if (btn) btn.disabled = true;
        cwSeen["cw" + i] = { ok: res.ok, got: res.got, max: res.max, letters: cwCollect(el) };
        loc = { t: "cw", i: i };
      }
      // Restore a completed crossword without re-grading: refill whatever typed letters
      // survived suspend_data (dropped under byte pressure → inputs stay blank), re-mark + lock.
      function markCwDone(el, i, rec){
        var inputMap = cwInputAt(el);
        Object.keys(rec.letters || {}).forEach(function(rc){ var inp=inputMap[rc]; if(inp) inp.value = rec.letters[rc]; });
        if (rec.letters) cwMark(el);
        showCwFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
        cwInputs(el).forEach(function(inp){ inp.disabled = true; });
        var btn = el.querySelector(".nv-cw-check"); if (btn) btn.disabled = true;
        cwSeen["cw" + i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
      }
      crosswords.forEach(function(el, i){
        // Slice D — directional input model (buildCwModel/cwMove ported from crosswords-js).
        // Letter entry advances ALONG the active clue (across=right, DOWN=down), Backspace
        // clears + steps behind, arrows move + switch direction, Enter/re-click toggles at an
        // intersection, and a clue click activates that word — fixing the write-once cells and
        // the across-only advance. The Check button + scoring below are unchanged.
        var inputs = cwInputs(el);
        var byRC = {}; inputs.forEach(function(inp){ byRC[inp.getAttribute("data-r")+","+inp.getAttribute("data-c")] = inp; });
        var clueEls = Array.prototype.slice.call(el.querySelectorAll(".nv-cw-clue"));
        var model = buildCwModel(clueEls.map(function(li){
          return { dir: li.getAttribute("data-dir"), cells: (li.getAttribute("data-cells")||"").split(" ") }; }));
        var curDir = "across";
        function rcOf(inp){ return inp.getAttribute("data-r")+","+inp.getAttribute("data-c"); }
        function defaultDir(rc){ var m=model[rc]||{}; return m[curDir] ? curDir : (m.across ? "across" : (m.down ? "down" : curDir)); }
        function highlight(rc){
          inputs.forEach(function(x){ x.classList.remove("is-active"); if (x.parentNode) x.parentNode.classList.remove("in-clue"); });
          clueEls.forEach(function(li){ li.classList.remove("is-active"); });
          var seg = (model[rc]||{})[curDir];
          if (seg){ var key = seg.cells.join(" ");
            seg.cells.forEach(function(c){ var inp=byRC[c]; if (inp && inp.parentNode) inp.parentNode.classList.add("in-clue"); });
            clueEls.forEach(function(li){ if (li.getAttribute("data-dir")===curDir && (li.getAttribute("data-cells")||"")===key) li.classList.add("is-active"); }); }
          var cur = byRC[rc]; if (cur) cur.classList.add("is-active");
        }
        function goTo(rc){ var inp=byRC[rc]; if (inp){ inp.focus(); try { inp.select(); } catch(e){} highlight(rc); } }
        inputs.forEach(function(inp){
          inp.addEventListener("focus", function(){ curDir = defaultDir(rcOf(inp)); highlight(rcOf(inp)); });
          inp.addEventListener("mousedown", function(){
            var rc=rcOf(inp), m=model[rc]||{};
            if (document.activeElement===inp && m.across && m.down){ curDir = curDir==="across" ? "down" : "across"; highlight(rc); }
          });
          // Empty-cell typing (incl. mobile virtual keyboards) flows through `input`: sanitise,
          // keep the NEWEST char (overtype), then advance along the active clue.
          inp.addEventListener("input", function(){
            if (cwSeen["cw" + i]) return;
            inp.value = (inp.value || "").toUpperCase().replace(/[^A-Z]/g, "").slice(-1);
            inp.classList.remove("correct","incorrect");
            if (inp.value){ var nx = cwMove(model, rcOf(inp), curDir, "ahead"); curDir = nx.dir; goTo(nx.rc); }
          });
          inp.addEventListener("keydown", function(e){
            if (cwSeen["cw" + i]) return;
            var rc = rcOf(inp), k = e.key;
            // Overtype a FILLED cell from a physical keyboard (maxlength=1 would otherwise block
            // it): replace in place + advance. Empty cells fall through to the `input` path above.
            if (/^[a-zA-Z]$/.test(k) && inp.value){ e.preventDefault();
              inp.value = k.toUpperCase(); inp.classList.remove("correct","incorrect");
              var nx = cwMove(model, rc, curDir, "ahead"); curDir = nx.dir; goTo(nx.rc); return; }
            if (k === "Backspace"){ e.preventDefault();
              if (inp.value){ inp.value=""; inp.classList.remove("correct","incorrect"); highlight(rc); }
              else { var b = cwMove(model, rc, curDir, "behind");
                if (b.rc !== rc){ var bi=byRC[b.rc]; if (bi){ bi.value=""; bi.classList.remove("correct","incorrect"); } curDir=b.dir; goTo(b.rc); } } }
            else if (k === "Delete"){ e.preventDefault(); inp.value=""; inp.classList.remove("correct","incorrect"); highlight(rc); }
            else if (k === "Enter"){ e.preventDefault(); var t=cwMove(model, rc, curDir, "toggle"); curDir=t.dir; highlight(rc); }
            else if (k === "ArrowRight" || k === "ArrowLeft" || k === "ArrowUp" || k === "ArrowDown"){ e.preventDefault();
              var act = { ArrowRight:"right", ArrowLeft:"left", ArrowUp:"up", ArrowDown:"down" }[k];
              var mv = cwMove(model, rc, curDir, act); curDir = mv.dir; goTo(mv.rc); }
          });
        });
        // Clicking a clue activates that word (the most intuitive way to start a DOWN answer).
        clueEls.forEach(function(li){
          li.addEventListener("click", function(){ if (cwSeen["cw" + i]) return;
            curDir = li.getAttribute("data-dir") || "across";
            var first = (li.getAttribute("data-cells")||"").split(" ")[0]; if (first) goTo(first); });
        });
        var cbtn = el.querySelector(".nv-cw-check");
        if (cbtn) cbtn.addEventListener("click", function(){ if (cwSeen["cw" + i]) return; lockCw(el, i); updateProgress(); });
      });

      /* gameShow — spin-the-wheel review. Each slice is one MCQ. The learner spins
         (animated wheel + a keyboard/reduced-motion-safe Spin button that lands on the
         next unanswered slice, deterministically — no Math.random), answers the drawn
         question, then spins again. PARTIAL credit (answered N of M correctly). The block
         registers in gsSeen only once EVERY slice is answered — mirroring the single-shot
         game blocks' one-entry-when-done semantics; option order is fixed at build time so
         the correct-answer index (and thus scoring) is resume-stable. */
      function gsScore(marks){       // marks: [bool] one per answered slice
        var got=0; for (var k=0;k<marks.length;k++){ if (marks[k]) got++; }
        return { got: got, max: marks.length, ok: marks.length>0 && got===marks.length };
      }
      function showGsFb(el, res){
        var fb = el.querySelector(".nv-gs-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got != null && res.max != null) ? ("You answered " + res.got + " of " + res.max + " correctly. ") : "";
        fb.innerHTML = '<span class="nv-sr-only">' + (res.ok ? "All correct. " : "Round complete. ") + '</span>' +
          tally + (msg || (res.ok ? "Perfect round!" : "Review the answers above."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      gameshows.forEach(function(el, i){
        var rotor = el.querySelector(".nv-gs-rotor");
        var spinBtn = el.querySelector(".nv-gs-spin");
        var panelWrap = el.querySelector(".nv-gs-panels");
        var panels = Array.prototype.slice.call(el.querySelectorAll(".nv-gs-panel"));
        var segs = Array.prototype.slice.call(el.querySelectorAll(".nv-gs-seg"));
        var n = panels.length, seg = 360/(n||1), turns = 0;
        var answered = {};    // sliceIdx -> ok(bool)
        var current = -1;     // slice currently revealed & awaiting an answer (-1 = none)

        // Unique, panel-scoped radio names → a group is exclusive AND two gameShows can't clash.
        panels.forEach(function(p, qi){
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){ r.name = "gs"+i+"q"+qi; });
        });
        function remaining(){ var out=[]; for (var k=0;k<n;k++){ if (!(k in answered)) out.push(k); } return out; }
        function hidePanels(){ panels.forEach(function(p){ p.hidden = true; }); }
        function markSeg(idx, ok){ if (segs[idx]){ segs[idx].classList.add("nv-gs-done", ok?"nv-gs-ok":"nv-gs-no"); } }
        function pointAt(idx){
          if (!rotor) return;
          turns += 4;                                   // whole extra rotations for the spin effect
          rotor.style.transform = "rotate(" + (turns*360 - (idx+0.5)*seg) + "deg)";   // slice centre → top pointer
        }
        function reveal(idx){
          current = idx; hidePanels();
          var p = panels[idx]; if (!p) return;
          p.hidden = false;
          try { var f = p.querySelector('input[type="radio"]'); if (f) f.focus(); } catch(e){}
        }
        function lockPanel(p, chosen, ok){
          var ansIdx = +p.getAttribute("data-answer");
          Array.prototype.slice.call(p.querySelectorAll(".nv-gs-opt")).forEach(function(lab, oi){
            var r = lab.querySelector('input[type="radio"]'); if (r) r.disabled = true;
            if (oi === ansIdx) lab.classList.add("nv-gs-correct");
            else if (oi === chosen) lab.classList.add("nv-gs-wrong");
          });
          p.classList.add(ok ? "nv-gs-answered-ok" : "nv-gs-answered-no");
          var sub = p.querySelector(".nv-gs-submit"); if (sub) sub.disabled = true;
        }
        function finish(){
          var marks = []; for (var k=0;k<n;k++) marks.push(!!answered[k]);
          var res = gsScore(marks);
          showGsFb(el, res); hidePanels();
          if (spinBtn){ spinBtn.disabled = true; spinBtn.hidden = true; }
          var ans = {}; for (var k2=0;k2<n;k2++) ans[k2] = answered[k2] ? 1 : 0;
          gsSeen["gs"+i] = { ok: res.ok, got: res.got, max: res.max, ans: ans };
          loc = { t:"gs", i:i }; current = -1;
          updateProgress();
        }
        function submit(idx){
          if (gsSeen["gs"+i] || (idx in answered)) return;
          var p = panels[idx]; if (!p) return;
          var chosen = p.querySelector('input[type="radio"]:checked');
          if (!chosen){ if (panelWrap) panelWrap.classList.add("nv-gs-nudge"); return; }
          var ok = (+chosen.value === +p.getAttribute("data-answer"));
          answered[idx] = ok; lockPanel(p, +chosen.value, ok); markSeg(idx, ok); current = -1;
          if (remaining().length){ if (spinBtn){ spinBtn.disabled = false; spinBtn.textContent = "Spin again"; } }
          else finish();
        }
        function spin(){
          if (gsSeen["gs"+i] || current >= 0) return;
          var rem = remaining(); if (!rem.length) return;
          var rng = makeRng((i+1)*0x9E3779B1 + Object.keys(answered).length);   // deterministic + resume-safe (count re-derivable)
          var idx = rem[Math.floor(rng()*rem.length)];
          if (spinBtn) spinBtn.disabled = true;
          pointAt(idx); reveal(idx);
        }
        if (spinBtn) spinBtn.addEventListener("click", spin);
        panels.forEach(function(p, qi){
          var sub = p.querySelector(".nv-gs-submit");
          if (sub) sub.addEventListener("click", function(){ submit(qi); });
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){
            r.addEventListener("change", function(){ if (panelWrap) panelWrap.classList.remove("nv-gs-nudge"); });
          });
        });
        // Restore a completed gameShow without re-scoring: re-mark each slice by its stored
        // correctness (dropped under byte pressure → just the tally), reveal the answers, lock.
        el.__gsRestore = function(rec){
          var ans = rec.ans || null;
          panels.forEach(function(p, qi){
            if (ans && (qi in ans)){ var ok = !!ans[qi]; answered[qi] = ok;
              lockPanel(p, -1, ok); markSeg(qi, ok); p.hidden = false; p.classList.add("nv-gs-restored");
            } else { p.hidden = true; Array.prototype.slice.call(p.querySelectorAll("input,button")).forEach(function(c){ c.disabled = true; }); }
          });
          if (spinBtn){ spinBtn.disabled = true; spinBtn.hidden = true; }
          showGsFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
          gsSeen["gs"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
        };
        // Graded-retry hook: wipe this block's closure state + DOM (resetQuiz calls it).
        gsResetters.push(function(){
          answered = {}; current = -1; turns = 0;
          if (rotor) rotor.style.transform = "";
          hidePanels();
          panels.forEach(function(p){
            p.classList.remove("nv-gs-answered-ok","nv-gs-answered-no","nv-gs-restored");
            Array.prototype.slice.call(p.querySelectorAll(".nv-gs-opt")).forEach(function(lab){ lab.classList.remove("nv-gs-correct","nv-gs-wrong"); var r=lab.querySelector('input[type="radio"]'); if(r){ r.disabled=false; r.checked=false; } });
            var sub=p.querySelector(".nv-gs-submit"); if(sub) sub.disabled=false;
          });
          segs.forEach(function(s){ s.classList.remove("nv-gs-done","nv-gs-ok","nv-gs-no"); });
          if (spinBtn){ spinBtn.disabled=false; spinBtn.hidden=false; spinBtn.textContent="Spin"; }
          var fb=el.querySelector(".nv-gs-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
      });

      /* quizBoard (Jeopardy category board): pick any tile, answer its MCQ, the tile flips
         correct/incorrect. WEIGHTED partial credit — points earned / points possible, so the
         tally reads as a score. Registers in qbSeen only once EVERY tile is answered (single-
         shot, mirroring gameShow); option order is fixed at build time → resume-stable. */
      quizboards.forEach(function(el, i){
        var board = el.querySelector(".nv-qb-board");
        var tiles = Array.prototype.slice.call(el.querySelectorAll(".nv-qb-tile"));
        var panels = Array.prototype.slice.call(el.querySelectorAll(".nv-qb-panel"));
        var panelWrap = el.querySelector(".nv-qb-panels");
        var n = panels.length;
        var answered = {};    // flatIdx -> ok(bool)
        var current = -1;     // tile whose panel is open (-1 = none)
        var tileByIdx = {}; tiles.forEach(function(tl){ tileByIdx[+tl.getAttribute("data-idx")] = tl; });

        // Panels render in flatIdx order (data-idx = array index); tiles render row-major, so
        // they're looked up by data-idx. Unique, panel-scoped radio names keep groups exclusive.
        panels.forEach(function(p, qi){
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){ r.name = "qb"+i+"q"+qi; });
        });
        function score(){
          var got=0, max=0;
          panels.forEach(function(p, qi){ var v=+p.getAttribute("data-value")||0; max+=v; if (answered[qi]) got+=v; });
          return { got:got, max:max, ok: max>0 && got===max };
        }
        function showFb(res){
          var fb = el.querySelector(".nv-qb-fb"); if (!fb) return;
          var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
          var tally = (res.max != null) ? ("You scored " + res.got + " of " + res.max + " points. ") : "";
          fb.innerHTML = '<span class="nv-sr-only">' + (res.ok ? "All correct. " : "Board complete. ") + '</span>' +
            tally + (msg || (res.ok ? "Clean sweep!" : "Review the answers above."));
          fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
        }
        function hidePanels(){ panels.forEach(function(p){ p.hidden = true; }); }
        function markTile(idx, ok){ var tl=tileByIdx[idx]; if (tl){ tl.classList.add("nv-qb-done", ok?"nv-qb-ok":"nv-qb-no"); tl.disabled=true; } }
        function remaining(){ var c=0; for (var k=0;k<n;k++){ if (!(k in answered)) c++; } return c; }
        function reveal(idx){
          current = idx; hidePanels();
          if (board) board.classList.add("nv-qb-picking");
          var p = panels[idx]; if (!p) return; p.hidden = false;
          try { var f = p.querySelector('input[type="radio"]'); if (f) f.focus(); } catch(e){}
        }
        function lockPanel(p, chosen, ok){
          var ansIdx = +p.getAttribute("data-answer");
          Array.prototype.slice.call(p.querySelectorAll(".nv-qb-opt")).forEach(function(lab, oi){
            var r = lab.querySelector('input[type="radio"]'); if (r) r.disabled = true;
            if (oi === ansIdx) lab.classList.add("nv-qb-correct");
            else if (oi === chosen) lab.classList.add("nv-qb-wrong");
          });
          p.classList.add(ok ? "nv-qb-answered-ok" : "nv-qb-answered-no");
          var sub = p.querySelector(".nv-qb-submit"); if (sub) sub.disabled = true;
        }
        function finish(){
          var res = score(); showFb(res); hidePanels();
          if (board) board.classList.remove("nv-qb-picking");
          var ans = {}; for (var k=0;k<n;k++) ans[k] = answered[k] ? 1 : 0;
          qbSeen["qb"+i] = { ok: res.ok, got: res.got, max: res.max, ans: ans };
          loc = { t:"qb", i:i }; current = -1;
          updateProgress();
        }
        function submit(idx){
          if (qbSeen["qb"+i] || (idx in answered)) return;
          var p = panels[idx]; if (!p) return;
          var chosen = p.querySelector('input[type="radio"]:checked');
          if (!chosen){ if (panelWrap) panelWrap.classList.add("nv-qb-nudge"); return; }
          var ok = (+chosen.value === +p.getAttribute("data-answer"));
          answered[idx] = ok; lockPanel(p, +chosen.value, ok); markTile(idx, ok);
          p.hidden = true; current = -1;
          if (board) board.classList.remove("nv-qb-picking");
          if (!remaining()) finish();          // else: back to the board for the next tile
        }
        tiles.forEach(function(tl){
          tl.addEventListener("click", function(){
            if (qbSeen["qb"+i] || current >= 0) return;
            var idx = +tl.getAttribute("data-idx");
            if (!(idx in answered)) reveal(idx);
          });
        });
        panels.forEach(function(p, qi){
          var sub = p.querySelector(".nv-qb-submit");
          if (sub) sub.addEventListener("click", function(){ submit(qi); });
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){
            r.addEventListener("change", function(){ if (panelWrap) panelWrap.classList.remove("nv-qb-nudge"); });
          });
        });
        // Restore a completed board without re-scoring: re-mark each tile by its stored
        // correctness (dropped under byte pressure → neutral done + just the tally), lock.
        el.__qbRestore = function(rec){
          var ans = rec.ans || null;
          for (var qi=0; qi<n; qi++){
            var known = !!(ans && (qi in ans)), ok = known && !!ans[qi], tl = tileByIdx[qi];
            if (known){ answered[qi] = ok; if (panels[qi]) lockPanel(panels[qi], -1, ok); }
            if (tl){ tl.disabled = true; tl.classList.add("nv-qb-done"); if (known) tl.classList.add(ok?"nv-qb-ok":"nv-qb-no"); }
          }
          hidePanels();
          showFb({ ok: !!rec.ok, got: rec.got, max: rec.max });
          qbSeen["qb"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
        };
        // Graded-retry hook: wipe this block's closure state + DOM (resetQuiz calls it).
        qbResetters.push(function(){
          answered = {}; current = -1;
          if (board) board.classList.remove("nv-qb-picking");
          hidePanels();
          tiles.forEach(function(tl){ tl.disabled = false; tl.classList.remove("nv-qb-done","nv-qb-ok","nv-qb-no"); });
          panels.forEach(function(p){
            p.classList.remove("nv-qb-answered-ok","nv-qb-answered-no");
            Array.prototype.slice.call(p.querySelectorAll(".nv-qb-opt")).forEach(function(lab){ lab.classList.remove("nv-qb-correct","nv-qb-wrong"); var r=lab.querySelector('input[type="radio"]'); if(r){ r.disabled=false; r.checked=false; } });
            var sub=p.querySelector(".nv-qb-submit"); if(sub) sub.disabled=false;
          });
          var fb=el.querySelector(".nv-qb-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
      });

      /* speedStreak — a fast one-at-a-time MCQ run. The learner presses Start, answers each
         question in sequence (a native radio group), and builds a CONSECUTIVE-CORRECT streak
         shown on a cosmetic scoreboard. An optional per-question countdown (data-timer) drives
         only a cosmetic speed bonus + combo score — the ONLY place a wall-clock enters, and it
         never touches correctness, the graded {got,max}, or the persisted state, so the block
         stays accessible (no WCAG timing-adjustable problem — you can answer after 0) and
         deterministic. Registers in ssSeen only once EVERY round is answered (single-shot,
         mirroring gameShow); option order is fixed at build time → resume-stable. PARTIAL
         credit (answered N of M correctly). */
      function showSsFb(el, res){
        var fb = el.querySelector(".nv-ss-fb"); if (!fb) return;
        var msg = res.ok ? fb.getAttribute("data-fb-correct") : fb.getAttribute("data-fb-incorrect");
        var tally = (res.got != null && res.max != null) ? ("You answered " + res.got + " of " + res.max + " correctly. ") : "";
        fb.innerHTML = '<span class="nv-sr-only">' + (res.ok ? "All correct. " : "Run complete. ") + '</span>' +
          tally + (msg || (res.ok ? "Perfect run!" : "Review the answers above."));
        fb.classList.remove("ok","no"); fb.classList.add("show", res.ok ? "ok" : "no");
      }
      speedstreaks.forEach(function(el, i){
        var panels = Array.prototype.slice.call(el.querySelectorAll(".nv-ss-panel"));
        var n = panels.length;
        var startBtn = el.querySelector(".nv-ss-start");
        var nextBtn = el.querySelector(".nv-ss-next");
        var scoreEl = el.querySelector(".nv-ss-score b");
        var streakEl = el.querySelector(".nv-ss-streak b");
        var progEl = el.querySelector(".nv-ss-progress");
        var timerEl = el.querySelector(".nv-ss-timer b");
        var timerBar = el.querySelector(".nv-ss-timerbar span");
        var TSEC = +(el.getAttribute("data-timer") || 0);
        var answered = {};    // roundIdx -> ok(bool)
        var current = -1;     // round currently revealed & awaiting an answer (-1 = none)
        var streak = 0, score = 0;   // cosmetic only — never part of the grade
        var tHandle = null, tRemain = 0;

        // Unique, panel-scoped radio names → a group is exclusive AND two speedStreaks can't clash.
        panels.forEach(function(p, qi){
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){ r.name = "ss"+i+"q"+qi; });
        });
        function hidePanels(){ panels.forEach(function(p){ p.hidden = true; }); }
        function setProg(){ if (progEl) progEl.textContent = Object.keys(answered).length + " / " + n; }
        function setStreak(){ if (streakEl) streakEl.textContent = streak; }
        function setScore(){ if (scoreEl) scoreEl.textContent = score; }
        function stopTimer(){ if (tHandle){ clearInterval(tHandle); tHandle = null; } }
        function paintTimer(){ if (timerEl) timerEl.textContent = tRemain;
          if (timerBar) timerBar.style.width = (TSEC > 0 ? (tRemain / TSEC * 100) : 0) + "%"; }
        function startTimer(){
          if (!(TSEC > 0)) return;
          stopTimer(); tRemain = TSEC; paintTimer();
          // wall-clock, but COSMETIC ONLY — expiry stops the bonus, never marks the answer or forces an advance.
          tHandle = setInterval(function(){ tRemain -= 1; if (tRemain <= 0){ tRemain = 0; stopTimer(); } paintTimer(); }, 1000);
        }
        function timeFrac(){ return TSEC > 0 ? (tRemain / TSEC) : 0; }   // fraction still on the clock (cosmetic bonus)
        function reveal(idx){
          current = idx; hidePanels();
          var p = panels[idx]; if (!p) return;
          p.hidden = false;
          if (nextBtn) nextBtn.hidden = true;
          startTimer();
          try { var f = p.querySelector('input[type="radio"]'); if (f) f.focus(); } catch(e){}
        }
        function lockPanel(p, chosen, ok){
          var ansIdx = +p.getAttribute("data-answer");
          Array.prototype.slice.call(p.querySelectorAll(".nv-ss-opt")).forEach(function(lab, oi){
            var r = lab.querySelector('input[type="radio"]'); if (r) r.disabled = true;
            if (oi === ansIdx) lab.classList.add("nv-ss-correct");
            else if (oi === chosen) lab.classList.add("nv-ss-wrong");
          });
          p.classList.add(ok ? "nv-ss-answered-ok" : "nv-ss-answered-no");
          var sub = p.querySelector(".nv-ss-submit"); if (sub) sub.disabled = true;
        }
        function finish(){
          var marks = []; for (var k=0;k<n;k++) marks.push(!!answered[k]);
          var res = ssScore(marks);
          showSsFb(el, res); hidePanels();
          if (nextBtn){ nextBtn.disabled = true; nextBtn.hidden = true; }
          if (startBtn){ startBtn.disabled = true; startBtn.hidden = true; }
          var ans = {}; for (var k2=0;k2<n;k2++) ans[k2] = answered[k2] ? 1 : 0;
          ssSeen["ss"+i] = { ok: res.ok, got: res.got, max: res.max, ans: ans };
          loc = { t:"ss", i:i }; current = -1;
          updateProgress();
        }
        function submit(idx){
          if (ssSeen["ss"+i] || (idx in answered)) return;
          var p = panels[idx]; if (!p) return;
          var chosen = p.querySelector('input[type="radio"]:checked');
          if (!chosen){ el.classList.add("nv-ss-nudge"); return; }
          el.classList.remove("nv-ss-nudge");
          var frac = timeFrac(); stopTimer();
          var ok = (+chosen.value === +p.getAttribute("data-answer"));
          score += ssCombo(ok, streak, frac);          // cosmetic combo — never touches the grade
          streak = ok ? streak + 1 : 0;
          answered[idx] = ok; lockPanel(p, +chosen.value, ok); current = -1;
          setProg(); setStreak(); setScore();
          if (Object.keys(answered).length < n){ if (nextBtn){ nextBtn.disabled = false; nextBtn.hidden = false; try{ nextBtn.focus(); }catch(e){} } }
          else finish();
        }
        function nextRound(){
          if (ssSeen["ss"+i] || current >= 0) return;
          for (var k=0;k<n;k++){ if (!(k in answered)){ reveal(k); return; } }
        }
        if (startBtn) startBtn.addEventListener("click", function(){
          if (ssSeen["ss"+i] || current >= 0) return;
          startBtn.disabled = true; startBtn.hidden = true;
          nextRound();
        });
        if (nextBtn) nextBtn.addEventListener("click", nextRound);
        panels.forEach(function(p, qi){
          var sub = p.querySelector(".nv-ss-submit");
          if (sub) sub.addEventListener("click", function(){ submit(qi); });
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){
            r.addEventListener("change", function(){ el.classList.remove("nv-ss-nudge"); });
          });
        });
        // Restore a completed speedStreak without re-scoring: re-mark each round by its stored
        // correctness (dropped under byte pressure → just the tally), reveal the answers, lock.
        // The cosmetic streak/score is NOT restored (motivational only) — just the final tally.
        el.__ssRestore = function(rec){
          stopTimer();
          var ans = rec.ans || null;
          panels.forEach(function(p, qi){
            if (ans && (qi in ans)){ var ok = !!ans[qi]; answered[qi] = ok;
              lockPanel(p, -1, ok); p.hidden = false; p.classList.add("nv-ss-restored");
            } else { p.hidden = true; Array.prototype.slice.call(p.querySelectorAll("input,button")).forEach(function(c){ c.disabled = true; }); }
          });
          if (startBtn){ startBtn.disabled = true; startBtn.hidden = true; }
          if (nextBtn){ nextBtn.disabled = true; nextBtn.hidden = true; }
          setProg();
          showSsFb(el, { ok: !!rec.ok, got: rec.got, max: rec.max });
          ssSeen["ss"+i] = { ok: !!rec.ok, got: rec.got, max: rec.max };
        };
        // Graded-retry hook: wipe this block's closure state + DOM (resetQuiz calls it).
        ssResetters.push(function(){
          stopTimer();
          answered = {}; current = -1; streak = 0; score = 0;
          setProg(); setStreak(); setScore();
          if (timerEl) timerEl.textContent = TSEC || 0;
          if (timerBar) timerBar.style.width = "100%";
          hidePanels();
          panels.forEach(function(p){
            p.classList.remove("nv-ss-answered-ok","nv-ss-answered-no","nv-ss-restored");
            Array.prototype.slice.call(p.querySelectorAll(".nv-ss-opt")).forEach(function(lab){ lab.classList.remove("nv-ss-correct","nv-ss-wrong"); var r=lab.querySelector('input[type="radio"]'); if(r){ r.disabled=false; r.checked=false; } });
            var sub=p.querySelector(".nv-ss-submit"); if(sub) sub.disabled=false;
          });
          el.classList.remove("nv-ss-nudge");
          if (startBtn){ startBtn.disabled=false; startBtn.hidden=false; }
          if (nextBtn){ nextBtn.disabled=true; nextBtn.hidden=true; }
          var fb=el.querySelector(".nv-ss-fb"); if(fb){ fb.classList.remove("show","ok","no"); fb.innerHTML=""; }
        });
      });

      /* whackAMole — FORMATIVE recognition game (James, 2026-07-10). The moles are real
         <button>s already in the DOM (a11y + no-JS = a static "click the correct ones"
         board); this wiring adds the click scoring + completion. Clicks are isTrusted-
         guarded so a synthetic/scripted click can't auto-whack (anti-cheat). Completion-
         only: wamSeen never enters gradedScore()/xpTotals() (no data-obj), so the in-game
         score (targets hit − decoys hit, floored) is motivational feedback, not a grade.
         Moles never disappear on a clock → no WCAG 2.2.1 time limit on the essential
         function; the CSS pop-in entrance is purely cosmetic. */
      whackamoles.forEach(function(el, i){
        var moles = Array.prototype.slice.call(el.querySelectorAll(".nv-wam-mole"));
        var doneBtn = el.querySelector(".nv-wam-done");
        var fb = el.querySelector(".nv-wam-fb");
        var scoreEl = el.querySelector(".nv-wam-score b");
        var targets = moles.filter(function(m){ return m.getAttribute("data-target") === "1"; }).length;
        var hits = {};                 // idx -> true once whacked (target or decoy)
        function isTarget(m){ return m.getAttribute("data-target") === "1"; }
        function tally(){ return wamScore(moles.map(function(m, mi){ return { target: isTarget(m), hit: !!hits[mi] }; })); }
        function counts(){ var t=0, d=0; moles.forEach(function(m, mi){ if (hits[mi]){ if (isTarget(m)) t++; else d++; } }); return { t:t, d:d }; }
        function targetsLeft(){ return moles.some(function(m, mi){ return isTarget(m) && !hits[mi]; }); }
        function refreshScore(){ if (scoreEl) scoreEl.textContent = String(tally().got); }
        function finish(){
          if (wamSeen["wm"+i]) return;
          moles.forEach(function(m){ m.disabled = true; m.classList.add("nv-wam-locked"); });
          if (doneBtn){ doneBtn.disabled = true; doneBtn.hidden = true; }
          var r = tally(), c = counts();
          wamSeen["wm"+i] = { ok: r.ok, got: r.got, max: r.max };
          if (fb){ fb.classList.remove("ok","no"); fb.classList.add("show", r.ok ? "ok" : "no");
            var msg = "You found " + c.t + " of " + targets + " correct" + (c.d ? (" and hit " + c.d + " decoy" + (c.d>1?"s":"")) : "") + ".";
            fb.innerHTML = '<span class="nv-sr-only">' + (r.ok ? "Perfect. " : "Review. ") + '</span>' + msg; }
          save(); updateProgress();
        }
        moles.forEach(function(m, mi){
          m.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;       // anti-cheat: ignore synthetic clicks
            if (wamSeen["wm"+i] || hits[mi]) return;
            hits[mi] = true;
            var good = isTarget(m);
            m.disabled = true;
            m.classList.add("nv-wam-whacked", good ? "nv-wam-hit" : "nv-wam-miss");
            var mark = document.createElement("span"); mark.className = "nv-sr-only";
            mark.textContent = good ? " (correct)" : " (decoy)"; m.appendChild(mark);
            refreshScore();
            if (fb){ fb.classList.remove("ok","no"); fb.classList.add("show", good ? "ok" : "no");
              fb.textContent = good ? "Correct — that’s one to whack." : "That’s a decoy — costs you a point."; }
            if (!targetsLeft()) finish();                    // auto-finish when every target is found
          });
        });
        if (doneBtn) doneBtn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; finish(); });
        refreshScore();
        // Resume: re-lock the field and re-show the final tally. Under byte pressure only
        // {ok,got,max} survive (the per-mole hit set is dropped), so a resumed game can't
        // re-color individual moles — it shows the score + locks, mirroring the graded games.
        el.__wamRestore = function(rec){
          moles.forEach(function(m){ m.disabled = true; m.classList.add("nv-wam-locked"); });
          if (doneBtn){ doneBtn.disabled = true; doneBtn.hidden = true; }
          wamSeen["wm"+i] = { ok: !!(rec && rec.ok), got: (rec && rec.got) || 0, max: (rec && rec.max) || targets };
          if (scoreEl) scoreEl.textContent = String((rec && rec.got) || 0);
          if (fb){ fb.classList.add("show", (rec && rec.ok) ? "ok" : "no");
            fb.textContent = "You completed this activity (" + ((rec && rec.got) || 0) + " / " + targets + ")."; }
        };
      });

      /* dunkBooth — FORMATIVE arcade reward game (James, 2026-07-27; REPLACES the retired Quiz
         Show). Answer a randomly-drawn MCQ to EARN a throw, then release the oscillating timing
         meter inside the strike zone to dunk the character. Each landed dunk NARROWS the zone
         (escalating difficulty). No win/lose — completion is engagement (one throw released) and
         the dunk tally is motivational only: dbSeen never enters gradedScore()/xpTotals() (no
         data-obj). No WCAG 2.2.1 time limit on the essential function — the learner controls the
         release, misses never end the game, retries are unlimited; under prefers-reduced-motion
         the sweep is slowed. A wrong answer reveals the correct option and stays open so a throw
         is always earnable (no soft-lock). Clicks are isTrusted-guarded (anti-cheat). The static
         DOM (booth/target/meter/track/zone/indicator/panels) is already rendered; this wires the
         animation + draw. */
      function setupPhysicsDunk(el, i){
        var physics=window.CarnivalPhysics, stage=el.querySelector(".nv-dunk-stage");
        el.classList.add("nv-physics-mode");
        var plate=el.querySelector(".nv-dunk-plate"), ball=el.querySelector(".nv-dunk-ball");
        var guide=el.querySelector(".nv-dunk-guide"), target=el.querySelector(".nv-dunk-target");
        var water=el.querySelector(".nv-dunk-water"), throwBtn=el.querySelector(".nv-dunk-throw");
        var aimInput=el.querySelector(".nv-dunk-aim"), powerInput=el.querySelector(".nv-dunk-power");
        var restart=el.querySelector(".nv-dunk-restart"), countEl=el.querySelector(".nv-dunk-count");
        var fb=el.querySelector(".nv-dunk-fb"), panels=Array.prototype.slice.call(el.querySelectorAll(".nv-dunk-panel"));
        var fbOk=fb?(fb.getAttribute("data-fb-correct")||""):"", fbNo=fb?(fb.getAttribute("data-fb-incorrect")||""):"";
        var dunks=0, throws=0, active=false, inFlight=false, curPanel=null, run=null;
        function origin(){return{x:ball.offsetLeft+ball.offsetWidth/2,y:ball.offsetTop+ball.offsetHeight/2};}
        function say(ok,msg){if(!fb)return;fb.classList.remove("ok","no");fb.classList.add("show",ok?"ok":"no");fb.textContent=msg;}
        function count(){if(countEl)countEl.textContent=String(dunks);}
        function enable(on){[ball,throwBtn,aimInput,powerInput].forEach(function(c){if(c)c.disabled=!on;});
          if(stage)stage.classList.toggle("nv-physics-armed",!!on);}
        function reset(){if(ball){ball.hidden=false;ball.style.transform="";}if(guide)guide.innerHTML="";}
        function preview(p,sync){if(!ball||!guide)return;var v=physics.pullVelocity("dunk",p,0);
          ball.style.transform="translate("+p.x.toFixed(1)+"px,"+p.y.toFixed(1)+"px) rotate("+(p.x*.8).toFixed(1)+"deg)";
          physics.paintTrajectory(stage,guide,"dunk",origin(),v);
          if(sync){var c=physics.controlsForPull("dunk",p);aimInput.value=String(Math.round(c.angle));powerInput.value=String(Math.round(c.power));}}
        function preset(){if(active&&!inFlight)preview(physics.aimedPull("dunk",aimInput.value,powerInput.value),false);}
        function clear(p){Array.prototype.slice.call(p.querySelectorAll(".nv-dunk-opt")).forEach(function(o){
          o.classList.remove("nv-dunk-right","nv-dunk-wrong");var r=o.querySelector("input");if(r){r.checked=false;r.disabled=false;}});}
        function show(p){panels.forEach(function(x){x.hidden=true;});curPanel=p;if(!p)return;clear(p);p.hidden=false;}
        function next(){if(panels.length)show(panels[Math.floor(Math.random()*panels.length)]);}
        function record(){dbSeen["db"+i]={ok:1,got:dunks,max:throws};}
        function earn(){if(curPanel)curPanel.hidden=true;active=true;reset();enable(true);preset();
          if(ball)try{ball.focus();}catch(e){}say(true,"Ball ready. Drag backward in the field and release, or use the Aim and Power controls.");}
        function finish(hit,flight){inFlight=false;if(flight&&flight.parentNode)flight.parentNode.removeChild(flight);reset();
          if(hit){dunks++;count();if(target){target.classList.remove("nv-dunk-dunked");void target.offsetWidth;target.classList.add("nv-dunk-dunked");}
            if(water){water.classList.remove("nv-dunk-splash");void water.offsetWidth;water.classList.add("nv-dunk-splash");}
            say(true,(fbOk?fbOk+" ":"Direct hit! ")+"Dunks: "+dunks+".");
          }else say(false,(fbNo?fbNo+" ":"Missed the plate. ")+"Adjust the arc and try another ball.");
          record();if(restart)restart.hidden=false;next();save();updateProgress();}
        function launch(velocity){if(!active||inFlight)return;active=false;inFlight=true;enable(false);throws++;
          var o=origin(),flight=ball.cloneNode(false);flight.disabled=true;flight.classList.add("nv-physics-flight");stage.appendChild(flight);ball.hidden=true;
          record();save();updateProgress();
          run=physics.launch({profile:"dunk",stage:stage,origin:o,velocity:velocity,reducedMotion:reduceMotion,
            targets:[physics.elementTarget(stage,plate,"plate","circle",-3,false)],
            onFrame:function(pos){flight.style.left="0";flight.style.top="0";flight.style.bottom="auto";
              flight.style.transform="translate("+(pos.x-14).toFixed(1)+"px,"+(pos.y-14).toFixed(1)+"px) rotate("+(pos.angle*180/Math.PI).toFixed(1)+"deg)";},
            onComplete:function(result){finish(!!result.hit,flight);}});}
        physics.bindPull({profile:"dunk",stage:stage,surface:stage,handle:ball,origin:origin,delta:true,
          enabled:function(){return active&&!inFlight;},onDragState:function(on){stage.classList.toggle("nv-physics-dragging",on);},
          onPreview:function(p){preview(p,true);},onCancel:preset,onRelease:function(p,v){launch(v);}});
        panels.forEach(function(p){var submit=p.querySelector(".nv-dunk-submit");if(!submit)return;
          submit.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;if(p.hidden)return;
            var opts=Array.prototype.slice.call(p.querySelectorAll(".nv-dunk-opt")),chosen=-1;
            opts.forEach(function(o,oi){var r=o.querySelector("input");if(r&&r.checked)chosen=oi;});
            if(chosen<0){say(false,"Pick an answer to earn your ball.");return;}var ans=parseInt(p.getAttribute("data-answer")||"0",10);
            if(chosen===ans){if(opts[chosen])opts[chosen].classList.add("nv-dunk-right");earn();}
            else{if(opts[chosen])opts[chosen].classList.add("nv-dunk-wrong");if(opts[ans])opts[ans].classList.add("nv-dunk-right");
              say(false,"Not quite. Choose the highlighted answer to earn your ball.");}});});
        if(throwBtn)throwBtn.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;
          launch(physics.aimedVelocity("dunk",aimInput.value,powerInput.value));});
        if(aimInput)aimInput.addEventListener("input",preset);
        if(powerInput)powerInput.addEventListener("input",preset);
        window.addEventListener("resize",function(){if(active&&!inFlight)preset();});
        if(restart)restart.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;
          if(run)run.stop("restart");dunks=0;throws=0;active=false;inFlight=false;count();enable(false);reset();restart.hidden=true;
          say(true,"Fresh run. Answer a question to earn a ball.");next();});
        count();enable(false);reset();next();
        el.__dunkRestore=function(rec){dunks=(rec&&rec.got)||0;throws=(rec&&rec.max)||1;record();count();active=false;inFlight=false;
          enable(false);reset();if(restart)restart.hidden=false;say(true,"You completed this activity — "+dunks+" dunk"+(dunks===1?"":"s")+" landed. Play again to beat it.");next();};
      }
      dunkbooths.forEach(function(el, i){
        if(window.CarnivalPhysics){setupPhysicsDunk(el,i);return;}
        var ZONE_BASE = 40, ZONE_STEP = 6, ZONE_MIN = 12;         // strike-zone escalation (% of track)
        var SWEEP_MS = reduceMotion ? 2600 : 1400;                // one full 0→100→0 oscillation
        var target = el.querySelector(".nv-dunk-target");
        var water  = el.querySelector(".nv-dunk-water");
        var meter  = el.querySelector(".nv-dunk-meter");
        var trackEl = el.querySelector(".nv-dunk-track");
        var zone   = el.querySelector(".nv-dunk-zone");
        var indic  = el.querySelector(".nv-dunk-indicator");
        var throwBtn = el.querySelector(".nv-dunk-throw");
        var restart  = el.querySelector(".nv-dunk-restart");
        var countEl  = el.querySelector(".nv-dunk-count");
        var fb       = el.querySelector(".nv-dunk-fb");
        var panels = Array.prototype.slice.call(el.querySelectorAll(".nv-dunk-panel"));
        var fbOk = fb ? (fb.getAttribute("data-fb-correct") || "") : "";
        var fbNo = fb ? (fb.getAttribute("data-fb-incorrect") || "") : "";
        // The rendered `.nv-dunk-meter` is aria-hidden, but it holds the focusable Throw button.
        // Move aria-hidden onto the purely-visual track so the button stays reachable to AT.
        if (meter) meter.removeAttribute("aria-hidden");
        if (trackEl) trackEl.setAttribute("aria-hidden", "true");
        if (throwBtn && !throwBtn.getAttribute("aria-label")) throwBtn.setAttribute("aria-label", "Throw — release inside the strike zone");
        var dunks = 0, throws = 0, active = false, rafId = 0, pos = 0, curPanel = null;

        function setZone(){ var w = dunkZone(dunks, ZONE_BASE, ZONE_STEP, ZONE_MIN);
          if (zone){ zone.style.width = w + "%"; zone.style.left = ((100 - w) / 2) + "%"; } return w; }
        function showCount(){ if (countEl) countEl.textContent = String(dunks); }
        function say(ok, msg){ if (!fb) return; fb.classList.remove("ok","no"); fb.classList.add("show", ok?"ok":"no"); fb.textContent = msg; }
        function clearOpts(p){ Array.prototype.slice.call(p.querySelectorAll(".nv-dunk-opt")).forEach(function(o){
          o.classList.remove("nv-dunk-right","nv-dunk-wrong"); var r=o.querySelector("input"); if(r){ r.checked=false; r.disabled=false; } }); }
        function showPanel(p){ panels.forEach(function(x){ x.hidden = true; }); curPanel = p; if (!p) return;
          clearOpts(p); var s = p.querySelector(".nv-dunk-submit"); if (s){ s.disabled=false; s.textContent="Submit answer"; }
          p.hidden = false; }
        function nextQuestion(){ if (!panels.length) return;
          showPanel(panels[Math.floor(Math.random()*panels.length)]); }   // random draw from the whole block

        function startSweep(){ if (!indic || !window.requestAnimationFrame) return;
          var nowFn = (window.performance && performance.now) ? function(){ return performance.now(); } : function(){ return Date.now(); };
          var t0 = nowFn();
          (function frame(){ var phase = ((nowFn() - t0) % SWEEP_MS) / SWEEP_MS;   // 0..1
            pos = phase <= 0.5 ? (phase * 2 * 100) : ((1 - phase) * 2 * 100);       // triangle wave 0→100→0
            indic.style.left = pos + "%";
            rafId = requestAnimationFrame(frame); })(); }
        function stopSweep(){ if (rafId && window.cancelAnimationFrame) cancelAnimationFrame(rafId); rafId = 0; }

        function earnThrow(){ if (curPanel) curPanel.hidden = true; active = true;
          setZone(); if (throwBtn) throwBtn.disabled = false; startSweep();
          if (throwBtn) try { throwBtn.focus(); } catch(e){} }
        function record(){ dbSeen["db"+i] = { ok:1, got:dunks, max:throws }; }   // completion-only; never a grade

        function doThrow(){ if (!active) return; active = false; stopSweep();
          if (throwBtn) throwBtn.disabled = true; throws++;
          var hit = dunkHit(pos, dunkZone(dunks, ZONE_BASE, ZONE_STEP, ZONE_MIN));
          if (indic) indic.classList.add("nv-dunk-frozen");
          if (hit){ dunks++; showCount(); setZone();                              // narrow the zone for next time
            if (target){ target.classList.remove("nv-dunk-dunked"); void target.offsetWidth; target.classList.add("nv-dunk-dunked"); }
            if (water){ water.classList.remove("nv-dunk-splash"); void water.offsetWidth; water.classList.add("nv-dunk-splash"); }
            say(true, (fbOk ? fbOk + " " : "Direct hit! ") + "Dunks: " + dunks + ".");
          } else { say(false, (fbNo ? fbNo + " " : "So close — just outside the zone. ") + "Line up another throw."); }
          record(); if (restart) restart.hidden = false;
          if (window.setTimeout) window.setTimeout(function(){ if (indic) indic.classList.remove("nv-dunk-frozen"); nextQuestion(); }, 900);
          else nextQuestion();
          save(); updateProgress(); }

        panels.forEach(function(p){ var submit = p.querySelector(".nv-dunk-submit"); if (!submit) return;
          submit.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; if (p.hidden) return;
            var opts = Array.prototype.slice.call(p.querySelectorAll(".nv-dunk-opt"));
            var chosen = -1; opts.forEach(function(o, oi){ var r=o.querySelector("input"); if (r && r.checked) chosen = oi; });
            if (chosen < 0){ say(false, "Pick an answer to earn your throw."); return; }
            var ans = parseInt(p.getAttribute("data-answer") || "0", 10);
            if (chosen === ans){ if (opts[chosen]) opts[chosen].classList.add("nv-dunk-right"); say(true, "Correct — take your throw!"); earnThrow(); }
            else { if (opts[chosen]) opts[chosen].classList.add("nv-dunk-wrong"); if (opts[ans]) opts[ans].classList.add("nv-dunk-right");
              say(false, "Not quite — the highlighted answer is correct. Choose it to earn your throw."); }   // stays open: always earnable
          }); });

        if (throwBtn) throwBtn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; doThrow(); });
        if (restart) restart.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return;
          dunks = 0; throws = 0; active = false; stopSweep(); showCount(); setZone();
          if (throwBtn) throwBtn.disabled = true; restart.hidden = true;
          say(true, "Fresh run — answer a question to earn a throw."); nextQuestion(); });

        setZone(); showCount(); if (throwBtn) throwBtn.disabled = true; nextQuestion();   // initial paint

        // Resume: only the tally survives byte pressure. Re-show the count, mark complete, and
        // leave the game replayable (a new question is drawn) — mirrors __wamRestore's re-lock.
        el.__dunkRestore = function(rec){ dunks = (rec && rec.got) || 0; throws = (rec && rec.max) || 1;
          record(); showCount(); setZone(); active = false; stopSweep();
          if (throwBtn) throwBtn.disabled = true; if (restart) restart.hidden = false;
          say(true, "You completed this activity — " + dunks + " dunk" + (dunks===1?"":"s") + " landed. Play again to beat it.");
          nextQuestion(); };
      });

      /* balloonPop — FORMATIVE arcade reward game (James, 2026-07-27; the second shell in the
         arcade library alongside dunkBooth). A 2-AXIS carnival board: answer a randomly-drawn MCQ
         to EARN a dart, AIM a column (← → or the ◀ ▶ buttons), and HOLD Space (or the Charge
         button) to run a vertical power meter that sweeps up/down — release throws the dart at that
         power. Low power hits the bottom row, high the top; the released power must land in that
         row's target BAND (gutters = a miss). Clearing every balloon advances a difficulty LEVEL
         (balloonLevel: narrower bands + smaller targets + a bigger board, up to 4×4). No win/lose —
         completion is engagement (one dart released, hit OR miss) so timing is never essential
         (WCAG 2.2.1) and the center row is always winnable; the pop tally is motivational only
         (bpSeen never enters gradedScore()/xpTotals(); no data-obj). Under prefers-reduced-motion
         the sweep is slowed. A wrong answer reveals the correct option and stays open so a dart is
         always earnable (no soft-lock). Keyboard is handled at the block level (arrows/Space, with
         preventDefault so they don't scroll the page); the on-screen buttons drive the pointer path
         (the Charge button has NO click handler, so a keyboard Space never double-fires with the
         block handler). All interactions are isTrusted-guarded (anti-cheat). */
      function setupPhysicsBalloons(el, i){
        var physics=window.CarnivalPhysics, DONE_POPS=2, DEFAULT_DIFF=1;
        el.classList.add("nv-physics-mode");
        var stage=el.querySelector(".nv-balloon-stage"), grid=el.querySelector(".nv-balloon-grid");
        var dart=el.querySelector(".nv-balloon-dart"), guide=el.querySelector(".nv-balloon-guide");
        var throwBtn=el.querySelector(".nv-balloon-throw"), aimInput=el.querySelector(".nv-balloon-aim");
        var powerInput=el.querySelector(".nv-balloon-power-input"), aimL=el.querySelector(".nv-balloon-aim-left");
        var aimR=el.querySelector(".nv-balloon-aim-right"), diffBtns=Array.prototype.slice.call(el.querySelectorAll(".nv-balloon-diff"));
        var restart=el.querySelector(".nv-balloon-restart"), countEl=el.querySelector(".nv-balloon-count");
        var levelEl=el.querySelector(".nv-balloon-level"), fb=el.querySelector(".nv-balloon-fb");
        var panels=Array.prototype.slice.call(el.querySelectorAll(".nv-balloon-panel"));
        var fbOk=fb?(fb.getAttribute("data-fb-correct")||""):"",fbNo=fb?(fb.getAttribute("data-fb-incorrect")||""):"";
        var round=0,diff=DEFAULT_DIFF,spec=balloonLevel(round,diff),popped={},poppedN=0,totalPops=0,darts=0;
        var active=false,inFlight=false,curPanel=null,baseOrigin=null,run=null;
        function key(r,c){return r+"_"+c;}
        function origin(){if(baseOrigin)return baseOrigin;var sr=stage.getBoundingClientRect(),dr=dart.getBoundingClientRect();
          return{x:dr.left+dr.width/2-sr.left,y:dr.top+dr.height/2-sr.top};}
        function captureOrigin(){baseOrigin=null;baseOrigin=origin();}
        function say(ok,msg){if(!fb)return;fb.classList.remove("ok","no");fb.classList.add("show",ok?"ok":"no");fb.textContent=msg;}
        function count(){if(countEl)countEl.textContent=String(totalPops);if(levelEl)levelEl.textContent=String(round+1);}
        function enable(on){[dart,throwBtn,aimInput,powerInput,aimL,aimR].forEach(function(c){if(c)c.disabled=!on;});
          if(stage)stage.classList.toggle("nv-physics-armed",!!on);}
        function reset(){if(dart){dart.hidden=false;dart.style.transform="";}if(guide)guide.innerHTML="";}
        function preview(p,sync){if(!dart||!guide)return;var v=physics.pullVelocity("dart",p,0);
          var launchAngle=Math.atan2(-v.y,v.x)*180/Math.PI;
          dart.style.transform="translate("+p.x.toFixed(1)+"px,"+p.y.toFixed(1)+"px) rotate("+(90-launchAngle).toFixed(1)+"deg)";
          physics.paintTrajectory(stage,guide,"dart",origin(),v);
          if(sync){var c=physics.controlsForPull("dart",p);aimInput.value=String(Math.round(c.angle));powerInput.value=String(Math.round(c.power));}}
        function preset(){if(active&&!inFlight)preview(physics.aimedPull("dart",aimInput.value,powerInput.value),false);}
        function clear(p){Array.prototype.slice.call(p.querySelectorAll(".nv-balloon-opt")).forEach(function(o){
          o.classList.remove("nv-balloon-right","nv-balloon-wrong");var r=o.querySelector("input");if(r){r.checked=false;r.disabled=false;}});}
        function show(p){panels.forEach(function(x){x.hidden=true;});curPanel=p;if(!p)return;clear(p);p.hidden=false;}
        function next(){if(panels.length)show(panels[Math.floor(Math.random()*panels.length)]);}
        function build(){spec=balloonLevel(round,diff);popped={};poppedN=0;var html="";
          if(grid){grid.style.setProperty("--bp-cols",spec.cols);grid.style.setProperty("--bp-scale",spec.targetScale.toFixed(3));
            for(var dr=0;dr<spec.rows;dr++){var r=spec.rows-1-dr;for(var c=0;c<spec.cols;c++){
              html+='<div class="nv-balloon-cell" role="gridcell" data-r="'+r+'" data-c="'+c+'" data-swatch="'+(el.getAttribute("data-swatch")||"red")+
                '"><span class="nv-balloon-knot" aria-hidden="true"></span></div>';}}grid.innerHTML=html;}}
        function descriptors(){var out=[];Array.prototype.slice.call(grid.querySelectorAll(".nv-balloon-cell:not(.nv-balloon-gone)")).forEach(function(cell){
          var r=+cell.getAttribute("data-r"),c=+cell.getAttribute("data-c"),d=physics.elementTarget(stage,cell,key(r,c),"circle",-4,false);
          d.cell=cell;d.row=r;d.col=c;out.push(d);});return out;}
        function record(){if(totalPops>=DONE_POPS)bpSeen["bp"+i]={ok:1,got:totalPops,max:darts};}
        function earn(){if(curPanel)curPanel.hidden=true;active=true;reset();captureOrigin();enable(true);preset();
          if(dart)try{dart.focus();}catch(e){}say(true,"Dart ready. Drag backward in the field and release, or use the Aim and Power controls.");}
        function levelUp(){round++;build();count();say(true,"Board cleared. Round "+(round+1)+" has a tighter balloon wall.");}
        function finish(hit,flight){inFlight=false;if(flight&&flight.parentNode)flight.parentNode.removeChild(flight);reset();
          if(hit&&!popped[hit.id]){popped[hit.id]=1;poppedN++;totalPops++;count();if(hit.cell)hit.cell.classList.add("nv-balloon-gone");
            say(true,(fbOk?fbOk+" ":"Pop! ")+"Popped "+totalPops+(totalPops===DONE_POPS?" — enough to finish; keep playing or move on.":"."));
            if(poppedN>=spec.cols*spec.rows){if(window.setTimeout)setTimeout(levelUp,350);else levelUp();}
          }else say(false,(fbNo?fbNo+" ":"Missed. ")+"Adjust the dart's angle and power.");
          record();if(restart)restart.hidden=false;next();save();updateProgress();}
        function launch(velocity){if(!active||inFlight)return;active=false;inFlight=true;enable(false);darts++;
          var o=origin(),flight=dart.cloneNode(false);flight.disabled=true;flight.classList.add("nv-physics-flight");stage.appendChild(flight);dart.hidden=true;
          run=physics.launch({profile:"dart",stage:stage,origin:o,velocity:velocity,reducedMotion:reduceMotion,targets:descriptors(),
            onFrame:function(pos){flight.style.left="0";flight.style.top="0";flight.style.bottom="auto";
              var heading=Math.atan2(pos.vy,pos.vx)*180/Math.PI+90;
              flight.style.transform="translate("+(pos.x-3).toFixed(1)+"px,"+(pos.y-26).toFixed(1)+"px) rotate("+heading.toFixed(1)+"deg)";},
            onComplete:function(result){finish(result.hit,flight);}});}
        physics.bindPull({profile:"dart",stage:stage,surface:stage,handle:dart,origin:origin,delta:true,
          enabled:function(){return active&&!inFlight;},onDragState:function(on){stage.classList.toggle("nv-physics-dragging",on);},
          onPreview:function(p){preview(p,true);},onCancel:preset,onRelease:function(p,v){launch(v);}});
        panels.forEach(function(p){var submit=p.querySelector(".nv-balloon-submit");if(!submit)return;
          submit.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;if(p.hidden)return;
            var opts=Array.prototype.slice.call(p.querySelectorAll(".nv-balloon-opt")),chosen=-1;
            opts.forEach(function(o,oi){var r=o.querySelector("input");if(r&&r.checked)chosen=oi;});
            if(chosen<0){say(false,"Pick an answer to earn your dart.");return;}var ans=parseInt(p.getAttribute("data-answer")||"0",10);
            if(chosen===ans){if(opts[chosen])opts[chosen].classList.add("nv-balloon-right");earn();}
            else{if(opts[chosen])opts[chosen].classList.add("nv-balloon-wrong");if(opts[ans])opts[ans].classList.add("nv-balloon-right");
              say(false,"Not quite. Choose the highlighted answer to earn your dart.");}});});
        function nudge(delta){if(!active)return;aimInput.value=String(Math.max(+aimInput.min,Math.min(+aimInput.max,+aimInput.value+delta)));preset();}
        if(aimL)aimL.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;nudge(4);});
        if(aimR)aimR.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;nudge(-4);});
        if(throwBtn)throwBtn.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;
          launch(physics.aimedVelocity("dart",aimInput.value,powerInput.value));});
        if(aimInput)aimInput.addEventListener("input",preset);
        if(powerInput)powerInput.addEventListener("input",preset);
        window.addEventListener("resize",function(){if(active&&!inFlight){reset();captureOrigin();preset();}});
        diffBtns.forEach(function(btn){btn.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;
          diff=Math.max(0,+btn.getAttribute("data-diff")||0);round=0;diffBtns.forEach(function(b){var on=b===btn;b.classList.toggle("nv-balloon-diff-on",on);b.setAttribute("aria-pressed",on?"true":"false");});
          active=false;enable(false);reset();build();count();say(true,"Difficulty set. Answer a question to earn a dart.");});});
        if(restart)restart.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;if(run)run.stop("restart");
          totalPops=0;darts=0;round=0;active=false;inFlight=false;build();count();enable(false);reset();restart.hidden=true;
          say(true,"Fresh run. Answer a question to earn a dart.");next();});
        build();count();enable(false);reset();next();
        el.__balloonRestore=function(rec){totalPops=(rec&&rec.got)||0;darts=(rec&&rec.max)||1;record();build();count();active=false;inFlight=false;
          enable(false);reset();if(restart)restart.hidden=false;say(true,"You completed this activity — "+totalPops+" balloon"+(totalPops===1?"":"s")+" popped. Play again to beat it.");next();};
      }
      balloons.forEach(function(el, i){
        if(window.CarnivalPhysics){setupPhysicsBalloons(el,i);return;}
        var POWER_CYCLE = reduceMotion ? 3000 : 1600;            // one accelerating 0→100 ramp, then snap
        var MAX_ANGLE = 42, DONE_POPS = 2;                       // aim range (deg); pops needed to mark the block DONE
        var DEFAULT_DIFF = 1;                                    // Standard by default (chooser can change)
        var grid    = el.querySelector(".nv-balloon-grid");
        var dartEl  = el.querySelector(".nv-balloon-dart");
        var powerEl = el.querySelector(".nv-balloon-power");
        var fillEl  = el.querySelector(".nv-balloon-fill");
        var marksEl = el.querySelector(".nv-balloon-bands");     // now holds per-row power-height marks
        var throwBtn = el.querySelector(".nv-balloon-throw");
        var aimL    = el.querySelector(".nv-balloon-aim-left");
        var aimR    = el.querySelector(".nv-balloon-aim-right");
        var diffBtns = Array.prototype.slice.call(el.querySelectorAll(".nv-balloon-diff"));
        var restart  = el.querySelector(".nv-balloon-restart");
        var countEl  = el.querySelector(".nv-balloon-count");
        var levelEl  = el.querySelector(".nv-balloon-level");
        var fb       = el.querySelector(".nv-balloon-fb");
        var panels = Array.prototype.slice.call(el.querySelectorAll(".nv-balloon-panel"));
        var fbOk = fb ? (fb.getAttribute("data-fb-correct") || "") : "";
        var fbNo = fb ? (fb.getAttribute("data-fb-incorrect") || "") : "";
        // The visual power meter is aria-hidden; the focusable grid + buttons carry the a11y path.
        var round = 0, diff = DEFAULT_DIFF, spec = balloonLevel(round, diff), aim = 0;   // round=boards cleared; diff=Easy/Std/Hard; aim=launch angle (deg)
        var popped = {}, poppedN = 0, totalPops = 0, darts = 0;
        var active = false, charging = false, rafId = 0, pwr = 0, curPanel = null;

        function nowFn(){ return (window.performance && performance.now) ? performance.now() : Date.now(); }
        function showCount(){ if (countEl) countEl.textContent = String(totalPops); if (levelEl) levelEl.textContent = String(round+1); }
        function say(ok, msg){ if (!fb) return; fb.classList.remove("ok","no"); fb.classList.add("show", ok?"ok":"no"); fb.textContent = msg; }
        function key(r,c){ return r+"_"+c; }

        // draw a mark on the power meter at each ROW's target height, so the learner can read how
        // much power reaches each row (bottom row = low, top row = high). Height = (r+0.5)/rows.
        function paintMarks(){ if (!marksEl) return; var h="";
          for (var r=0;r<spec.rows;r++){ var y=100*(r+0.5)/spec.rows;
            h += '<div class="nv-balloon-mark" style="bottom:'+y.toFixed(1)+'%"></div>'; }
          marksEl.innerHTML = h; }

        function buildBoard(){ spec = balloonLevel(round, diff); popped = {}; poppedN = 0; aim = 0;
          if (grid){ grid.style.setProperty("--bp-cols", spec.cols);
            grid.style.setProperty("--bp-scale", spec.targetScale.toFixed(3));
            var cells = "";
            // rows top→bottom in DOM order (row 0 in the spec = BOTTOM, so DOM row index inverts)
            for (var dr=0; dr<spec.rows; dr++){ var r = spec.rows-1-dr;
              for (var c=0; c<spec.cols; c++){
                cells += '<div class="nv-balloon-cell" role="gridcell" data-r="'+r+'" data-c="'+c+'" data-swatch="'
                  + (el.getAttribute("data-swatch")||"red") + '"><span class="nv-balloon-knot" aria-hidden="true"></span></div>'; } }
            grid.innerHTML = cells; }
          paintMarks(); pointDart(); }

        function cellAt(r,c){ return grid ? grid.querySelector('.nv-balloon-cell[data-r="'+r+'"][data-c="'+c+'"]') : null; }
        // the un-popped balloons as normalized centers {r,c,x,y} for the landing/hit math.
        function targets(){ var out=[]; for (var r=0;r<spec.rows;r++){ for (var c=0;c<spec.cols;c++){
          if (!popped[key(r,c)]) out.push({ r:r, c:c, x:(c+0.5)/spec.cols, y:(r+0.5)/spec.rows }); } } return out; }
        function pointDart(){ if (dartEl) dartEl.style.transform = "rotate(" + aim.toFixed(1) + "deg)"; }
        // finer aim step as the board gains columns — 4×4 rounds need tight aiming to line up a column.
        function aimStep(){ return (2*MAX_ANGLE/spec.cols)/8; }
        function setAim(d){ if (!active) return; var n=aim + d*aimStep(); if (n<-MAX_ANGLE) n=-MAX_ANGLE; if (n>MAX_ANGLE) n=MAX_ANGLE; aim=n; pointDart(); if (charging) highlightTarget(); }

        // fly the dart on a real PARABOLA (rAF) to the target balloon's live on-screen position, in
        // the stage's flat coordinates so it lands accurately over the 3D-tilted board. It arcs up,
        // eases into the target, and SHRINKS as it flies so there's visible distance to the board.
        // `landing` = normalized landing point (for a miss); `cell` = the hit balloon (null on miss).
        // `onArrive` fires on impact so the balloon bursts when the dart lands. Reduced motion is
        // instant.
        function throwDart(power, landing, cell, onArrive){
          var stage = el.querySelector(".nv-balloon-stage");
          if (!stage || !dartEl || !document.createElement || !stage.getBoundingClientRect || !window.requestAnimationFrame){ if (onArrive) onArrive(); return; }
          var sRect = stage.getBoundingClientRect(), dRect = dartEl.getBoundingClientRect();
          var sx = dRect.left + dRect.width/2 - sRect.left, sy = dRect.top - sRect.top;   // launch = dart tip
          var ex, ey;
          if (cell){ var cr = cell.getBoundingClientRect(); ex = cr.left+cr.width/2 - sRect.left; ey = cr.top+cr.height/2 - sRect.top; }
          else if (grid){ var gr = grid.getBoundingClientRect(); ex = gr.left + landing.x*gr.width - sRect.left; ey = gr.top + (1-landing.y)*gr.height - sRect.top; }
          else { ex = sx; ey = sy - 120; }
          var proj = document.createElement("div"); proj.className = "nv-balloon-proj";
          var inner = document.createElement("div"); inner.className = "nv-balloon-proj-dart"; proj.appendChild(inner);
          stage.appendChild(proj);
          if (dartEl) dartEl.style.visibility = "hidden";               // the loaded dart has left the launcher
          var dist = Math.sqrt((ex-sx)*(ex-sx)+(ey-sy)*(ey-sy)), H = Math.max(46, dist*0.34);  // arc peak height
          var D = reduceMotion ? 0 : 500;
          function finish(){ if (proj.parentNode) proj.parentNode.removeChild(proj); if (dartEl){ dartEl.style.visibility=""; pointDart(); } if (onArrive) onArrive(); }
          if (D<=0){ finish(); return; }
          var t0 = nowFn(), px=sx, py=sy;
          (function frame(){ var u=(nowFn()-t0)/D; if (u>1) u=1;
            var ue = 1-(1-u)*(1-u);                                     // easeOutQuad — decelerate into the target
            var x = sx + (ex-sx)*ue, y = sy + (ey-sy)*ue - 4*H*u*(1-u); // lerp + parabolic arc
            var s = 1 - 0.34*u;                                         // shrink into the distance
            var ang = Math.atan2(y-py, x-px)*180/Math.PI + 90;          // nose along the flight tangent
            proj.style.transform = "translate("+x.toFixed(1)+"px,"+y.toFixed(1)+"px) scale("+s.toFixed(3)+")";
            inner.style.transform = "rotate("+ang.toFixed(1)+"deg)";
            px=x; py=y;
            if (u<1){ requestAnimationFrame(frame); } else { finish(); } })(); }

        function clearOpts(p){ Array.prototype.slice.call(p.querySelectorAll(".nv-balloon-opt")).forEach(function(o){
          o.classList.remove("nv-balloon-right","nv-balloon-wrong"); var r=o.querySelector("input"); if(r){ r.checked=false; r.disabled=false; } }); }
        function showPanel(p){ panels.forEach(function(x){ x.hidden = true; }); curPanel = p; if (!p) return;
          clearOpts(p); var s = p.querySelector(".nv-balloon-submit"); if (s){ s.disabled=false; s.textContent="Submit answer"; }
          p.hidden = false; }
        function nextQuestion(){ if (!panels.length) return;
          showPanel(panels[Math.floor(Math.random()*panels.length)]); }   // random draw from the whole block

        function enableControls(on){ [throwBtn, aimL, aimR].forEach(function(btn){ if (btn) btn.disabled = !on; }); }
        // light up the SPECIFIC balloon the current aim + live power would hit (nearest within the
        // tolerance) so the learner aims at an individual balloon; none lit = currently a miss.
        function highlightTarget(){ if (!grid) return;
          var lp = aimLanding(aim, pwr, MAX_ANGLE), t = hitTest(lp.x, lp.y, targets(), spec.hitR);
          Array.prototype.slice.call(grid.querySelectorAll(".nv-balloon-cell")).forEach(function(cell){
            var c=parseInt(cell.getAttribute("data-c"),10), r=parseInt(cell.getAttribute("data-r"),10);
            cell.classList.toggle("nv-balloon-targeted", charging && !!t && t.r===r && t.c===c); }); }
        function clearTarget(){ if (!grid) return;
          Array.prototype.slice.call(grid.querySelectorAll(".nv-balloon-targeted")).forEach(function(c){ c.classList.remove("nv-balloon-targeted"); }); }
        function startCharge(){ if (!active || charging) return; charging = true;
          var t0 = nowFn();
          (function frame(){ if (!charging) return; pwr = powerAt(nowFn()-t0, POWER_CYCLE);
            if (fillEl) fillEl.style.height = pwr + "%";
            if (dartEl) dartEl.style.transform = "rotate(" + aim.toFixed(1) + "deg) scaleY(" + (1 + pwr/150).toFixed(3) + ")";  // dart cocks taller as it charges
            highlightTarget();
            rafId = window.requestAnimationFrame ? requestAnimationFrame(frame) : 0; })(); }
        function stopCharge(){ charging = false; if (rafId && window.cancelAnimationFrame) cancelAnimationFrame(rafId); rafId = 0; clearTarget(); }

        function earnThrow(){ if (curPanel) curPanel.hidden = true; active = true;
          enableControls(true); pointDart(); if (grid) try { grid.focus(); } catch(e){}
          say(true, "Dart ready — aim with ← →, hold Space to charge (it speeds up!), release to throw."); }
        // DONE after DONE_POPS pops (not the whole board): the block completes so the learner may
        // move on, but the game stays fully playable if they want to keep going. Never a grade, no
        // failure state — unlimited darts, so 2 pops is always eventually reachable (Easy = big
        // targets). Below the threshold the block simply isn't marked complete yet.
        function record(){ if (totalPops >= DONE_POPS) bpSeen["bp"+i] = { ok:1, got:totalPops, max:darts }; }

        function levelUp(){ round++; buildBoard();
          if (CELEB) celebrate("level"); say(true, "Board cleared! Round " + (round+1) + " — a bigger 4×4 board; aim tight!"); }

        function fire(){ if (!active || !charging) { stopCharge(); return; } stopCharge();
          active = false; enableControls(false); darts++;
          var lp = aimLanding(aim, pwr, MAX_ANGLE);
          var t = hitTest(lp.x, lp.y, targets(), spec.hitR);       // nearest un-popped balloon within tolerance
          var cell = t ? cellAt(t.r, t.c) : null, hit = !!cell;
          if (hit){ popped[key(t.r,t.c)] = 1; poppedN++; totalPops++; showCount(); }   // score now; burst on impact
          throwDart(pwr, lp, cell, function(){                      // the dart has ARRIVED
            if (hit){ cell.classList.add("nv-balloon-gone");
              say(true, (fbOk ? fbOk + " " : "Pop! ") + "Popped " + totalPops
                + (totalPops === DONE_POPS ? " — that's enough to finish. Keep popping for fun, or move on!" : "."));
              if (poppedN >= spec.cols*spec.rows){ if (window.setTimeout) window.setTimeout(levelUp, 450); else levelUp(); }
            } else { say(false, (fbNo ? fbNo + " " : "Missed — aim and power were off. ") + "Line up another dart."); } });
          if (fillEl) fillEl.style.height = "0%";
          record(); if (restart) restart.hidden = false;
          nextQuestion(); save(); updateProgress(); }

        panels.forEach(function(p){ var submit = p.querySelector(".nv-balloon-submit"); if (!submit) return;
          submit.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; if (p.hidden) return;
            var opts = Array.prototype.slice.call(p.querySelectorAll(".nv-balloon-opt"));
            var chosen = -1; opts.forEach(function(o, oi){ var r=o.querySelector("input"); if (r && r.checked) chosen = oi; });
            if (chosen < 0){ say(false, "Pick an answer to earn your dart."); return; }
            var ans = parseInt(p.getAttribute("data-answer") || "0", 10);
            if (chosen === ans){ if (opts[chosen]) opts[chosen].classList.add("nv-balloon-right"); earnThrow(); }
            else { if (opts[chosen]) opts[chosen].classList.add("nv-balloon-wrong"); if (opts[ans]) opts[ans].classList.add("nv-balloon-right");
              say(false, "Not quite — the highlighted answer is correct. Choose it to earn your dart."); }   // stays open: always earnable
          }); });

        // pointer path (mouse/touch): aim buttons click; Charge button hold (pointerdown→up). The
        // Charge button has NO click handler, so a keyboard Space (handled at block level) can't
        // double-fire through it.
        if (aimL) aimL.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; setAim(-1); });
        if (aimR) aimR.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; setAim(1); });
        if (throwBtn){
          throwBtn.addEventListener("pointerdown", function(ev){ if (ev && ev.isTrusted === false) return; if (ev.preventDefault) ev.preventDefault(); startCharge(); });
          throwBtn.addEventListener("pointerup", function(ev){ if (ev && ev.isTrusted === false) return; fire(); });
          throwBtn.addEventListener("pointerleave", function(){ if (charging) fire(); });
          throwBtn.addEventListener("pointercancel", function(){ if (charging) fire(); });
        }
        // keyboard path (block-scoped: only fires while focus is inside this game).
        el.addEventListener("keydown", function(ev){ if (ev && ev.isTrusted === false) return; if (!active) return;
          var k = ev.key;
          if (k === "ArrowLeft"){ ev.preventDefault(); setAim(-1); }
          else if (k === "ArrowRight"){ ev.preventDefault(); setAim(1); }
          else if (k === " " || k === "Spacebar" || k === "Space"){ ev.preventDefault(); if (!ev.repeat) startCharge(); } });
        el.addEventListener("keyup", function(ev){ if (ev && ev.isTrusted === false) return;
          var k = ev.key; if (k === " " || k === "Spacebar" || k === "Space"){ ev.preventDefault(); if (charging) fire(); } });

        diffBtns.forEach(function(btn){ btn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return;
          var d = parseInt(btn.getAttribute("data-diff") || "1", 10); diff = d>0?d:0; round = 0;   // new difficulty → back to a first-round 3×3
          diffBtns.forEach(function(b){ var on = b===btn; b.classList.toggle("nv-balloon-diff-on", on); b.setAttribute("aria-pressed", on?"true":"false"); });
          stopCharge(); if (fillEl) fillEl.style.height = "0%"; buildBoard(); showCount();
          say(true, "Difficulty set. Answer a question to earn a dart."); }); });

        if (restart) restart.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return;
          totalPops = 0; darts = 0; round = 0; active = false; stopCharge(); if (fillEl) fillEl.style.height = "0%";
          buildBoard(); showCount(); enableControls(false); restart.hidden = true;
          say(true, "Fresh run — answer a question to earn a dart."); nextQuestion(); });

        buildBoard(); showCount(); enableControls(false); nextQuestion();   // initial paint

        // Resume: only the tally + level survive byte pressure. Re-show them, mark complete, and
        // leave the game replayable (a fresh board is drawn) — mirrors __dunkRestore's re-lock.
        el.__balloonRestore = function(rec){ totalPops = (rec && rec.got) || 0; darts = (rec && rec.max) || 1;
          record(); buildBoard(); showCount(); active = false; stopCharge(); if (fillEl) fillEl.style.height = "0%";
          enableControls(false); if (restart) restart.hidden = false;
          say(true, "You completed this activity — " + totalPops + " balloon" + (totalPops===1?"":"s") + " popped. Play again to beat it.");
          nextQuestion(); };
      });

      /* shootingGallery — FORMATIVE arcade reward game (James, 2026-07-27; the THIRD shell in the
         arcade library alongside dunkBooth + balloonPop). The distinct mechanic is MOVING TARGETS:
         answer a randomly-drawn MCQ to EARN 3 shots (SHOTS_PER_ANSWER), slide the crosshair left/right
         (← → or the ◀ ▶ buttons), and press Space (or Fire) to shoot whichever lane's target is under
         it — you must LEAD the sliding target, which can also REVERSE direction at random (FLIP_RATE),
         so leading is reactive, not memorized. A hit clears that lane; clearing every lane advances a difficulty
         LEVEL (galleryLevel: more lanes + faster targets + a tighter hit window). No win/lose —
         completion is engagement (one shot FIRED, hit OR miss), so timing is never essential (WCAG
         2.2.1) and there is no fail state; the hit tally is motivational only (sgSeen never enters
         gradedScore()/xpTotals(); no data-obj). Under prefers-reduced-motion the targets slide
         slowly. A wrong answer reveals the correct option and stays open so a shot is always earnable
         (no soft-lock). Keyboard is block-scoped (arrows/Space, preventDefault so they don't scroll
         the page); the on-screen buttons drive the pointer path (the Fire button's click is the
         pointer path, and the block-level Space is guarded so they never double-fire). All
         interactions are isTrusted-guarded (anti-cheat). */
      function setupPhysicsGallery(el, i){
        var physics=window.CarnivalPhysics,DEFAULT_DIFF=1,SHOTS_PER_ANSWER=3,FLIP_RATE=.4;
        el.classList.add("nv-physics-mode");
        var stage=el.querySelector(".nv-gallery-scene"),lanesEl=el.querySelector(".nv-gallery-lanes");
        var pouch=el.querySelector(".nv-gallery-pouch"),guide=el.querySelector(".nv-gallery-guide");
        var bandL=el.querySelector(".nv-gallery-band-left"),bandR=el.querySelector(".nv-gallery-band-right");
        var fireBtn=el.querySelector(".nv-gallery-fire"),aimInput=el.querySelector(".nv-gallery-aim");
        var powerInput=el.querySelector(".nv-gallery-power"),aimL=el.querySelector(".nv-gallery-aim-left");
        var aimR=el.querySelector(".nv-gallery-aim-right"),aimUp=el.querySelector(".nv-gallery-aim-up");
        var aimDown=el.querySelector(".nv-gallery-aim-down"),diffBtns=Array.prototype.slice.call(el.querySelectorAll(".nv-gallery-diff"));
        var restart=el.querySelector(".nv-gallery-restart"),countEl=el.querySelector(".nv-gallery-count");
        var levelEl=el.querySelector(".nv-gallery-level"),fb=el.querySelector(".nv-gallery-fb");
        var panels=Array.prototype.slice.call(el.querySelectorAll(".nv-gallery-panel")),quarry=el.getAttribute("data-quarry")||"target";
        var fbOk=fb?(fb.getAttribute("data-fb-correct")||""):"",fbNo=fb?(fb.getAttribute("data-fb-incorrect")||""):"";
        var round=0,diff=DEFAULT_DIFF,spec=galleryLevel(round,diff),ducks=[],aliveN=0,hits=0,shots=0,shotsLeft=0;
        var active=false,inFlight=false,curPanel=null,baseOrigin=null,motionRaf=0,lastT=0,run=null;
        function origin(){if(baseOrigin)return baseOrigin;var sr=stage.getBoundingClientRect(),pr=pouch.getBoundingClientRect();
          return{x:pr.left+pr.width/2-sr.left,y:pr.top+pr.height/2-sr.top};}
        function captureOrigin(){baseOrigin=null;baseOrigin=origin();}
        function say(ok,msg){if(!fb)return;fb.classList.remove("ok","no");fb.classList.add("show",ok?"ok":"no");fb.textContent=msg;}
        function count(){if(countEl)countEl.textContent=String(hits);if(levelEl)levelEl.textContent=String(round+1);}
        function enable(on){[pouch,fireBtn,aimInput,powerInput,aimL,aimR,aimUp,aimDown].forEach(function(c){if(c)c.disabled=!on;});
          if(stage)stage.classList.toggle("nv-physics-armed",!!on);}
        function band(elm,ax,ay,tx,ty){if(!elm)return;var dx=tx-ax,dy=ty-ay;
          elm.style.left=ax.toFixed(1)+"px";elm.style.top=ay.toFixed(1)+"px";elm.style.width=Math.sqrt(dx*dx+dy*dy).toFixed(1)+"px";
          elm.style.transform="rotate("+Math.atan2(dy,dx)+"rad)";}
        function bands(p){var o=origin(),tx=o.x+p.x,ty=o.y+p.y;band(bandL,o.x-25,o.y-7,tx,ty);band(bandR,o.x+25,o.y-7,tx,ty);}
        function reset(){if(pouch){pouch.hidden=false;pouch.style.transform="";}if(guide)guide.innerHTML="";if(baseOrigin)bands({x:0,y:0});}
        function preview(p,sync){if(!pouch||!guide)return;var v=physics.pullVelocity("gallery",p,0);
          pouch.style.transform="translate("+p.x.toFixed(1)+"px,"+p.y.toFixed(1)+"px) rotate("+(p.x*.45).toFixed(1)+"deg)";
          bands(p);physics.paintTrajectory(stage,guide,"gallery",origin(),v);
          if(sync){var c=physics.controlsForPull("gallery",p);aimInput.value=String(Math.round(c.angle));powerInput.value=String(Math.round(c.power));}}
        function preset(){if(active&&!inFlight)preview(physics.aimedPull("gallery",aimInput.value,powerInput.value),false);}
        function clear(p){Array.prototype.slice.call(p.querySelectorAll(".nv-gallery-opt")).forEach(function(o){
          o.classList.remove("nv-gallery-right","nv-gallery-wrong");var r=o.querySelector("input");if(r){r.checked=false;r.disabled=false;}});}
        function show(p){panels.forEach(function(x){x.hidden=true;});curPanel=p;if(!p)return;clear(p);p.hidden=false;}
        function next(){if(panels.length)show(panels[Math.floor(Math.random()*panels.length)]);}
        function laneMap(){var map={};Array.prototype.slice.call(lanesEl.querySelectorAll(".nv-gallery-lane")).forEach(function(l){map[l.getAttribute("data-row")]=l;});return map;}
        function speedMult(row,idx){return .7+.15*(((idx*7+row*3)%5));}
        function build(){spec=galleryLevel(round,diff);ducks=[];aliveN=0;lanesEl.innerHTML='<div class="nv-gallery-lane" role="row" data-row="1"></div><div class="nv-gallery-lane" role="row" data-row="0"></div>';
          var map=laneMap();for(var row=0;row<2;row++){for(var k=0;k<spec.perRow;k++){var x=(k+.5)/spec.perRow,de=document.createElement("div");
            de.className="nv-gallery-target";de.setAttribute("data-quarry",quarry);de.setAttribute("role","gridcell");de.setAttribute("aria-label","Moving target");
            de.style.left=(x*100).toFixed(2)+"%";map[""+row].appendChild(de);
            ducks.push({row:row,idx:k,el:de,dir:k%2? -1:1,speed:spec.rows[row].speed*speedMult(row,k),x:x,alive:true});aliveN++;}}}
        function motion(){var now=(window.performance&&performance.now)?performance.now():Date.now(),dt=lastT?(now-lastT)/1000:0;lastT=now;if(dt>.1)dt=.1;
          ducks.forEach(function(d){if(!d.alive)return;var sp=reduceMotion?d.speed*.35:d.speed;if(!reduceMotion&&Math.random()<FLIP_RATE*dt)d.dir=-d.dir;
            d.x+=d.dir*sp*dt;if(d.x<=0){d.x=0;d.dir=1;}else if(d.x>=1){d.x=1;d.dir=-1;}
            d.el.style.left=(d.x*100).toFixed(2)+"%";d.el.classList.toggle("nv-gallery-facing-left",d.dir<0);});
          motionRaf=requestAnimationFrame(motion);}
        function startMotion(){if(!motionRaf&&window.requestAnimationFrame){lastT=0;motionRaf=requestAnimationFrame(motion);}}
        function descriptors(){var out=[];ducks.forEach(function(d){if(!d.alive)return;var t=physics.elementTarget(stage,d.el,d.row+"_"+d.idx,"circle",-2,true);t.duck=d;out.push(t);});return out;}
        function record(){if(shots>=1)sgSeen["sg"+i]={ok:1,got:hits,max:shots};}
        function earn(){if(curPanel)curPanel.hidden=true;active=true;shotsLeft=SHOTS_PER_ANSWER;reset();captureOrigin();enable(true);preset();
          if(pouch)try{pouch.focus();}catch(e){}say(true,shotsLeft+" shots ready. Drag backward in the field and release, or use the Aim and Power controls.");}
        function levelUp(){round++;build();count();say(true,"Targets cleared. Level "+(round+1)+" moves faster.");}
        function finish(hit,flight){inFlight=false;if(flight&&flight.parentNode)flight.parentNode.removeChild(flight);reset();
          if(hit&&hit.duck&&hit.duck.alive){hit.duck.alive=false;aliveN--;hit.duck.el.classList.add("nv-gallery-hit");hits++;count();
            say(true,(fbOk?fbOk+" ":"Hit! ")+"Targets down: "+hits+"."+ (shotsLeft?" "+shotsLeft+" shots left.":""));
            if(aliveN<=0){if(window.setTimeout)setTimeout(levelUp,450);else levelUp();}
          }else say(false,(fbNo?fbNo+" ":"Missed. ")+"Lead the moving target and adjust the arc."+ (shotsLeft?" "+shotsLeft+" shots left.":""));
          record();if(restart)restart.hidden=false;save();updateProgress();
          if(shotsLeft>0){active=true;captureOrigin();enable(true);preset();}else{active=false;enable(false);next();}}
        function launch(velocity){if(!active||inFlight||shotsLeft<=0)return;active=false;inFlight=true;enable(false);shotsLeft--;shots++;
          var o=origin(),flight=pouch.cloneNode(false);flight.disabled=true;flight.classList.add("nv-physics-flight");stage.appendChild(flight);
          if(guide)guide.innerHTML="";bands({x:0,y:0});pouch.hidden=true;
          record();save();updateProgress();
          run=physics.launch({profile:"gallery",stage:stage,origin:o,velocity:velocity,reducedMotion:reduceMotion,targets:descriptors(),
            onFrame:function(pos){flight.style.left="0";flight.style.top="0";flight.style.bottom="auto";
              flight.style.transform="translate("+(pos.x-11).toFixed(1)+"px,"+(pos.y-11).toFixed(1)+"px) rotate("+(pos.angle*180/Math.PI).toFixed(1)+"deg)";},
            onComplete:function(result){finish(result.hit,flight);}});}
        physics.bindPull({profile:"gallery",stage:stage,surface:stage,handle:pouch,origin:origin,delta:true,
          enabled:function(){return active&&!inFlight;},onDragState:function(on){stage.classList.toggle("nv-physics-dragging",on);},
          onPreview:function(p){preview(p,true);},onCancel:preset,onRelease:function(p,v){launch(v);}});
        panels.forEach(function(p){var submit=p.querySelector(".nv-gallery-submit");if(!submit)return;
          submit.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;if(p.hidden)return;
            var opts=Array.prototype.slice.call(p.querySelectorAll(".nv-gallery-opt")),chosen=-1;
            opts.forEach(function(o,oi){var r=o.querySelector("input");if(r&&r.checked)chosen=oi;});
            if(chosen<0){say(false,"Pick an answer to earn your shots.");return;}var ans=parseInt(p.getAttribute("data-answer")||"0",10);
            if(chosen===ans){if(opts[chosen])opts[chosen].classList.add("nv-gallery-right");earn();}
            else{if(opts[chosen])opts[chosen].classList.add("nv-gallery-wrong");if(opts[ans])opts[ans].classList.add("nv-gallery-right");
              say(false,"Not quite. Choose the highlighted answer to earn your shots.");}});});
        function aim(delta){if(!active)return;aimInput.value=String(Math.max(+aimInput.min,Math.min(+aimInput.max,+aimInput.value+delta)));preset();}
        function power(delta){if(!active)return;powerInput.value=String(Math.max(+powerInput.min,Math.min(+powerInput.max,+powerInput.value+delta)));preset();}
        if(aimL)aimL.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;aim(4);});
        if(aimR)aimR.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;aim(-4);});
        if(aimUp)aimUp.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;power(5);});
        if(aimDown)aimDown.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;power(-5);});
        if(fireBtn)fireBtn.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;
          launch(physics.aimedVelocity("gallery",aimInput.value,powerInput.value));});
        if(aimInput)aimInput.addEventListener("input",preset);
        if(powerInput)powerInput.addEventListener("input",preset);
        window.addEventListener("resize",function(){if(active&&!inFlight){reset();captureOrigin();preset();}});
        diffBtns.forEach(function(btn){btn.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;
          diff=Math.max(0,+btn.getAttribute("data-diff")||0);round=0;diffBtns.forEach(function(b){var on=b===btn;b.classList.toggle("nv-gallery-diff-on",on);b.setAttribute("aria-pressed",on?"true":"false");});
          active=false;shotsLeft=0;enable(false);reset();build();count();say(true,"Difficulty set. Answer a question to earn your shots.");});});
        if(restart)restart.addEventListener("click",function(ev){if(ev&&ev.isTrusted===false)return;if(run)run.stop("restart");
          hits=0;shots=0;shotsLeft=0;round=0;active=false;inFlight=false;build();count();enable(false);reset();restart.hidden=true;
          say(true,"Fresh run. Answer a question to earn your shots.");next();});
        build();count();enable(false);reset();next();startMotion();
        el.__galleryRestore=function(rec){hits=(rec&&rec.got)||0;shots=(rec&&rec.max)||1;shotsLeft=0;record();build();count();active=false;inFlight=false;
          enable(false);reset();if(restart)restart.hidden=false;say(true,"You completed this activity — "+hits+" target"+(hits===1?"":"s")+" hit. Play again to beat it.");next();startMotion();};
      }
      galleries.forEach(function(el, i){
        if(window.CarnivalPhysics){setupPhysicsGallery(el,i);return;}
        var DEFAULT_DIFF = 1;                                   // Standard by default (chooser can change)
        var AIM_STEP = 0.04;                                    // crosshair move per ← → step (normalized)
        var SHOTS_PER_ANSWER = 3;                               // each correct answer earns THIS many shots (James, 2026-07-27)
        var FLIP_RATE = 0.4;                                    // avg RANDOM direction reversals/sec per duck (0 = never; off under reduced motion)
        var reduceMotion = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
        var lanesEl  = el.querySelector(".nv-gallery-lanes");
        var sceneEl  = el.querySelector(".nv-gallery-scene");
        var reticleEl= el.querySelector(".nv-gallery-reticle");
        var gunEl    = el.querySelector(".nv-gallery-gun");
        var fireBtn  = el.querySelector(".nv-gallery-fire");
        var aimL     = el.querySelector(".nv-gallery-aim-left");
        var aimR     = el.querySelector(".nv-gallery-aim-right");
        var aimUp    = el.querySelector(".nv-gallery-aim-up");
        var aimDown  = el.querySelector(".nv-gallery-aim-down");
        var diffBtns = Array.prototype.slice.call(el.querySelectorAll(".nv-gallery-diff"));
        var restart  = el.querySelector(".nv-gallery-restart");
        var countEl  = el.querySelector(".nv-gallery-count");
        var levelEl  = el.querySelector(".nv-gallery-level");
        var fb       = el.querySelector(".nv-gallery-fb");
        var panels   = Array.prototype.slice.call(el.querySelectorAll(".nv-gallery-panel"));
        var quarry   = el.getAttribute("data-quarry") || "duck";
        var fbOk = fb ? (fb.getAttribute("data-fb-correct") || "") : "";
        var fbNo = fb ? (fb.getAttribute("data-fb-incorrect") || "") : "";
        var ROW_LABEL = { 0: "bottom", 1: "top" };

        var round = 0, diff = DEFAULT_DIFF, spec = galleryLevel(round, diff);
        var reticleX = 0.5, reticleRow = 0;                    // crosshair X (0..1) + aimed row (0 bottom / 1 top)
        var ducks = [], aliveN = 0, hits = 0, shots = 0, shotsLeft = 0;   // ducks = [{row,idx,el,phase,dir,speed,x,alive}]; shotsLeft = shots remaining on the current answer
        var active = false, curPanel = null, rafId = 0, t0 = 0, lastT = 0;

        function nowFn(){ return (window.performance && performance.now) ? performance.now() : Date.now(); }
        function showCount(){ if (countEl) countEl.textContent = String(hits); if (levelEl) levelEl.textContent = String(round+1); }
        function say(ok, msg){ if (!fb) return; fb.classList.remove("ok","no"); fb.classList.add("show", ok?"ok":"no"); fb.textContent = msg; }

        function laneElByRow(){ var map = {};
          if (lanesEl){ Array.prototype.slice.call(lanesEl.querySelectorAll(".nv-gallery-lane")).forEach(function(l){ map[l.getAttribute("data-row")] = l; }); }
          return map; }

        // move the crosshair into the AIMED row (so its vertical position is that water row's center)
        // and to reticleX across it; highlight the aimed lane; tilt the gun toward the aim point.
        function positionReticle(){ var laneEls = laneElByRow(), lane = laneEls["" + reticleRow];
          if (reticleEl && lane){ if (reticleEl.parentNode !== lane) lane.appendChild(reticleEl);
            reticleEl.style.left = (reticleX*100).toFixed(2) + "%"; reticleEl.style.top = "50%"; }
          Object.keys(laneEls).forEach(function(rr){ if (laneEls[rr]) laneEls[rr].classList.toggle("nv-gallery-aimed", (+rr) === reticleRow); });
          if (gunEl){ var ang = (reticleX-0.5)*40 + (reticleRow===1 ? -7 : 5);   // point at X, a touch higher for the top row
            gunEl.style.transform = "translateX(-50%) rotate(" + ang.toFixed(1) + "deg)"; } }

        // each duck gets its OWN speed: a deterministic 0.7..1.3 spread of the row's base speed keyed
        // on (row, index) — so ducks in a row move at different speeds (and resume identically, no RNG).
        function duckSpeedMult(row, idx){ return 0.7 + 0.15*(((idx*7 + row*3) % 5)); }

        function buildLanes(){ spec = galleryLevel(round, diff); reticleX = 0.5; reticleRow = 0; ducks = []; aliveN = 0;
          if (lanesEl){ var h = "";
            for (var ri = 0; ri < 2; ri++){ var r = 1 - ri;   // DOM order top→bottom: row 1 (top) first, row 0 (bottom) second
              h += '<div class="nv-gallery-lane" role="row" data-row="' + r + '"></div>'; }
            lanesEl.innerHTML = h; }
          var laneEls = laneElByRow();
          for (var row = 0; row < 2; row++){ var rowSpec = spec.rows[row], lane = laneEls["" + row];
            for (var k = 0; k < spec.perRow; k++){
              var phase = ((k*0.31 + row*0.17) % 1), m0 = ((phase % 2) + 2) % 2;
              var dk = { row: row, idx: k, el: null, phase: phase, dir: (k % 2 === 0 ? 1 : -1),
                         speed: rowSpec.speed * duckSpeedMult(row, k), x: (m0 <= 1 ? m0 : 2 - m0), alive: true };
              if (lane && document.createElement){ var de = document.createElement("div");
                de.className = "nv-gallery-target"; de.setAttribute("data-quarry", quarry);
                de.setAttribute("role", "gridcell"); de.setAttribute("aria-label", "Target");
                de.style.left = (dk.x*100).toFixed(2) + "%"; lane.appendChild(de); dk.el = de; }
              ducks.push(dk); aliveN++;
            } }
          positionReticle(); }

        function aliveDucks(){ var out = [];   // live ducks as {row, idx, x} for the hit math
          for (var d = 0; d < ducks.length; d++){ if (ducks[d].alive) out.push({ row: ducks[d].row, idx: ducks[d].idx, x: ducks[d].x }); } return out; }
        function duckAt(row, idx){ for (var d = 0; d < ducks.length; d++){ if (ducks[d].row === row && ducks[d].idx === idx) return ducks[d]; } return null; }

        // continuous rAF motion: every live duck slides in a 0↔1 bounce at ITS OWN speed (reduced
        // motion = slower). Ducks move even before a shot is earned, so the learner can read the
        // rhythm and LEAD; the duck under the crosshair IN THE AIMED ROW is highlighted while a shot
        // is loaded. Guarded so a no-DOM/no-rAF environment (node) never runs it.
        // frame-delta integration (not a closed-form t0 sweep) so ducks can REVERSE mid-lane: every
        // live duck advances dir*speed*dt each frame, BOUNCES off the 0/1 walls, and — under normal
        // motion — randomly flips direction at ~FLIP_RATE/sec (Poisson-ish per frame), so leading a
        // duck means reacting, not memorizing a fixed sweep (James, 2026-07-27). Reduced motion keeps
        // the slow, PREDICTABLE bounce (no random flips) for accessibility. dt is clamped so a
        // backgrounded tab (huge gap) never teleports the flock.
        function motion(){ var now = nowFn(); var dt = lastT ? (now - lastT)/1000 : 0; lastT = now;
          if (dt > 0.1) dt = 0.1;
          for (var d = 0; d < ducks.length; d++){ var dk = ducks[d]; if (!dk.alive) continue;
            var sp = reduceMotion ? dk.speed*0.4 : dk.speed;
            if (!reduceMotion && FLIP_RATE > 0 && Math.random() < FLIP_RATE*dt) dk.dir = -dk.dir;  // random reversal
            dk.x += dk.dir * sp * dt;
            if (dk.x <= 0){ dk.x = 0; dk.dir = 1; } else if (dk.x >= 1){ dk.x = 1; dk.dir = -1; }   // bounce off the walls
            if (dk.el){ dk.el.style.left = (dk.x*100).toFixed(2) + "%";
              dk.el.classList.toggle("nv-gallery-facing-left", dk.dir < 0);   // flip the sprite to face travel
              var lit = active && dk.row === reticleRow && Math.abs(dk.x - reticleX) <= spec.rows[reticleRow].hitR;
              dk.el.classList.toggle("nv-gallery-under", lit); } }
          rafId = window.requestAnimationFrame ? requestAnimationFrame(motion) : 0; }
        function startMotion(){ if (rafId || !window.requestAnimationFrame) return; t0 = lastT = nowFn(); rafId = requestAnimationFrame(motion); }

        function enableControls(on){ [fireBtn, aimL, aimR, aimUp, aimDown].forEach(function(b){ if (b) b.disabled = !on; }); }
        function setAim(dx){ if (!active) return; reticleX += dx*AIM_STEP; if (reticleX<0) reticleX=0; if (reticleX>1) reticleX=1; positionReticle(); }
        function setRow(r){ if (!active) return; reticleRow = r>0?1:0; positionReticle();
          say(true, "Aiming the " + ROW_LABEL[reticleRow] + " row" + (reticleRow===1 ? " (faster — lead more!)" : "") + "."); }

        // a MISS leaves a splash where the shot landed (the crosshair point in the aimed row), so the
        // learner can see where they hit; it fades out and removes itself.
        function splashAt(x, row){ var laneEls = laneElByRow(), lane = laneEls["" + row];
          if (!lane || !document.createElement) return;
          var s = document.createElement("div"); s.className = "nv-gallery-splash"; s.setAttribute("aria-hidden", "true");
          s.style.left = (x*100).toFixed(2) + "%"; lane.appendChild(s);
          if (window.setTimeout) window.setTimeout(function(){ if (s.parentNode) s.parentNode.removeChild(s); }, 900); }

        function clearOpts(p){ Array.prototype.slice.call(p.querySelectorAll(".nv-gallery-opt")).forEach(function(o){
          o.classList.remove("nv-gallery-right","nv-gallery-wrong"); var r=o.querySelector("input"); if(r){ r.checked=false; r.disabled=false; } }); }
        function showPanel(p){ panels.forEach(function(x){ x.hidden = true; }); curPanel = p; if (!p) return;
          clearOpts(p); var s = p.querySelector(".nv-gallery-submit"); if (s){ s.disabled=false; s.textContent="Submit answer"; }
          p.hidden = false; }
        function nextQuestion(){ if (!panels.length) return;
          showPanel(panels[Math.floor(Math.random()*panels.length)]); }   // random draw from the whole block

        function earnShot(){ if (curPanel) curPanel.hidden = true; active = true; shotsLeft = SHOTS_PER_ANSWER; enableControls(true);
          if (lanesEl) try { lanesEl.focus(); } catch(e){}
          say(true, shotsLeft + " shots ready — ← → to aim, ↑ ↓ to switch rows, Space to fire. Lead the moving duck!"); }

        // DONE on the FIRST shot fired (hit OR miss) — the block completes so the learner may move
        // on, but the game stays fully playable. Never a grade, no failure state.
        function record(){ if (shots >= 1) sgSeen["sg"+i] = { ok:1, got:hits, max:shots }; }

        function levelUp(){ round++; buildLanes();
          if (typeof CELEB !== "undefined" && CELEB) celebrate("level");
          say(true, "Flock cleared! Level " + (round+1) + " — " + spec.perRow + " ducks per row, faster and tighter."); }

        // one Fire spends ONE of the shots earned by the last correct answer. While shots remain the
        // learner keeps firing (re-aim + fire again, no new question); only when the magazine is empty
        // does a fresh question appear to earn the next 3. Completion still fires on the FIRST shot.
        function fire(){ if (!active || shotsLeft <= 0) return; shotsLeft--; shots++;
          if (reticleEl){ reticleEl.classList.add("nv-gallery-firing");
            if (window.setTimeout) window.setTimeout(function(){ if (reticleEl) reticleEl.classList.remove("nv-gallery-firing"); }, 220); }
          var rowSpec = spec.rows[reticleRow];
          var t = galleryHit(reticleX, reticleRow, aliveDucks(), rowSpec.hitR);   // nearest live duck in the aimed row
          var left = shotsLeft > 0 ? (" " + shotsLeft + " shot" + (shotsLeft===1?"":"s") + " left.") : " Out of shots — answer to earn 3 more.";
          if (t){ var dk = duckAt(t.row, t.idx);
            if (dk){ dk.alive = false; aliveN--;
              if (dk.el){ dk.el.classList.remove("nv-gallery-under"); dk.el.classList.add("nv-gallery-hit"); } }
            hits++; showCount();
            say(true, (fbOk ? fbOk + " " : "Hit! ") + "Ducks down: " + hits + "." + left);
            if (aliveN <= 0){ if (window.setTimeout) window.setTimeout(levelUp, 560); else levelUp(); } }
          else { splashAt(reticleX, reticleRow);
            say(false, (fbNo ? fbNo + " " : "Missed — see the splash? Lead the duck more.") + left); }
          record(); if (restart) restart.hidden = false;
          if (shotsLeft > 0){ save(); updateProgress(); return; }   // still loaded — keep aiming, no new question yet
          active = false; enableControls(false);
          nextQuestion(); save(); updateProgress(); }

        panels.forEach(function(p){ var submit = p.querySelector(".nv-gallery-submit"); if (!submit) return;
          submit.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; if (p.hidden) return;
            var opts = Array.prototype.slice.call(p.querySelectorAll(".nv-gallery-opt"));
            var chosen = -1; opts.forEach(function(o, oi){ var r=o.querySelector("input"); if (r && r.checked) chosen = oi; });
            if (chosen < 0){ say(false, "Pick an answer to earn your shot."); return; }
            var ans = parseInt(p.getAttribute("data-answer") || "0", 10);
            if (chosen === ans){ if (opts[chosen]) opts[chosen].classList.add("nv-gallery-right"); earnShot(); }
            else { if (opts[chosen]) opts[chosen].classList.add("nv-gallery-wrong"); if (opts[ans]) opts[ans].classList.add("nv-gallery-right");
              say(false, "Not quite — the highlighted answer is correct. Choose it to earn your shot."); }   // stays open: always earnable
          }); });

        // pointer path (mouse/touch): aim buttons + the Fire button click.
        if (aimL) aimL.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; setAim(-1); });
        if (aimR) aimR.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; setAim(1); });
        if (aimUp) aimUp.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; setRow(1); });
        if (aimDown) aimDown.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; setRow(0); });
        if (fireBtn) fireBtn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; fire(); });
        // keyboard path (block-scoped: only fires while focus is inside this game).
        el.addEventListener("keydown", function(ev){ if (ev && ev.isTrusted === false) return; if (!active) return;
          var k = ev.key;
          if (k === "ArrowLeft"){ ev.preventDefault(); setAim(-1); }
          else if (k === "ArrowRight"){ ev.preventDefault(); setAim(1); }
          else if (k === "ArrowUp"){ ev.preventDefault(); setRow(1); }
          else if (k === "ArrowDown"){ ev.preventDefault(); setRow(0); }
          else if (k === " " || k === "Spacebar" || k === "Space" || k === "Enter"){ ev.preventDefault(); if (!ev.repeat) fire(); } });

        diffBtns.forEach(function(btn){ btn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return;
          var d = parseInt(btn.getAttribute("data-diff") || "1", 10); diff = d>0?d:0; round = 0;   // new difficulty → back to the first level
          diffBtns.forEach(function(b){ var on = b===btn; b.classList.toggle("nv-gallery-diff-on", on); b.setAttribute("aria-pressed", on?"true":"false"); });
          buildLanes(); showCount(); active = false; shotsLeft = 0; enableControls(false);
          say(true, "Difficulty set. Answer a question to earn your shots."); }); });

        if (restart) restart.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return;
          hits = 0; shots = 0; shotsLeft = 0; round = 0; active = false; buildLanes(); showCount(); enableControls(false); restart.hidden = true;
          say(true, "Fresh run — answer a question to earn your shots."); nextQuestion(); });

        buildLanes(); showCount(); enableControls(false); nextQuestion(); startMotion();   // initial paint + start the ducks sliding

        // Resume: only the tally + level survive byte pressure. Re-show them, mark complete, and
        // leave the game replayable (a fresh flock is drawn) — mirrors __balloonRestore's re-lock.
        el.__galleryRestore = function(rec){ hits = (rec && rec.got) || 0; shots = (rec && rec.max) || 1; shotsLeft = 0;
          record(); buildLanes(); showCount(); active = false; enableControls(false); if (restart) restart.hidden = false;
          say(true, "You completed this activity — " + hits + " duck" + (hits===1?"":"s") + " hit. Play again to beat it.");
          nextQuestion(); startMotion(); };
      });

      /* simulation — operator-authored software-sim walkthrough (SIM Studio; build-1 VIEW).
         Every frame is a real element already in the DOM, so with NO JS the whole ordered
         list is readable (an illustrated numbered walkthrough — graceful degradation). This
         wiring shows one frame at a time, advances on Next OR a click anywhere on the frame
         (the marker is clickable too — James's decision #4), and marks the block complete when
         the learner reaches the LAST frame. FORMATIVE, completion-only: simSeen never enters
         gradedScore()/xpTotals() (no data-obj). No WCAG 2.2.1 time limit — Next is always
         present; `auto` advance (when authored) would be cosmetic on top of it. Clicks are
         isTrusted-guarded (anti-cheat). */
      sims.forEach(function(el, i){
        var frames = Array.prototype.slice.call(el.querySelectorAll(".nv-sim-frame"));
        var nextBtn = el.querySelector(".nv-sim-next");
        var restartBtn = el.querySelector(".nv-sim-restart");
        var counter = el.querySelector(".nv-sim-counter");
        var fb = el.querySelector(".nv-sim-fb");
        var total = frames.length;
        var at = 0;
        // slice-2: overlays ENTER when a frame is shown (staggered by author order) and
        // EXIT on advance; a frame's `data-transition` plays as it enters. Motion is pure
        // CSS driven by state classes — base-visible, so no-JS / reduced-motion degrade to
        // a labelled screenshot. reduced-motion also skips the exit delay.
        var reduceMotion = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
        function complete(){
          if (simSeen["sm"+i]) return;
          simSeen["sm"+i] = { ok:1 };
          if (fb){ fb.classList.add("show","ok"); fb.textContent = "Walkthrough complete."; }
          updateProgress();
        }
        function showAt(idx){
          var p = simProgress(total, idx); at = p.at;
          frames.forEach(function(f, fi){
            f.hidden = (fi !== at);
            f.classList.remove("nv-sim-playing", "nv-sim-exiting");
            var ft = f.getAttribute("data-transition");
            if (ft) f.classList.remove("nv-sim-trans-" + ft);   // strip so re-entry replays
          });
          var cur = frames[at];
          if (cur){
            void cur.offsetWidth;                                // reflow: restart the CSS animations
            cur.classList.add("nv-sim-playing");
            var tr = cur.getAttribute("data-transition");
            if (tr) cur.classList.add("nv-sim-trans-" + tr);
          }
          if (counter) counter.textContent = (at + 1) + " / " + total;
          if (nextBtn) nextBtn.hidden = p.done;
          if (restartBtn) restartBtn.hidden = !p.done;
          if (p.done) complete();
        }
        function advance(){
          if (at >= total - 1) return;
          var cur = frames[at], nx = at + 1;
          if (cur && !reduceMotion){
            cur.classList.add("nv-sim-exiting");                 // overlays play their exit, then swap
            setTimeout(function(){ showAt(nx); }, 220);
          } else {
            showAt(nx);
          }
        }
        if (nextBtn) nextBtn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; advance(); });
        if (restartBtn) restartBtn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; showAt(0); });
        frames.forEach(function(f){
          f.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;
            // don't hijack a real control inside a content frame (link/button/field)
            if (ev.target && ev.target.closest && ev.target.closest("a,button,input,textarea,select")) return;
            advance();
          });
        });
        // Resume: the sm rung only records "completed" (byte pressure drops the frame index),
        // so a resumed sim jumps to the last frame and re-marks complete.
        el.__simRestore = function(){ simSeen["sm"+i] = { ok:1 }; showAt(total - 1); };
        if (total) showAt(0);
      });

      /* memoryMatch — FORMATIVE concentration game (James, 2026-07-10). The cards are real
         <button>s already in the DOM carrying their face text; with NO JS the faces show as a
         readable study list. This wiring switches the block into game mode (adds nv-mm-live so
         CSS hides the faces behind a "?" back), then handles flip → match/no-match → completion.
         Clicks are isTrusted-guarded (anti-cheat). Completion-only: mmSeen never enters
         gradedScore()/xpTotals() (no data-obj), so pairs-found / moves are motivational feedback,
         not a grade. No time limit; the brief flip-back delay is cosmetic. */
      memorymatches.forEach(function(el, i){
        var cards = Array.prototype.slice.call(el.querySelectorAll(".nv-mm-card"));
        var fb = el.querySelector(".nv-mm-fb");
        var scoreEl = el.querySelector(".nv-mm-score b");
        var movesEl = el.querySelector(".nv-mm-moves");
        var pc = {}; cards.forEach(function(c){ pc[c.getAttribute("data-pair")] = true; });
        var total = Object.keys(pc).length;
        var open = [], matched = 0, moves = 0, busy = false;
        function setDown(c){ c.classList.remove("nv-mm-up"); c.setAttribute("aria-label", "Face-down card"); c.disabled = false; }
        function setUp(c){ c.classList.add("nv-mm-up"); var f = c.querySelector(".nv-mm-face");
          c.setAttribute("aria-label", "Card showing: " + (f ? f.textContent : "")); }
        function refresh(){ if (scoreEl) scoreEl.textContent = String(matched);
          if (movesEl) movesEl.textContent = moves + (moves === 1 ? " move" : " moves"); }
        function finish(){
          if (mmSeen["mm"+i]) return;
          mmSeen["mm"+i] = { ok: matched === total, got: matched, max: total };
          if (fb){ fb.classList.remove("no"); fb.classList.add("show", "ok");
            fb.textContent = "All " + total + " pairs found in " + moves + (moves === 1 ? " move." : " moves."); }
          save(); updateProgress();
        }
        el.classList.add("nv-mm-live");                 // static study list → interactive game
        cards.forEach(function(c){ setDown(c);
          c.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;   // anti-cheat: ignore synthetic clicks
            if (busy || mmSeen["mm"+i]) return;
            if (c.classList.contains("nv-mm-up") || c.classList.contains("nv-mm-done")) return;
            setUp(c); c.disabled = true; open.push(c);
            if (open.length === 2){
              moves++; refresh();
              var a = open[0], b = open[1];
              if (a.getAttribute("data-pair") === b.getAttribute("data-pair")){
                a.classList.add("nv-mm-done"); b.classList.add("nv-mm-done"); open = [];
                matched++; refresh();
                if (fb){ fb.classList.remove("no"); fb.classList.add("show", "ok"); fb.textContent = "Matched!"; }
                if (matched === total) finish();
              } else {
                busy = true;
                if (fb){ fb.classList.remove("ok"); fb.classList.add("show", "no"); fb.textContent = "Not a match — try again."; }
                setTimeout(function(){ setDown(a); setDown(b); open = []; busy = false; }, 900);
              }
            }
          });
        });
        refresh();
        // Resume: only completion survives byte pressure (the mid-game board isn't stored), so a
        // resumed completed game shows every pair matched + the tally, mirroring the other games.
        el.__mmRestore = function(rec){
          matched = (rec && rec.got) || total;
          cards.forEach(function(c){ setUp(c); c.classList.add("nv-mm-done"); c.disabled = true; });
          mmSeen["mm"+i] = { ok: !!(rec && rec.ok), got: matched, max: total };
          if (scoreEl) scoreEl.textContent = String(matched);
          if (fb){ fb.classList.add("show", "ok"); fb.textContent = "You completed this activity (" + matched + " / " + total + " pairs)."; }
        };
      });

      /* hangman — FORMATIVE word-guess game (James, 2026-07-10). The keys are real <button>s;
         this wiring reveals letters, builds the decorative circle-X figure on wrong guesses, and
         records completion on win/loss. Clicks are isTrusted-guarded (anti-cheat). Completion-only:
         hgSeen never enters gradedScore()/xpTotals() (no data-obj). The figure is purely cosmetic
         (aria-hidden) — the live "N guesses left" readout carries the state, so there is no time
         limit and it works under reduced-motion / screen readers. */
      hangmen.forEach(function(el, i){
        var answer = (el.getAttribute("data-answer") || "").toUpperCase();
        var maxWrong = parseInt(el.getAttribute("data-max"), 10) || 6;
        var slots = Array.prototype.slice.call(el.querySelectorAll(".nv-hg-slot"));
        var keys = Array.prototype.slice.call(el.querySelectorAll(".nv-hg-key"));
        var lives = el.querySelector(".nv-hg-lives");
        var word = el.querySelector(".nv-hg-word");
        var fb = el.querySelector(".nv-hg-fb");
        var pieces = Array.prototype.slice.call(el.querySelectorAll(".nv-hg-piece"));
        var solveBtn = el.querySelector(".nv-hg-solve-btn");
        var solveInput = el.querySelector(".nv-hg-solve-input");
        var solveWrong = 0;   // wrong whole-word "Solve" attempts, counted alongside bad letters
        var need = {}, ci; for (ci=0;ci<answer.length;ci++){ var c0=answer.charAt(ci); if (c0>="A"&&c0<="Z") need[c0]=true; }
        var guessed = [];
        function has(L){ for (var q=0;q<guessed.length;q++){ if (guessed[q]===L) return true; } return false; }
        function normWord(s){ return String(s||"").toUpperCase().replace(/[^A-Z]/g, ""); }
        function totalWrong(){ return hgState(answer, guessed, maxWrong).wrong + solveWrong; }
        function reveal(all, missed){
          slots.forEach(function(s){ var L=s.getAttribute("data-letter"); var ch=s.querySelector(".nv-hg-ch");
            if (all || has(L)){ if (ch){ ch.textContent=L; ch.removeAttribute("aria-hidden"); } s.classList.add("nv-hg-filled");
              if (missed && !has(L)) s.classList.add("nv-hg-missed"); } });
          if (word){ var shown = slots.map(function(s){ return (all || has(s.getAttribute("data-letter"))) ? s.getAttribute("data-letter") : "blank"; }).join(" ");
            word.setAttribute("aria-label", "Word: " + shown); }
        }
        function drawFigure(wrong){
          // reveal `wrong` discrete segments (one per wrong guess); the ghost outline stays behind
          // so the whole circle-X is visible from the start. Pieces: [4 quarter-arcs | 1 ring] + 2 X.
          pieces.forEach(function(p, idx){ p.style.opacity = idx < wrong ? "1" : "0"; });
        }
        function finish(st){
          if (hgSeen["hg"+i]) return;
          keys.forEach(function(k){ k.disabled = true; });
          if (solveBtn) solveBtn.disabled = true;
          if (solveInput) solveInput.disabled = true;
          reveal(true, !st.won);
          hgSeen["hg"+i] = { ok: st.won };
          if (fb){ fb.classList.remove("ok","no"); fb.classList.add("show", st.won ? "ok" : "no");
            fb.textContent = st.won ? "Solved it — nice recall." : ("Out of guesses. The word was “" + answer + ".”"); }
          save(); updateProgress();
        }
        keys.forEach(function(k){
          k.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;   // anti-cheat: ignore synthetic clicks
            if (hgSeen["hg"+i] || k.disabled) return;
            var L = (k.getAttribute("data-letter") || "").toUpperCase(); if (!L || has(L)) return;
            guessed.push(L); k.disabled = true;
            var good = !!need[L];
            k.classList.add(good ? "nv-hg-key-hit" : "nv-hg-key-miss");
            var st = hgState(answer, guessed, maxWrong);
            var tw = totalWrong();
            if (good){ reveal(false, false);
              if (fb){ fb.classList.remove("no"); fb.classList.add("show","ok"); fb.textContent = "“" + L + "” is in the word."; } }
            else { drawFigure(tw);
              var left = Math.max(0, maxWrong - tw); if (lives) lives.textContent = left + (left === 1 ? " guess left" : " guesses left");
              if (fb){ fb.classList.remove("ok"); fb.classList.add("show","no"); fb.textContent = "“" + L + "” isn’t in the word."; } }
            if (st.won || tw >= maxWrong) finish({ won: st.won });
          });
        });
        // Solve the Puzzle — guess the WHOLE term. Correct wins; wrong costs one guess like a bad letter.
        function trySolve(){
          if (hgSeen["hg"+i]) return;
          var val = solveInput ? solveInput.value : "";
          if (!normWord(val)) return;
          if (normWord(val) === normWord(answer)) { reveal(true, false); finish({ won: true }); return; }
          solveWrong++;
          var tw = totalWrong();
          drawFigure(tw);
          var left = Math.max(0, maxWrong - tw); if (lives) lives.textContent = left + (left === 1 ? " guess left" : " guesses left");
          if (fb){ fb.classList.remove("ok"); fb.classList.add("show","no"); fb.textContent = "“" + val + "” isn’t the term."; }
          if (solveInput) solveInput.value = "";
          if (tw >= maxWrong) finish({ won: false });
        }
        if (solveBtn) solveBtn.addEventListener("click", trySolve);
        if (solveInput) solveInput.addEventListener("keydown", function(e){ if (e.key === "Enter"){ e.preventDefault(); trySolve(); } });
        reveal(false, false);
        // Resume: only {ok} survives byte pressure; a resumed completed game reveals the word + locks.
        el.__hgRestore = function(rec){
          keys.forEach(function(k){ k.disabled = true; });
          reveal(true, false);
          hgSeen["hg"+i] = { ok: !!(rec && rec.ok) };
          if (fb){ fb.classList.add("show", (rec && rec.ok) ? "ok" : "no");
            fb.textContent = (rec && rec.ok) ? "You solved this word." : ("You completed this activity. The word was “" + answer + ".”"); }
        };
      });

      /* wheelOfFortune (hybrid review game): SPIN to draw a category (gameShow's wheel), answer a
         random MCQ from its bank (quizBoard's banks, drawn WITHOUT replacement), and a CORRECT
         answer earns a turn to guess a letter or SOLVE the single hidden phrase (hangman's reveal).
         FORMATIVE — completion-only, never graded. Registers in woffSeen once the puzzle is solved
         OR the question bank is exhausted and the learner explicitly reveals the phrase. The dry-bank
         fallback keeps the completion gate from wedging, but it does not auto-spoil the answer. The play-time draw is a seeded, resume-safe RNG
         (count-re-derivable, like gameShow's spin); option order per MCQ is fixed at build time →
         resume-stable. Only {ok} is persisted (like hangman) → resume reveals the phrase + locks. */
      wheels.forEach(function(el, i){
        var puzzle = (el.getAttribute("data-puzzle") || "").toUpperCase();
        var rotor = el.querySelector(".nv-wof-rotor");
        var spinBtn = el.querySelector(".nv-wof-spin");
        var panelWrap = el.querySelector(".nv-wof-panels");
        var panels = Array.prototype.slice.call(el.querySelectorAll(".nv-wof-panel"));
        var segs = Array.prototype.slice.call(el.querySelectorAll(".nv-wof-seg"));
        var legendItems = Array.prototype.slice.call(el.querySelectorAll(".nv-wof-cat"));
        var slots = Array.prototype.slice.call(el.querySelectorAll(".nv-wof-slot"));
        var keys = Array.prototype.slice.call(el.querySelectorAll(".nv-wof-key"));
        var turnBox = el.querySelector(".nv-wof-turn");
        var solveInput = el.querySelector(".nv-wof-solveinput");
        var solveBtn = el.querySelector(".nv-wof-solve");
        var word = el.querySelector(".nv-wof-word");
        var fb = el.querySelector(".nv-wof-fb");
        var ncat = segs.length, seg = 360/(ncat||1), turns = 0;
        var answered = {};       // "ci:qi" -> true (questions used, no replacement)
        var guessed = [];        // letters guessed so far
        var current = null;      // panel awaiting an answer (null = none)
        var earned = false;      // a correct answer has earned a letter/solve turn
        var finalSolve = false;  // question bank is dry; allow solve attempts before reveal fallback

        // panel-scoped radio names → exclusive groups that also can't clash across blocks
        panels.forEach(function(p){
          var ci = p.getAttribute("data-cat"), qi = p.getAttribute("data-q");
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){ r.name = "wof"+i+"c"+ci+"q"+qi; });
        });
        function panelKey(p){ return p.getAttribute("data-cat") + ":" + p.getAttribute("data-q"); }
        function remainingPanels(){ return panels.filter(function(p){ return !answered[panelKey(p)]; }); }
        function catRemaining(ci){ return panels.filter(function(p){ return p.getAttribute("data-cat")===String(ci) && !answered[panelKey(p)]; }); }
        function hidePanels(){ panels.forEach(function(p){ p.hidden = true; }); }
        function updateLegend(){
          legendItems.forEach(function(li){ var ci=li.getAttribute("data-cat"); var left=catRemaining(ci).length;
            // Don't reveal how many questions remain; the dimmed "done" state is signal enough.
            var lab=li.querySelector(".nv-wof-catleft"); if (lab) lab.textContent = "";
            if (!left) li.classList.add("nv-wof-cat-done"); });
        }
        function markSeg(ci, done){ if (segs[ci] && done) segs[ci].classList.add("nv-wof-seg-done"); }
        function pointAt(ci){ if (!rotor) return; turns += 4; rotor.style.transform = "rotate(" + (turns*360 - (ci+0.5)*seg) + "deg)"; }
        function reveal(all){
          slots.forEach(function(s){ var L=s.getAttribute("data-letter"); var ch=s.querySelector(".nv-wof-ch");
            if (all || guessed.indexOf(L) >= 0){ if (ch){ ch.textContent=L; ch.removeAttribute("aria-hidden"); } s.classList.add("nv-wof-filled"); } });
          if (word){ var shown = slots.map(function(s){ return (all || guessed.indexOf(s.getAttribute("data-letter"))>=0) ? s.getAttribute("data-letter") : "blank"; }).join(" ");
            word.setAttribute("aria-label", "Puzzle: " + shown); }
        }
        function showFb(kind, msg){ if (!fb) return; fb.classList.remove("ok","no"); fb.classList.add("show", kind); fb.textContent = msg; }
        function endTurn(){ earned = false; if (turnBox) turnBox.hidden = true;
          keys.forEach(function(k){ k.disabled = true; }); }   // solve stays enabled always (persistent, outside the turn box)
        function offerTurn(){ earned = true; if (turnBox) turnBox.hidden = false;
          keys.forEach(function(k){ if (!k.classList.contains("nv-wof-key-used")) k.disabled = false; });
          if (solveInput) solveInput.disabled = false; if (solveBtn) solveBtn.disabled = false; }
        function offerFinalSolve(){
          finalSolve = true; earned = true; hidePanels();
          if (spinBtn){ spinBtn.disabled = true; spinBtn.textContent = "No questions left"; }
          if (turnBox) turnBox.hidden = false;
          keys.forEach(function(k){ k.disabled = true; });
          if (solveInput) solveInput.disabled = false; if (solveBtn){ solveBtn.disabled = false; }
          showFb("ok", "No questions left — try to solve the puzzle, or reveal it to complete.");
        }
        function reSpin(){ if (remainingPanels().length){ if (spinBtn){ spinBtn.disabled=false; spinBtn.textContent="Spin again"; } } else offerFinalSolve(); }
        function finish(solved){
          if (woffSeen["wof"+i]) return;
          reveal(true); endTurn(); hidePanels();
          if (spinBtn){ spinBtn.disabled = true; spinBtn.hidden = true; }
          woffSeen["wof"+i] = { ok: solved };
          showFb(solved ? "ok" : "no", solved ? "Solved it — nice recall." : ("Puzzle revealed. It was “" + puzzle + ".”"));
          loc = { t:"wof", i:i }; current = null;
          save(); updateProgress();
        }
        function lockPanel(p, chosen, ok){
          var ansIdx = +p.getAttribute("data-answer");
          Array.prototype.slice.call(p.querySelectorAll(".nv-wof-opt")).forEach(function(lab, oi){
            var r=lab.querySelector('input[type="radio"]'); if (r) r.disabled = true;
            if (oi===ansIdx) lab.classList.add("nv-wof-correct"); else if (oi===chosen) lab.classList.add("nv-wof-wrong"); });
          var sub=p.querySelector(".nv-wof-submit"); if (sub) sub.disabled = true;
        }
        function submit(p){
          if (woffSeen["wof"+i] || !p || answered[panelKey(p)]) return;
          var chosen = p.querySelector('input[type="radio"]:checked');
          if (!chosen){ if (panelWrap) panelWrap.classList.add("nv-wof-nudge"); return; }
          var ok = (+chosen.value === +p.getAttribute("data-answer"));
          answered[panelKey(p)] = true; lockPanel(p, +chosen.value, ok);
          markSeg(+p.getAttribute("data-cat"), !catRemaining(p.getAttribute("data-cat")).length);
          updateLegend(); current = null; p.hidden = true;
          if (ok){ showFb("ok", "Correct — guess a letter or solve the puzzle."); offerTurn(); }
          else { showFb("no", "Not quite — spin again."); reSpin(); }
        }
        function spin(){
          if (woffSeen["wof"+i] || current || earned) return;
          var catsLeft = []; legendItems.forEach(function(li){ var ci=li.getAttribute("data-cat"); if (catRemaining(ci).length) catsLeft.push(+ci); });
          if (!catsLeft.length){ offerFinalSolve(); return; }                 // bank dry → explicit solve/reveal terminal
          var rng = makeRng((i+1)*0x9E3779B1 + Object.keys(answered).length);  // deterministic + resume-safe
          var ci = catsLeft[Math.floor(rng()*catsLeft.length)];
          var pool = catRemaining(ci);
          var p = pool[Math.floor(rng()*pool.length)];
          if (spinBtn) spinBtn.disabled = true;
          current = p; hidePanels();                          // keep the question hidden while the wheel turns
          pointAt(ci);
          function showThisPanel(){
            if (woffSeen["wof"+i] || current !== p) return;   // still the active spin?
            hidePanels(); p.hidden = false;
            try { var f = p.querySelector('input[type="radio"]'); if (f) f.focus(); } catch(e){}
          }
          // Reveal the question only AFTER the wheel STOPS spinning (transition end);
          // reveal immediately when motion is reduced (no spin animation) or there's no rotor.
          var reduce = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
          if (reduce || !rotor){ showThisPanel(); return; }
          var shown = false;
          var onEnd = function(ev){
            if (ev && ev.propertyName && ev.propertyName !== "transform") return;
            if (shown) return; shown = true;
            rotor.removeEventListener("transitionend", onEnd); showThisPanel();
          };
          rotor.addEventListener("transitionend", onEnd);
          setTimeout(function(){ if (!shown){ shown = true;   // fallback if transitionend never fires
            try { rotor.removeEventListener("transitionend", onEnd); } catch(e){} showThisPanel(); } }, 3600);
        }
        function guessLetter(L){
          if (woffSeen["wof"+i] || !earned || !L || guessed.indexOf(L) >= 0) return;
          guessed.push(L);
          var key = keys.filter(function(k){ return (k.getAttribute("data-letter")||"").toUpperCase()===L; })[0];
          var inWord = puzzle.indexOf(L) >= 0;
          if (key){ key.disabled = true; key.classList.add("nv-wof-key-used", inWord ? "nv-wof-key-hit" : "nv-wof-key-miss"); }
          reveal(false); endTurn();
          if (wofState(puzzle, guessed).solved){ finish(true); return; }
          showFb(inWord ? "ok" : "no", inWord ? ("“"+L+"” is in the puzzle.") : ("“"+L+"” isn’t in the puzzle."));
          reSpin();                                                            // spend the turn, spin again (or finish if dry)
        }
        function trySolve(){
          if (woffSeen["wof"+i]) return;                                     // solving is ALWAYS available — no earned-turn gate
          var guess = (solveInput ? solveInput.value : "").toUpperCase().replace(/[^A-Z]/g, "");
          var ans = puzzle.replace(/[^A-Z]/g, "");
          if (guess && guess === ans){ finish(true); return; }               // solved outright → win
          if (finalSolve){
            showFb("no", "Not quite. Try again, or reveal the answer to complete.");
            if (solveInput) solveInput.select();
            return;
          }
          // A wrong/empty solve is a FREE action: nudge, never consume the earned turn or force a spin.
          showFb("no", guess ? "Not the puzzle yet — keep playing, or try again." : "Type the full puzzle to solve.");
          if (solveInput) solveInput.select();
        }
        function revealAnswer(){
          if (woffSeen["wof"+i]) return;   // "I give up": reveal the answer and complete the game at any time
          finish(false);
        }
        if (spinBtn) spinBtn.addEventListener("click", spin);
        panels.forEach(function(p){
          var sub=p.querySelector(".nv-wof-submit");
          if (sub) sub.addEventListener("click", function(){ submit(p); });
          Array.prototype.slice.call(p.querySelectorAll('input[type="radio"]')).forEach(function(r){
            r.addEventListener("change", function(){ if (panelWrap) panelWrap.classList.remove("nv-wof-nudge"); }); });
        });
        keys.forEach(function(k){
          k.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;   // anti-cheat: ignore synthetic clicks
            guessLetter((k.getAttribute("data-letter")||"").toUpperCase());
          });
        });
        if (solveBtn) solveBtn.addEventListener("click", trySolve);
        if (solveInput) solveInput.addEventListener("keydown", function(ev){ if (ev.key === "Enter") trySolve(); });
        var revealBtn = document.createElement("button");
        revealBtn.className = "nv-btn nv-wof-reveal";
        revealBtn.type = "button";
        revealBtn.textContent = "Reveal";
        revealBtn.disabled = false;   // always available as an "I give up" / advance affordance
        revealBtn.addEventListener("click", revealAnswer);
        var solveWrap = el.querySelector(".nv-wof-solvewrap");
        if (solveWrap) solveWrap.appendChild(revealBtn);
        var oldOfferFinalSolve = offerFinalSolve;
        offerFinalSolve = function(){
          oldOfferFinalSolve();
          revealBtn.disabled = false;
        };
        updateLegend(); reveal(false);
        // Resume: only {ok} survives byte pressure — a resumed completed game reveals the phrase + locks.
        el.__wofRestore = function(rec){
          reveal(true); endTurn(); hidePanels();
          if (spinBtn){ spinBtn.disabled = true; spinBtn.hidden = true; }
          woffSeen["wof"+i] = { ok: !!(rec && rec.ok) };
          showFb((rec && rec.ok) ? "ok" : "no", (rec && rec.ok) ? "You solved this puzzle." : ("You completed this activity. The puzzle was “" + puzzle + ".”"));
        };
      });

      /* E1 — declarative interaction engine. Each [data-interaction] root carries its
         config (elements/variables/rules) in a JSON script; the pure core above runs the
         rules, this wiring only paints (active face per state, `hidden` state hides,
         {var} spans update) and persists. Clicks land on [data-el] nodes (buttons for
         keyboard a11y). A `done` action records into ixSeen — with got/max as PARTIAL
         credit when authored — and locks the block, mirroring the other interactives. */
      interactions.forEach(function(root, i){
        var cfg = {};
        try { var cEl = root.querySelector(".nv-ix-cfg"); cfg = JSON.parse(cEl ? cEl.textContent : "{}") || {}; }
        catch(e){ cfg = {}; }
        var st = ixInitState(cfg);
        var key = "ix" + i;
        var fb = root.querySelector(".nv-ix-fb");
        function paint(){
          (cfg.elements || []).forEach(function(el){
            var node = root.querySelector('[data-el="' + el.id + '"]'); if (!node) return;
            var cur = st.states[el.id];
            node.setAttribute("data-state", cur);
            node.hidden = (cur === "hidden");                       // `hidden` is a stateful visibility switch
            var faces = node.querySelectorAll(".nv-ix-face"), hasFace = false, f;
            for (f = 0; f < faces.length; f++){ if (faces[f].getAttribute("data-face") === cur){ hasFace = true; } }
            for (f = 0; f < faces.length; f++){ var fa = faces[f].getAttribute("data-face");
              faces[f].hidden = hasFace ? (fa !== cur) : (fa !== ""); }   // no face for this state -> default face
          });
          Object.keys(st.vars).forEach(function(name){
            var spans = root.querySelectorAll('[data-nvvar="' + name + '"]'), v = st.vars[name];
            for (var n = 0; n < spans.length; n++){ spans[n].textContent = (typeof v === "boolean") ? (v ? "true" : "false") : String(v); }
          });
        }
        function settle(){
          paint();
          if (st.done && !ixSeen[key]){
            var rec = { ok: (st.max != null ? (ixNum(st.got) >= ixNum(st.max) ? 1 : 0) : 1),
                        v: st.vars, s: st.states };
            if (st.got != null){ rec.got = st.got; rec.max = st.max; }
            ixSeen[key] = rec;
            root.classList.add("nv-ix-done");
            if (fb){ fb.textContent = (st.max != null) ? ("Complete — " + st.got + " of " + st.max) : "Complete"; fb.classList.add("show", rec.ok ? "ok" : "no"); }
            updateProgress();
          }
        }
        root.addEventListener("click", function(ev){
          if (ixSeen[key]) return;                                  // locked once complete
          var t = ev.target && ev.target.closest ? ev.target.closest("[data-el]") : null;
          if (!t || !root.contains(t)) return;
          ixStep(cfg, st, { event: "click", target: t.getAttribute("data-el") });
          settle();
        });
        // Resume: a completed interaction restores its final variable/state snapshot and
        // repaints (dropped under byte pressure -> initial paint + the completion record).
        root.__ixRestore = function(rec){
          if (rec && rec.v) st.vars = rec.v;
          if (rec && rec.s) st.states = rec.s;
          st.done = true;
          if (rec && rec.got != null){ st.got = rec.got; st.max = rec.max; }
          ixSeen[key] = { ok: (rec && rec.ok) ? 1 : 0, got: rec && rec.got, max: rec && rec.max, v: st.vars, s: st.states };
          paint(); root.classList.add("nv-ix-done");
          if (fb){ fb.textContent = (rec && rec.max != null) ? ("Complete — " + rec.got + " of " + rec.max) : "Complete"; fb.classList.add("show", ixSeen[key].ok ? "ok" : "no"); }
        };
        ixResetters.push(function(){                                // graded retry: back to a fresh machine
          st = ixInitState(cfg);
          root.classList.remove("nv-ix-done");
          if (fb){ fb.textContent = ""; fb.classList.remove("show", "ok", "no"); }
          ixStep(cfg, st, { event: "start" });
          paint();
        });
        ixStep(cfg, st, { event: "start" });                        // a resumed course overwrites via __ixRestore below
        settle();
      });

      /* wordScramble — FORMATIVE anagram game (mirrors hangman). Tapping a scrambled tile
         places its letter into the next empty slot (left to right); once every slot is
         filled the arrangement auto-checks. A wrong arrangement offers Clear to retry —
         unlimited attempts, no time limit, and no "wrong guess" budget (the learner already
         holds every letter; they are only ordering them). Clicks are isTrusted-guarded
         (anti-cheat). Completion-only: scSeen never enters gradedScore()/xpTotals() (no
         data-obj). */
      wordscrambles.forEach(function(el, i){
        var answer = (el.getAttribute("data-answer") || "").toUpperCase();
        var need = answer.split("").filter(function(ch){ return ch >= "A" && ch <= "Z"; });
        var slots = Array.prototype.slice.call(el.querySelectorAll(".nv-scr-slot"));
        var tiles = Array.prototype.slice.call(el.querySelectorAll(".nv-scr-tile"));
        var word = el.querySelector(".nv-scr-word");
        var clearBtn = el.querySelector(".nv-scr-clear");
        var fb = el.querySelector(".nv-scr-fb");
        var placed = [];   // [{tile, letter}] in slot order, left to right
        function renderSlots(){
          slots.forEach(function(s, k){ var p = placed[k];
            s.textContent = p ? p.letter : ""; s.classList.toggle("nv-scr-filled", !!p); });
          if (word){ var shown = need.map(function(_letter, k){ return placed[k] ? placed[k].letter : "blank"; }).join(" ");
            word.setAttribute("aria-label", "Term: " + shown); }
        }
        function finish(ok){
          if (scSeen["sc"+i]) return;
          tiles.forEach(function(t){ t.disabled = true; });
          el.classList.add("nv-scr-done");
          scSeen["sc"+i] = { ok: ok };
          if (fb){ fb.classList.remove("ok","no"); fb.classList.add("show", ok ? "ok" : "no");
            fb.textContent = ok ? "Solved it — nice recall." : ("Not quite. The term was “" + answer + ".”"); }
          save(); updateProgress();
        }
        function checkIfFull(){
          if (placed.length !== need.length) return;
          if (scSolved(need, placed.map(function(p){ return p.letter; }))){ finish(true); return; }
          if (fb){ fb.classList.remove("ok"); fb.classList.add("show","no"); fb.textContent = "Not quite — try again."; }
        }
        tiles.forEach(function(t){
          t.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;   // anti-cheat: ignore synthetic clicks
            if (el.classList.contains("nv-scr-done") || t.disabled || placed.length >= need.length) return;
            t.disabled = true; t.classList.add("nv-scr-used");
            placed.push({ tile: t, letter: (t.getAttribute("data-letter") || "").toUpperCase() });
            renderSlots();
            checkIfFull();
          });
        });
        if (clearBtn){
          clearBtn.addEventListener("click", function(){
            if (el.classList.contains("nv-scr-done")) return;
            placed.forEach(function(p){ p.tile.disabled = false; p.tile.classList.remove("nv-scr-used"); });
            placed = [];
            renderSlots();
            if (fb){ fb.classList.remove("show","ok","no"); fb.textContent = ""; }
          });
        }
        renderSlots();
        // Resume: only {ok} survives byte pressure; a resumed completed game reveals the term + locks.
        el.__scRestore = function(rec){
          tiles.forEach(function(t){ t.disabled = true; });
          el.classList.add("nv-scr-done");
          slots.forEach(function(s, k){ s.textContent = need[k]; s.classList.add("nv-scr-filled"); });
          scSeen["sc"+i] = { ok: !!(rec && rec.ok) };
          if (fb){ fb.classList.add("show", (rec && rec.ok) ? "ok" : "no");
            fb.textContent = (rec && rec.ok) ? "You solved this term." : ("You completed this activity. The term was “" + answer + ".”"); }
        };
      });

      /* spotHazard — FORMATIVE click-to-identify recognition game (mirrors whackAMole
         exactly, including its wamScore math — a hotspot is either a hazard=target or a
         decoy, just positioned over a real image instead of laid out in a grid). Clicks
         are isTrusted-guarded (anti-cheat). Completion-only: shSeen never enters
         gradedScore()/xpTotals() (no data-obj). */
      spothazards.forEach(function(el, i){
        var spots = Array.prototype.slice.call(el.querySelectorAll(".nv-sh-spot"));
        var doneBtn = el.querySelector(".nv-sh-done");
        var fb = el.querySelector(".nv-sh-fb");
        var statusEl = el.querySelector(".nv-sh-status");
        var targets = spots.filter(function(s){ return s.getAttribute("data-hazard") === "1"; }).length;
        var hits = {};                 // idx -> true once clicked (hazard or decoy)
        function isHazard(s){ return s.getAttribute("data-hazard") === "1"; }
        function tally(){ return wamScore(spots.map(function(s, si){ return { target: isHazard(s), hit: !!hits[si] }; })); }
        function counts(){ var t=0, d=0; spots.forEach(function(s, si){ if (hits[si]){ if (isHazard(s)) t++; else d++; } }); return { t:t, d:d }; }
        function hazardsLeft(){ return spots.some(function(s, si){ return isHazard(s) && !hits[si]; }); }
        function refreshStatus(){ if (statusEl) statusEl.textContent = counts().t + " of " + targets + " found"; }
        function finish(){
          if (shSeen["sh"+i]) return;
          spots.forEach(function(s){ s.disabled = true; s.classList.add("nv-sh-locked"); });
          if (doneBtn){ doneBtn.disabled = true; doneBtn.hidden = true; }
          var r = tally(), c = counts();
          shSeen["sh"+i] = { ok: r.ok, got: r.got, max: r.max };
          if (fb){ fb.classList.remove("ok","no"); fb.classList.add("show", r.ok ? "ok" : "no");
            var msg = "You found " + c.t + " of " + targets + " hazard" + (targets===1?"":"s") +
              (c.d ? (" and clicked " + c.d + " non-hazard spot" + (c.d>1?"s":"")) : "") + ".";
            fb.innerHTML = '<span class="nv-sr-only">' + (r.ok ? "Perfect. " : "Review. ") + '</span>' + msg; }
          save(); updateProgress();
        }
        spots.forEach(function(s, si){
          s.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;       // anti-cheat: ignore synthetic clicks
            if (shSeen["sh"+i] || hits[si]) return;
            hits[si] = true;
            var good = isHazard(s);
            s.disabled = true;
            s.classList.add("nv-sh-hit", good ? "nv-sh-found" : "nv-sh-miss");
            var mark = document.createElement("span"); mark.className = "nv-sr-only";
            mark.textContent = " (" + (good ? s.getAttribute("data-label") + ", hazard" : "not a hazard") + ")";
            s.appendChild(mark);
            refreshStatus();
            if (fb){ fb.classList.remove("ok","no"); fb.classList.add("show", good ? "ok" : "no");
              fb.textContent = good ? ("Hazard found — " + s.getAttribute("data-label") + ".") : "Not a hazard."; }
            if (!hazardsLeft()) finish();                    // auto-finish when every hazard is found
          });
        });
        if (doneBtn) doneBtn.addEventListener("click", function(ev){ if (ev && ev.isTrusted === false) return; finish(); });
        refreshStatus();
        // Resume: re-lock the field and re-show the final tally. Under byte pressure only
        // {ok,got,max} survive (the per-spot hit set is dropped), so a resumed game cannot
        // re-mark individual spots - it shows the score + locks, mirroring whackAMole.
        el.__shRestore = function(rec){
          spots.forEach(function(s){ s.disabled = true; s.classList.add("nv-sh-locked"); });
          if (doneBtn){ doneBtn.disabled = true; doneBtn.hidden = true; }
          shSeen["sh"+i] = { ok: !!(rec && rec.ok), got: rec && rec.got, max: rec && rec.max };
          if (statusEl) statusEl.textContent = (rec && typeof rec.got === "number" ? rec.got : "?") + " of " + targets + " found";
          if (fb){ fb.classList.add("show", (rec && rec.ok) ? "ok" : "no");
            fb.textContent = "You completed this activity."; }
        };
      });

      /* C7 reflection — free-text / open-response, NON-GRADED (completion-only). The learner
         types a response and submits; the model answer + rubric (authored at build time — no
         runtime AI scorer, SCORM is offline) then REVEAL for self-assessment. Marking the block
         done never touches the graded score, pass gate, or XP (there is no data-obj, and it is
         never passed to gradedScore()/xpTotals()). Requires a non-empty answer so ticking the
         box means the learner actually reflected. The typed text persists via the `rf` suspend
         rung; on resume the guidance is re-revealed and the block locked. */
      reflections.forEach(function(el, i){
        var input = el.querySelector(".nv-rf-input");
        var submit = el.querySelector(".nv-rf-submit");
        var answer = el.querySelector(".nv-rf-answer");   // may be absent (no model/criteria authored)
        var done = el.querySelector(".nv-rf-done");
        function lock(){ if (input) input.readOnly = true; if (submit){ submit.disabled = true; submit.hidden = true; } }
        function reveal(){ if (answer) answer.hidden = false; if (done) done.hidden = false; }
        if (submit) submit.addEventListener("click", function(){
          if (reflectionSeen["rf"+i]) return;                 // already submitted
          var txt = input ? input.value.trim() : "";
          if (!txt){ if (input){ el.classList.add("nv-rf-nudge"); input.focus(); } return; }  // need something written
          el.classList.remove("nv-rf-nudge");
          reflectionSeen["rf"+i] = { ok:1, text: txt, rev:1 };
          reveal(); lock();
          save(); updateProgress();
        });
        // Resume: re-fill the typed text (dropped under byte pressure -> just the completion
        // flag survives), re-reveal the guidance, and lock. The model answer lives in the DOM,
        // so it is always shown once the block was completed, even if the text was packed away.
        el.__rfRestore = function(rec){
          if (rec && rec.text && input) input.value = rec.text;
          reveal(); lock();
          reflectionSeen["rf"+i] = { ok:1, text: (rec && rec.text) || "", rev:1 };
        };
      });

      /* poll — a no-right-answer check-in question (mirrors reflection: completion-only,
         never graded, no data-obj). Clicking an option locks the whole poll — like a real
         vote, there's no changing your answer — reveals the optional debrief note, and
         completes the block. Clicks are isTrusted-guarded (anti-cheat). */
      polls.forEach(function(el, i){
        var opts = Array.prototype.slice.call(el.querySelectorAll(".nv-poll-opt"));
        var revealWrap = el.querySelector(".nv-poll-reveal-wrap");
        function lock(picked){
          opts.forEach(function(o, oi){ o.disabled = true; o.classList.toggle("nv-poll-picked", oi === picked); });
          if (revealWrap) revealWrap.hidden = false;
        }
        opts.forEach(function(o, oi){
          o.addEventListener("click", function(ev){
            if (ev && ev.isTrusted === false) return;   // anti-cheat: ignore synthetic clicks
            if (pollSeen["pl"+i] || o.disabled) return;
            lock(oi);
            pollSeen["pl"+i] = { picked: oi };
            save(); updateProgress();
          });
        });
        // Resume: the picked index survives byte pressure (a small int, cheap to keep).
        el.__pollRestore = function(rec){
          var picked = rec && typeof rec.picked === "number" ? rec.picked : -1;
          lock(picked);
          pollSeen["pl"+i] = { picked: picked };
        };
      });

      /* ---------------- Section pager (opt-in via `*Paged:* on`) ----------------
         Group the course into one-at-a-time PAGES at `.nv-section` boundaries: the intro
         before the first section is page 0; each [lead wave, section, tail wave] is a page;
         everything after the last section (incl .nv-course-end) rides the final page. A gated
         "Next" button advances between pages, DISABLED until every required interaction on the
         current page is complete (reuses the same per-block Seen maps the completion logic
         reads). Modals stay OUTSIDE the pages (position-fixed overlays must not be paginated).
         Purely client-side navigation — the graded score / objectives / single SCO are all
         unchanged. Absent (no data-paged) → PAGED stays false and this whole layer is inert. */
      var PAGED = document.body.getAttribute("data-paged") === "1";
      var pageEls = [], pageReq = [], curPage = 0;
      // The required-interaction predicates, keyed by DOM node, that the pager consults to
      // decide when a page is complete — mirrors maybeComplete()'s required set exactly.
      var interactiveNodes = [];
      function regNode(node, doneFn){ if (node) interactiveNodes.push({ node: node, done: doneFn }); }
      function pageInteractive(pageEl){
        return interactiveNodes.filter(function(e){ return pageEl.contains(e.node); });
      }
      function pageDone(p){
        return pageComplete((pageReq[p] || []).map(function(e){ return e.done(); }));
      }
      function refreshPager(){
        if (!PAGED) return;
        pageEls.forEach(function(pageEl, p){
          // Instant/terminal (no DEFERRED): the "Next" button gates on every interaction being
          // complete. Deferred: the "Submit section" button stays enabled (it scores the section
          // on click), so leave its disabled state alone once submitted.
          var btn = pageEl.__nextBtn; if (btn && !DEFERRED) btn.disabled = !pageDone(p);
        });
      }
      // ---- Deferred mode: section submit (fixes "answered everything, couldn't Finish") -------
      // Grade + silently record every not-yet-scored block on a section, reading tentative picks
      // straight from the DOM. Blank items score wrong. updateProgress() then advances completion:
      // once the LAST section is submitted, every Seen map is full → maybeComplete fires →
      // enableEndButton runs → Finish enables. Feedback is held to the end-of-course review.
      function sectionScoredEls(pageEl){
        var out = [];
        kcs.forEach(function(el,i){ if(!kcSeen[i]&&pageEl.contains(el)) out.push(el); });
        sorts.forEach(function(el,i){ if(!sortSeen["s"+i]&&pageEl.contains(el)) out.push(el); });
        matches.forEach(function(el,i){ if(!matchSeen["mt"+i]&&pageEl.contains(el)) out.push(el); });
        sequences.forEach(function(el,i){ if(!seqSeen["sq"+i]&&pageEl.contains(el)) out.push(el); });
        fills.forEach(function(el,i){ if(!fillSeen["fl"+i]&&pageEl.contains(el)) out.push(el); });
        drags.forEach(function(el,i){ if(!dragSeen["dd"+i]&&pageEl.contains(el)) out.push(el); });
        hotspots.forEach(function(el,i){ if(!hotSeen["ht"+i]&&pageEl.contains(el)) out.push(el); });
        return out;
      }
      function blockAnswered(el){
        if (el.classList.contains("nv-kc"))
          return Array.prototype.slice.call(el.querySelectorAll(".nv-kc-opt")).some(function(o){ return o.classList.contains("is-selected")||o.getAttribute("aria-pressed")==="true"; });
        var picks = Array.prototype.slice.call(el.querySelectorAll(".nv-sort-pick,.nv-match-pick,.nv-seq-pick,.nv-drag-pick"));
        if (picks.length) return picks.some(function(p){ return p.value!==""; });
        var inputs = Array.prototype.slice.call(el.querySelectorAll(".nv-fill-input"));
        if (inputs.length) return inputs.some(function(inp){ return (inp.value||"").trim()!==""; });
        var spots = Array.prototype.slice.call(el.querySelectorAll(".nv-hotspot-spot"));
        if (spots.length) return spots.some(function(sp){ return sp.getAttribute("aria-pressed")==="true"; });
        return true;
      }
      function sectionHasBlank(pageEl){ return sectionScoredEls(pageEl).some(function(el){ return !blockAnswered(el); }); }
      function submitSection(pageEl){
        kcs.forEach(function(kc,i){ if (kcSeen[i] || !pageEl.contains(kc)) return;
          var opts = Array.prototype.slice.call(kc.querySelectorAll(".nv-kc-opt"));
          if (kc.classList.contains("nv-kc--multi")){
            var sel=[]; opts.forEach(function(o,oi){ if(o.classList.contains("is-selected")||o.getAttribute("aria-pressed")==="true") sel.push(oi); });
            lockKcMulti(kc,i,sel, multiAllCorrect(opts.map(function(o){ return o.dataset.correct==="1"; }), sel), true);
          } else {
            var oi=-1; opts.forEach(function(o,k){ if(o.classList.contains("is-selected")) oi=k; });
            lockKc(kc,i,oi, oi>=0 && opts[oi].dataset.correct==="1", true);
          }
        });
        sorts.forEach(function(el,i){ if(!sortSeen["s"+i]&&pageEl.contains(el)) lockSort(el,i,true); });
        matches.forEach(function(el,i){ if(!matchSeen["mt"+i]&&pageEl.contains(el)) lockMatch(el,i,true); });
        sequences.forEach(function(el,i){ if(!seqSeen["sq"+i]&&pageEl.contains(el)) lockSeq(el,i,true); });
        fills.forEach(function(el,i){ if(!fillSeen["fl"+i]&&pageEl.contains(el)) lockFill(el,i,true); });
        drags.forEach(function(el,i){ if(!dragSeen["dd"+i]&&pageEl.contains(el)) lockDrag(el,i,true); });
        hotspots.forEach(function(el,i){ if(!hotSeen["ht"+i]&&pageEl.contains(el)) lockHotspot(el,i,true); });
        updateProgress();
      }
      function focusPage(idx){
        var np = pageEls[idx]; if (!np) return;
        np.scrollIntoView({ behavior: "smooth", block: "start" });
        var h = np.querySelector(".nv-band, h1, h2, h3");
        if (h) { if (!h.hasAttribute("tabindex")) h.setAttribute("tabindex", "-1"); try { h.focus(); } catch (e) {} }
      }
      function showPage(p){
        if (!PAGED || !pageEls.length) return;
        if (p < 0) p = 0; if (p > pageEls.length - 1) p = pageEls.length - 1;
        curPage = p;
        pageEls.forEach(function(pageEl, i){
          var on = i === p;
          pageEl.hidden = !on;
          if (on) pageEl.removeAttribute("inert"); else pageEl.setAttribute("inert", "");
        });
        loc = null;   // paged nav supersedes the scroll-anchor resume hint
        save();       // no-op while restoring; persists `pg` otherwise (only for paged courses)
        refreshPager();
      }
      if (PAGED) {
        var main = document.querySelector(".nv-main");
        if (main) {
          // Partition main's top-level children into contiguous runs; a new run starts at each
          // LEAD wave (a .nv-transition immediately followed by a .nv-section). Modals are held
          // aside and re-appended after the pages.
          var kids = Array.prototype.slice.call(main.children), runs = [], run = [], heldModals = [];
          kids.forEach(function(node){
            if (node.classList && node.classList.contains("nv-modal")) { heldModals.push(node); return; }
            var isLead = node.classList && node.classList.contains("nv-transition")
              && node.nextElementSibling && node.nextElementSibling.classList
              && node.nextElementSibling.classList.contains("nv-section");
            if (isLead && run.length) { runs.push(run); run = []; }
            run.push(node);
          });
          if (run.length) runs.push(run);
          if (runs.length > 1) {   // only paginate when the course actually has sections to split
            runs.forEach(function(r, p){
              var page = document.createElement("div");
              page.className = "nv-page";
              page.setAttribute("role", "group");
              page.setAttribute("aria-label", "Section " + (p + 1) + " of " + runs.length);
              main.insertBefore(page, r[0]);
              r.forEach(function(node){ page.appendChild(node); });
              pageEls.push(page);
            });
            heldModals.forEach(function(m){ main.appendChild(m); });   // modals live outside the pages
            pageEls.forEach(function(page, p){
              pageReq[p] = pageInteractive(page);
              var isLast = p === pageEls.length - 1;
              // Non-last pages always get an advance control. In DEFERRED mode the LAST page ALSO
              // gets one ("Submit exam") — submitting it scores the final section and lets a learner
              // who answered everything actually complete (the #13 fix).
              if (!isLast || DEFERRED) {
                var nav = document.createElement("div"); nav.className = "nv-page-nav";
                var count = document.createElement("span"); count.className = "nv-page-count";
                count.textContent = "Section " + (p + 1) + " of " + pageEls.length;
                var btn = document.createElement("button");
                btn.type = "button";
                if (DEFERRED) {
                  btn.className = "nv-btn nv-page-submit";
                  btn.textContent = isLast ? "Submit exam" : "Submit section";
                  btn.disabled = false;   // deferred: submit any time (blanks score wrong)
                } else {
                  btn.className = "nv-btn nv-page-next";
                  btn.textContent = "Next"; btn.disabled = true;   // gated until the page's interactions are done
                }
                page.__nextBtn = btn;
                (function(idx, pageEl, last){
                  btn.addEventListener("click", function(){
                    if (btn.disabled) return;
                    if (DEFERRED) {
                      if (sectionHasBlank(pageEl) && !window.confirm("Some items in this section are unanswered. Submit the section anyway? Unanswered items are marked incorrect.")) return;
                      btn.disabled = true;          // one submit per section (blocks are now scored/locked)
                      submitSection(pageEl);        // scores this section → updateProgress → (on last) completion → Finish
                      if (!last) { showPage(idx + 1); focusPage(idx + 1); }
                      return;
                    }
                    showPage(idx + 1); focusPage(idx + 1);
                  });
                })(p, page, isLast);
                nav.appendChild(count); nav.appendChild(btn);
                page.appendChild(nav);
              }
            });
            // initial visibility WITHOUT persisting (restore below may override with resumed.pg)
            pageEls.forEach(function(pageEl, i){ var on = i === 0; pageEl.hidden = !on; if (!on) pageEl.setAttribute("inert", ""); });
          } else {
            PAGED = false;   // no sections → nothing to paginate; behave as an unpaged scroll
          }
        } else {
          PAGED = false;
        }
      }

      /* Completion floor */
      if (endEl && "IntersectionObserver" in window) { var io=new IntersectionObserver(function(es){ es.forEach(function(e){ if(e.isIntersecting){ reachedEnd=true; updateProgress(); } }); }); io.observe(endEl); }
      else { reachedEnd = true; }

      /* End button — disabled until complete (set by render); on click leave/advance */
      if (exitBtn) {
        exitBtn.disabled = true;
        exitBtn.addEventListener("click", function () {
          if (exitBtn.disabled) return;
          if (RT) RT.quit();
          exitBtn.disabled = true;
          var ru = RT && RT.returnURL && RT.returnURL();
          if (ru) { location.href = ru; return; }
          try { window.top.close(); } catch (e) {}
          window.close();
        });
      }

      /* Restore prior progress */
      if (resumed) { restoring = true;
        (resumed.g||[]).forEach(function(gi){ if(gates[gi]) passGate(gates[gi],gi); });
        Object.keys(resumed.k||{}).forEach(function(ki){ var r=resumed.k[ki]; if(kcs[ki]&&r){
          if(r.multi) lockKcMulti(kcs[ki], +ki, parseMultiSel(r.opt), r.ok);
          else lockKc(kcs[ki],+ki,r.opt,r.ok); } });
        (resumed.m||[]).forEach(function(mk){ mediaSeen[mk]=true; });
        (resumed.o||[]).forEach(function(ok){ openSeen[ok]=true; });
        Object.keys(resumed.s||{}).forEach(function(sk){ var idx=+sk.slice(1), st=resumed.s[sk];
          if (sorts[idx] && st){ var picks=st.picks||[];
            if (picks.length){
              Array.prototype.slice.call(sorts[idx].querySelectorAll(".nv-sort-item")).forEach(function(li,n){
                var p=li.querySelector(".nv-sort-pick"); if(p&&picks[n]!=null) p.value=picks[n]; });
              lockSort(sorts[idx], idx);
            } else {
              markSortDone(sorts[idx], idx, st);   // picks were dropped to fit suspend_data (ok+got/max kept)
            }
          } });
        Object.keys(resumed.mt||{}).forEach(function(mk){ var idx=+mk.slice(2), st=resumed.mt[mk];  // M12 matching
          if (matches[idx] && st){ var picks=st.picks||[];
            if (picks.length){
              Array.prototype.slice.call(matches[idx].querySelectorAll(".nv-match-item")).forEach(function(li,n){
                var p=li.querySelector(".nv-match-pick"); if(p&&picks[n]!=null) p.value=picks[n]; });
              lockMatch(matches[idx], idx);
            } else {
              markMatchDone(matches[idx], idx, st);     // picks were dropped to fit suspend_data
            }
          } });
        Object.keys(resumed.sq||{}).forEach(function(qk){ var idx=+qk.slice(2), st=resumed.sq[qk];  // M12 sequencing
          if (sequences[idx] && st){ var picks=st.picks||[];
            if (picks.length){
              Array.prototype.slice.call(sequences[idx].querySelectorAll(".nv-seq-item")).forEach(function(li,n){
                var p=li.querySelector(".nv-seq-pick"); if(p&&picks[n]!=null) p.value=picks[n]; });
              lockSeq(sequences[idx], idx);
            } else {
              markSeqDone(sequences[idx], idx, st);     // picks were dropped to fit suspend_data
            }
          } });
        Object.keys(resumed.fl||{}).forEach(function(fk){ var idx=+fk.slice(2), st=resumed.fl[fk];  // M12 fill-in-the-blank
          if (fills[idx] && st){ var inputs=st.inputs||[];
            if (inputs.length){
              Array.prototype.slice.call(fills[idx].querySelectorAll(".nv-fill-input")).forEach(function(inp,n){
                if(inputs[n]!=null) inp.value=inputs[n]; });
              lockFill(fills[idx], idx);
            } else {
              markFillDone(fills[idx], idx, st);        // inputs were dropped to fit suspend_data
            }
          } });
        Object.keys(resumed.dd||{}).forEach(function(dk){ var idx=+dk.slice(2), st=resumed.dd[dk];  // dragDrop
          if (drags[idx] && st){ var picks=st.picks||[];
            if (picks.length){
              Array.prototype.slice.call(drags[idx].querySelectorAll(".nv-drag-item")).forEach(function(li,n){
                li.setAttribute("data-cid","c"+n);
                var p=li.querySelector(".nv-drag-pick"); if(p&&picks[n]!=null){ p.value=picks[n]; placeChip(drags[idx], li, picks[n]); } });
              lockDrag(drags[idx], idx);
            } else {
              markDragDone(drags[idx], idx, st);        // picks were dropped to fit suspend_data
            }
          } });
        Object.keys(resumed.ht||{}).forEach(function(hk){ var idx=+hk.slice(2), st=resumed.ht[hk];  // hotspot
          if (hotspots[idx] && st){ var sel=st.sel;
            if (sel && sel.length!=null){
              Array.prototype.slice.call(hotspots[idx].querySelectorAll(".nv-hotspot-spot")).forEach(function(sp,n){
                if (sel.indexOf(n) >= 0){ sp.setAttribute("aria-pressed","true"); sp.classList.add("is-selected"); } });
              lockHotspot(hotspots[idx], idx);
            } else {
              markHotspotDone(hotspots[idx], idx, st);   // selection was dropped to fit suspend_data
            }
          } });
        Object.keys(resumed.ws||{}).forEach(function(wk){ var idx=+wk.slice(2), st=resumed.ws[wk];  // wordSearch
          if (wordsearches[idx] && st){ markWsDone(wordsearches[idx], idx, st); } });   // grid paths aren't stored → re-mark found words + lock
        Object.keys(resumed.cw||{}).forEach(function(ck){ var idx=+ck.slice(2), st=resumed.cw[ck];  // crossword
          if (crosswords[idx] && st){ markCwDone(crosswords[idx], idx, st); } });   // refill surviving letters (or blank under byte pressure) + lock
        Object.keys(resumed.gs||{}).forEach(function(gk){ var idx=+gk.slice(2), st=resumed.gs[gk];  // gameShow
          if (gameshows[idx] && st && gameshows[idx].__gsRestore){ gameshows[idx].__gsRestore(st); } });   // per-slice marks (or just the tally under byte pressure) + lock
        Object.keys(resumed.qb||{}).forEach(function(qk){ var idx=+qk.slice(2), st=resumed.qb[qk];  // quizBoard
          if (quizboards[idx] && st && quizboards[idx].__qbRestore){ quizboards[idx].__qbRestore(st); } });   // per-tile marks (or just the tally under byte pressure) + lock
        Object.keys(resumed.ss||{}).forEach(function(sk){ var idx=+sk.slice(2), st=resumed.ss[sk];  // speedStreak
          if (speedstreaks[idx] && st && speedstreaks[idx].__ssRestore){ speedstreaks[idx].__ssRestore(st); } });   // per-round marks (or just the tally under byte pressure) + lock
        Object.keys(resumed.wm||{}).forEach(function(wk){ var idx=+wk.slice(2), st=resumed.wm[wk];  // whackAMole
          if (whackamoles[idx] && st && whackamoles[idx].__wamRestore){ whackamoles[idx].__wamRestore(st); } });   // re-show the final tally + lock (per-mole hits dropped under byte pressure)
        Object.keys(resumed.mm||{}).forEach(function(mk){ var idx=+mk.slice(2), st=resumed.mm[mk];  // memoryMatch
          if (memorymatches[idx] && st && memorymatches[idx].__mmRestore){ memorymatches[idx].__mmRestore(st); } });   // re-show every pair matched + the tally + lock (mid-game board dropped under byte pressure)
        Object.keys(resumed.hg||{}).forEach(function(hk){ var idx=+hk.slice(2), st=resumed.hg[hk];  // hangman
          if (hangmen[idx] && st && hangmen[idx].__hgRestore){ hangmen[idx].__hgRestore(st); } });   // reveal the word + lock (only win/loss survives byte pressure)
        Object.keys(resumed.wof||{}).forEach(function(wk){ var idx=+wk.slice(3), st=resumed.wof[wk];  // wheelOfFortune
          if (wheels[idx] && st && wheels[idx].__wofRestore){ wheels[idx].__wofRestore(st); } });   // reveal the puzzle + lock (only solved/completed survives byte pressure)
        Object.keys(resumed.ix||{}).forEach(function(xk){ var idx=+xk.slice(2), st=resumed.ix[xk];  // E1 interaction engine
          if (interactions[idx] && st && interactions[idx].__ixRestore){ interactions[idx].__ixRestore(st); } });   // restore the final var/state snapshot (or just the completion record under byte pressure) + lock
        Object.keys(resumed.sm||{}).forEach(function(mk){ var idx=+mk.slice(2), st=resumed.sm[mk];  // simulation (SIM Studio)
          if (sims[idx] && st && sims[idx].__simRestore){ sims[idx].__simRestore(st); } });   // jump to the last frame + re-mark complete (frame index dropped under byte pressure)
        Object.keys(resumed.db||{}).forEach(function(bk){ var idx=+bk.slice(2), st=resumed.db[bk];  // dunkBooth (arcade reward)
          if (dunkbooths[idx] && st && dunkbooths[idx].__dunkRestore){ dunkbooths[idx].__dunkRestore(st); } });   // re-show the dunk tally + mark complete (only the tally survives byte pressure)
        Object.keys(resumed.bp||{}).forEach(function(pk){ var idx=+pk.slice(2), st=resumed.bp[pk];  // balloonPop (arcade reward)
          if (balloons[idx] && st && balloons[idx].__balloonRestore){ balloons[idx].__balloonRestore(st); } });   // re-show the pop tally + mark complete (only the tally survives byte pressure)
        Object.keys(resumed.sg||{}).forEach(function(gk){ var idx=+gk.slice(2), st=resumed.sg[gk];  // shootingGallery (arcade reward)
          if (galleries[idx] && st && galleries[idx].__galleryRestore){ galleries[idx].__galleryRestore(st); } });   // re-show the hit tally + mark complete (only the tally survives byte pressure)
        Object.keys(resumed.pl||{}).forEach(function(pk){ var idx=+pk.slice(2), st=resumed.pl[pk];  // poll
          if (polls[idx] && st && polls[idx].__pollRestore){ polls[idx].__pollRestore(st); } });   // reselect the picked option + reveal + lock
        Object.keys(resumed.rf||{}).forEach(function(fk){ var idx=+fk.slice(2), st=resumed.rf[fk];  // C7 reflection
          if (reflections[idx] && st && reflections[idx].__rfRestore){ reflections[idx].__rfRestore(st); } });   // re-fill the typed text (dropped under byte pressure), reveal the model answer + lock
        Object.keys(resumed.sc||{}).forEach(function(ck){ var idx=+ck.slice(2), st=resumed.sc[ck];  // wordScramble
          if (wordscrambles[idx] && st && wordscrambles[idx].__scRestore){ wordscrambles[idx].__scRestore(st); } });   // reveal the term + lock (only {ok} survives byte pressure)
        Object.keys(resumed.sh||{}).forEach(function(hk){ var idx=+hk.slice(2), st=resumed.sh[hk];  // spotHazard
          if (spothazards[idx] && st && spothazards[idx].__shRestore){ spothazards[idx].__shRestore(st); } });   // re-lock the field + re-show the tally (per-spot hits dropped, mirrors whackAMole)
        loc = resumed.loc || null; restoring = false;
        if (PAGED) { showPage(resumed.pg != null ? resumed.pg : 0); }   // section pager — return to the saved page
        else if (loc){ var tgt = loc.t==="g"?gates[loc.i]:(loc.t==="kc"?kcs[loc.i]:null); if(tgt) try{ tgt.scrollIntoView({block:"start"}); }catch(e){} }
      }

      updateProgress();
      window.addEventListener("pagehide", function(){ if (RT) RT.quit(); });
      window.addEventListener("beforeunload", function(){ if (RT) RT.quit(); });
    });
  });

  /* =========================== Entrance animations =========================== */
  /* Named entrance effects as each top-level block enters the viewport: simple
     blocks rotate through a tasteful palette ('up' = Float In dominant, with
     occasional Slide In From Left/Right); grouped blocks (cards, comparison
     panels, timeline, infographic items) fade their shell and CASCADE their
     children with a stagger. Purely presentational and independent of the LMS
     runtime. We add the classes ONLY when animations are on (body[data-anim] !=
     "0"), IntersectionObserver is available, and motion is allowed — so a no-JS,
     no-observer, reduced-motion, or animations-off visitor always sees fully-
     visible content. Gated blocks (their own reveal) and modals are skipped. */
  if (HAS_DOM) ready(function () {
    if (document.body.getAttribute("data-anim") === "0") return;
    var reduce = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    if (reduce || !("IntersectionObserver" in window)) return;
    var blocks = Array.prototype.slice.call(document.querySelectorAll(".nv-main .nv-block"))
      .filter(function (el) { return el.closest && !el.closest(".nv-gated") && !el.closest(".nv-modal"); });
    if (!blocks.length) return;
    var DIRS = ["up", "left", "up", "right"];   // Float In dominant; both slide sides appear
    var GROUP_ITEMS = ".nv-card, .nv-tl-item, .nv-cmp-panel, .nv-ig-card, .nv-ig-goal";
    var si = 0;                                 // advance the palette per simple block only,
                                                // so grouped blocks don't starve the slide-ins
    blocks.forEach(function (el) {
      var kids = Array.prototype.slice.call(el.querySelectorAll(GROUP_ITEMS));
      if (kids.length > 1) {                    // grouped block: fade shell, cascade items
        el.classList.add("nv-anim", "nv-anim-fade");
        kids.forEach(function (k, j) {
          k.classList.add("nv-anim", "nv-anim-up", "nv-anim-kid");
          k.style.setProperty("--nv-anim-delay", Math.min(0.08 + j * 0.11, 0.8).toFixed(2) + "s");
        });
      } else {                                  // simple block: one directional effect
        el.classList.add("nv-anim", "nv-anim-" + DIRS[si++ % DIRS.length]);
      }
    });
    var ro = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) {
        if (!e.isIntersecting) return;
        e.target.classList.add("nv-in");
        var kids = e.target.querySelectorAll(".nv-anim-kid");
        Array.prototype.slice.call(kids).forEach(function (k) { k.classList.add("nv-in"); });
        ro.unobserve(e.target);
      });
    }, { rootMargin: "0px 0px -8% 0px", threshold: 0.08 });
    blocks.forEach(function (el) { ro.observe(el); });
  });

  // Node-only: expose the pure helpers for unit tests (no-op in the browser,
  // where `module` is undefined). The DOM bootstrap above is HAS_DOM-guarded, so
  // requiring this file under node defines + exports without touching the DOM.
  if (typeof module !== "undefined" && module.exports) {
    module.exports = { utf8len: utf8len, packSorts: packSorts, packKcs: packKcs,
      fitSuspend: fitSuspend, multiAllCorrect: multiAllCorrect, kcLocks: kcLocks,
      scorePct: scorePct, parseMultiSel: parseMultiSel, resolveScene: resolveScene,
      aggregateScore: aggregateScore, reviewEntries: reviewEntries, packSeen: packSeen, tallyExact: tallyExact, scoreHotspot: scoreHotspot,
      buildCwModel: buildCwModel, cwMove: cwMove,
      normFill: normFill, fillScore: fillScore,
      makeRng: makeRng, seededShuffle: seededShuffle, drawPool: drawPool, packBank: packBank,
      ssScore: ssScore, ssCombo: ssCombo, wamScore: wamScore, scSolved: scSolved, mmScore: mmScore, hgState: hgState, wofState: wofState, simProgress: simProgress, dunkZone: dunkZone, dunkHit: dunkHit, dunkProgress: dunkProgress, powerAt: powerAt, balloonLevel: balloonLevel, aimLanding: aimLanding, hitTest: hitTest, popProgress: popProgress, galleryLevel: galleryLevel, galleryHit: galleryHit, shotProgress: shotProgress, pageComplete: pageComplete, celebrateAllowed: celebrateAllowed,
      xpCat: xpCat, xpWeight: xpWeight, xpForResult: xpForResult, xpTotals: xpTotals, tierFor: tierFor,
      revealDelay: revealDelay,
      ixCondOk: ixCondOk, ixApplyActions: ixApplyActions, ixStep: ixStep, ixInitState: ixInitState, ixValue: ixValue, ixNum: ixNum };
  }
})();
