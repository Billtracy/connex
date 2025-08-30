/** ====================== Geometry & Graph ====================== */
const NODES = {
  A:{x:20,  y:200}, B:{x:20,  y:20},  C:{x:150, y:20},  D:{x:280, y:20},
  E:{x:280, y:200}, F:{x:280, y:380}, G:{x:150, y:380}, H:{x:20,  y:380},
  X:{x:150, y:200}
};
/** Edges:
 * Perimeter: top (B–C–D), bottom (H–G–F), left (B–A–H), right (D–E–F)
 * Cross lines: AXE, CXG, BXF, HXD
 */
const EDGES = [
  // perimeter
  ['B','C'], ['C','D'],
  ['H','G'], ['G','F'],
  ['B','A'], ['A','H'],
  ['D','E'], ['E','F'],
  // cross through X
  ['A','X'], ['X','E'],
  ['C','X'], ['X','G'],
  ['B','X'], ['X','F'],
  ['H','X'], ['X','D'],
];
const WINS = [['A','X','E'],['G','X','C'],['H','X','D'],['B','X','F']];
const START = { p1:['B','C','D'], p2:['H','G','F'] };
const PIECE_SIZE = 28;

const svg = document.getElementById('board');
const edgesG = document.getElementById('edges');
const nodesG = document.getElementById('nodes');
const piecesG = document.getElementById('pieces');
const winLine = document.getElementById('winline');
const turnEl = document.getElementById('turn');
const logEl = document.getElementById('log');

svg.addEventListener('click',(ev)=>{
  if (tapSel && !ev.target.closest('.node') && !ev.target.closest('.piece')){
    highlight(tapSel.legal,false);
    tapSel=null;
  }
});

const adj = {};
for (const [u,v] of EDGES){ (adj[u]??=new Set()).add(v); (adj[v]??=new Set()).add(u); }

function drawEdges(){
  edgesG.innerHTML='';
  EDGES.forEach(([u,v])=>{
    const l = document.createElementNS('http://www.w3.org/2000/svg','line');
    l.setAttribute('class','edge');
    l.setAttribute('x1',NODES[u].x); l.setAttribute('y1',NODES[u].y);
    l.setAttribute('x2',NODES[v].x); l.setAttribute('y2',NODES[v].y);
    edgesG.appendChild(l);
  });
}
function drawNodes(){
  nodesG.innerHTML='';
  for (const [k,pt] of Object.entries(NODES)){
    const g = document.createElementNS('http://www.w3.org/2000/svg','g');
    g.setAttribute('class','node'); g.setAttribute('data-id',k);
    const c = document.createElementNS('http://www.w3.org/2000/svg','circle');
    c.setAttribute('cx',pt.x); c.setAttribute('cy',pt.y); c.setAttribute('r',13);
    const t = document.createElementNS('http://www.w3.org/2000/svg','text');
    t.setAttribute('x',pt.x); t.setAttribute('y',pt.y+4);
    t.setAttribute('text-anchor','middle'); t.setAttribute('fill','#555'); t.setAttribute('font-size','10');
    t.textContent=k; g.appendChild(c); g.appendChild(t); nodesG.appendChild(g);

    g.addEventListener('click',()=>{
      if (!tapSel) return;
      const id=g.getAttribute('data-id');
      if (tapSel.legal.has(id)){
        pushHistory();
        state.pieces[tapSel.who][tapSel.idx].at = id;
        state.turn = (state.turn==='p1') ? 'p2' : 'p1';
        log(`${tapSel.who==='p1'?'P1':'P2'}: ${tapSel.from} → ${id}`);
        postMoveActions({side:tapSel.who,idx:tapSel.idx,from:tapSel.from,to:id});
        highlight(tapSel.legal,false);
        tapSel=null;
        renderPieces();
        if (!winner && botEnabled && state.turn==='p2') {
          setTimeout(botMove,220);
        }
      } else {
        highlight(tapSel.legal,false);
        tapSel=null;
      }
    });
  }
}

/** ====================== Game State ====================== */
let state, winner=null, dragging=null, kbNav=null, tapSel=null;
let history = []; // stack of prior states for Undo
let botEnabled = true; // Player 2 is bot
let flipped = false; // board orientation
let botDepth = 4; // max search depth for bot
let botTime = 1000; // ms allotted per bot move

function clone(obj){ return JSON.parse(JSON.stringify(obj)); }

function initialState(){
  return {
    turn: 'p1',
    pieces: {
      p1: START.p1.map(at=>({at})),
      p2: START.p2.map(at=>({at}))
    }
  };
}

function reset(){
  state = initialState();
  history = [];
  winner = null;
  dragging = null;
  tapSel = null;
  winLine.style.display='none';
  updateUI();
  updateModeText();
  renderPieces();
  clearLog();
  log('Game started. P1 moves first.');
}

/** Helpers */
function occupiedAt(s,nodeId){
  for (const p of s.pieces.p1) if (p.at===nodeId) return 'p1';
  for (const p of s.pieces.p2) if (p.at===nodeId) return 'p2';
  return null;
}
function legalTargets(s, from){
  return new Set([...(adj[from]??[])].filter(n=>!occupiedAt(s,n)));
}
function allMoves(s, side){
  const moves = [];
  s.pieces[side].forEach((p,idx)=>{
    for (const to of legalTargets(s,p.at)){
      moves.push({side, idx, from:p.at, to});
    }
  });
  return moves;
}
function applyMove(s, move){
  const ns = clone(s);
  ns.pieces[move.side][move.idx].at = move.to;
  ns.turn = (s.turn==='p1') ? 'p2' : 'p1';
  return ns;
}
function isWin(s){
  for (const [a,x,b] of WINS){
    const oa=occupiedAt(s,a), ox=occupiedAt(s,x), ob=occupiedAt(s,b);
    if (oa && oa===ox && ox===ob) return {player:oa, line:[a,x,b]};
  }
  return null;
}

/** ====================== Heuristic + Bot ====================== */
/* Simple positional heuristic:
   +6 if you own a winning line completed (terminal)
   +2 for controlling X
   +1 per your piece adjacent to X
   +2 for each "two-in-line with X" (e.g., you at A and X, empty E)
   Mirror negative for opponent.
*/
function scoreSide(s, side){
  const other = side==='p1' ? 'p2' : 'p1';
  const youAt = new Set(s.pieces[side].map(p=>p.at));
  const oppAt = new Set(s.pieces[other].map(p=>p.at));
  let sc = 0;

  // Control X
  if (youAt.has('X')) sc += 2;
  // Adjacent to X
  for (const n of (adj['X']??[])) if (youAt.has(n)) sc += 1;

  // Two-in-line threats and completions
  for (const [a,x,b] of WINS){
    const ya = youAt.has(a), yx = youAt.has(x), yb = youAt.has(b);
    const oa = oppAt.has(a), ox = oppAt.has(x), ob = oppAt.has(b);

    if (ya && yx && yb) sc += 6; // already winning (terminal check elsewhere)
    else {
      // two with empty third
      if ((ya && yx && !ob && !oa && !ox && !yb) || (yx && yb && !oa && !ob && !ya)) sc += 2;
    }
    // penalize if opponent close
    if ((oa && ox && !yb) || (ox && ob && !ya)) sc -= 2;
  }
  return sc;
}

function evaluate(s){ return scoreSide(s,'p2') - scoreSide(s,'p1'); } // bot is p2
const TIMEOUT = Symbol('timeout');
function minimax(s, depth, alpha, beta, maximizing, deadline){
  if (deadline && performance.now() > deadline) throw TIMEOUT;
  const win = isWin(s);
  if (win){
    // terminal: huge score
    return (win.player==='p2') ? 1000 : -1000;
  }
  if (depth===0) return evaluate(s);

  const side = maximizing ? 'p2' : 'p1';
  const moves = allMoves(s, side);
  if (moves.length===0) return evaluate(s);

  if (maximizing){
    let best = -Infinity;
    for (const m of moves){
      const ns = applyMove(s,m);
      const val = minimax(ns, depth-1, alpha, beta, false, deadline);
      best = Math.max(best, val);
      alpha = Math.max(alpha, val);
      if (beta <= alpha) break;
    }
    return best;
  } else {
    let best = Infinity;
    for (const m of moves){
      const ns = applyMove(s,m);
      const val = minimax(ns, depth-1, alpha, beta, true, deadline);
      best = Math.min(best, val);
      beta = Math.min(beta, val);
      if (beta <= alpha) break;
    }
    return best;
  }
}

function botMove(){
  if (!botEnabled || winner || state.turn!=='p2') return;
  const moves = allMoves(state,'p2');
  if (moves.length===0) return;

  // Default to first move in case time runs out immediately
  let best = moves[0];

  // Small opening bias: prefer taking X if free and reachable
  for (const m of moves){
    if (m.to==='X'){ best = m; break; }
  }

  if (best.to !== 'X'){ // if no immediate X move, search
    const deadline = performance.now() + botTime;
    let bestScore = -Infinity;
    for (let depth = 1; depth <= botDepth; depth++){
      let currentBest = best;
      let currentBestScore = -Infinity;
      try {
        for (const m of moves){
          const ns = applyMove(state,m);
          const sc = minimax(ns, depth-1, -Infinity, Infinity, false, deadline);
          if (sc > currentBestScore){ currentBestScore = sc; currentBest = m; }
        }
        best = currentBest;
        bestScore = currentBestScore;
      } catch (e){
        if (e === TIMEOUT) break; else throw e;
      }
      if (performance.now() > deadline) break;
    }
  }

  if (best){
    pushHistory();
    state = applyMove(state, best);
    log(`P2: ${best.from} → ${best.to}`);
    postMoveActions(best);
    renderPieces();
  }
}

/** ====================== UI & Interaction ====================== */
function updateUI(){
  turnEl.textContent = `Turn: ${state.turn==='p1'?'Player 1 (blue)':'Player 2 (gold)'}`;
}

function updateModeText(){
  const modeEl = document.getElementById('mode');
  modeEl.textContent = botEnabled ? 'Mode: Human vs Bot (P2)' : 'Mode: Human vs Human';
}

function renderPieces(){
  piecesG.innerHTML='';
  for (const [who,cls] of [['p1','p1'],['p2','p2']]){
    state.pieces[who].forEach((p,idx)=>{
      const g=document.createElementNS('http://www.w3.org/2000/svg','g');
      g.setAttribute('class',`piece ${cls}`); g.setAttribute('data-side',who); g.setAttribute('data-index',idx);
      g.setAttribute('tabindex','0');
      const pt=NODES[p.at];
      const c=document.createElementNS('http://www.w3.org/2000/svg','rect');
      c.setAttribute('x',pt.x-PIECE_SIZE/2);
      c.setAttribute('y',pt.y-PIECE_SIZE/2);
      c.setAttribute('width',PIECE_SIZE);
      c.setAttribute('height',PIECE_SIZE);
      g.appendChild(c); piecesG.appendChild(g);

      // Interaction only for current side and if game not over
      g.addEventListener('pointerdown',(ev)=>{
        if (winner || state.turn!==who) return;
        const legal = legalTargets(state, p.at);
        if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
        dragging={who,idx,from:p.at,x0:pt.x,y0:pt.y,legal,moved:false};
        highlight(legal,true);
        g.setPointerCapture(ev.pointerId);
      });
      g.addEventListener('pointermove',(ev)=>{
        if (!dragging||dragging.idx!==idx||dragging.who!==who) return;
        dragging.moved=true;
        const q=svgPoint(ev);
        g.firstChild.setAttribute('x',q.x-PIECE_SIZE/2);
        g.firstChild.setAttribute('y',q.y-PIECE_SIZE/2);
        
      });
      g.addEventListener('pointerup',(ev)=>{
        if (!dragging||dragging.idx!==idx||dragging.who!==who) return;
        const drop=nearest(svgPoint(ev),dragging.legal);
        if (drop){
          pushHistory();
          state.pieces[who][idx].at = drop;
          state.turn = (state.turn==='p1')?'p2':'p1';
          log(`${who==='p1'?'P1':'P2'}: ${dragging.from} → ${drop}`);
          postMoveActions({side:who,idx,from:dragging.from,to:drop});
          if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
          highlight(dragging.legal,false); dragging=null; renderPieces();
          if (!winner && botEnabled && state.turn==='p2') {
            setTimeout(botMove, 220); // tiny delay feels natural
          }
          return;
        }
        if (!dragging.moved){
          if (tapSel && tapSel.who===who && tapSel.idx===idx){
            highlight(tapSel.legal,false);
            tapSel=null;
          } else {
            if (tapSel) highlight(tapSel.legal,false);
            tapSel={who,idx,from:p.at,legal:dragging.legal};
            highlight(tapSel.legal,true);
          }
          dragging=null; renderPieces();
          return;
        }
        highlight(dragging.legal,false); dragging=null; renderPieces();
        // If bot's turn, let it move after render
        if (!winner && botEnabled && state.turn==='p2') {
          setTimeout(botMove, 220); // tiny delay feels natural
        }
      });

      g.addEventListener('focus',()=>{
        if (winner || state.turn!==who) return;
        const legal=legalTargets(state,p.at);
        if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
        kbNav={who,idx,from:p.at,current:p.at,legal,el:g};
        highlight(legal,true);
      });
      g.addEventListener('blur',()=>{
        if (!kbNav) return;
        highlight(kbNav.legal,false);
        kbNav=null;
        renderPieces();
      });
      g.addEventListener('keydown',(ev)=>{
        if (!kbNav||kbNav.idx!==idx||kbNav.who!==who) return;
        if (['ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(ev.key)){
          ev.preventDefault();
          const {from}=kbNav; const {x:fx,y:fy}=NODES[from];
          let best=null, bestd=Infinity;
          for (const id of kbNav.legal){
            const {x,y}=NODES[id];
            switch(ev.key){
              case 'ArrowUp':
                if (y<fy && fy-y<bestd){best=id; bestd=fy-y;}
                break;
              case 'ArrowDown':
                if (y>fy && y-fy<bestd){best=id; bestd=y-fy;}
                break;
              case 'ArrowLeft':
                if (x<fx && fx-x<bestd){best=id; bestd=fx-x;}
                break;
              case 'ArrowRight':
                if (x>fx && x-fx<bestd){best=id; bestd=x-fx;}
                break;
            }
          }
          if (best){
            kbNav.current=best;
            const pt=NODES[best];
            g.firstChild.setAttribute('x',pt.x-PIECE_SIZE/2);
            g.firstChild.setAttribute('y',pt.y-PIECE_SIZE/2);
          }
        } else if (ev.key==='Enter' || ev.key===' '){
          ev.preventDefault();
          if (kbNav.current!==kbNav.from){
            pushHistory();
            state.pieces[who][idx].at = kbNav.current;
            state.turn = (state.turn==='p1')?'p2':'p1';
            log(`${who==='p1'?'P1':'P2'}: ${kbNav.from} → ${kbNav.current}`);
            postMoveActions({side:who,idx,from:kbNav.from,to:kbNav.current});
            highlight(kbNav.legal,false);
            kbNav=null;
            renderPieces();
            if (!winner && botEnabled && state.turn==='p2') {
              setTimeout(botMove,220);
            }
          }
        }
      });
    });
  }
}

function postMoveActions(lastMove){
  playMoveSound();
  const res = isWin(state);
  if (res){
    winner = res.player;
    drawWinLine(...res.line);
    log(`<b>${winner==='p1'?'P1':'P2'} wins</b> via ${res.line.join('–')}`);
    playWinSound();
  }
  updateUI();
}

function drawWinLine(a,x,b){
  winLine.setAttribute('x1',NODES[a].x); winLine.setAttribute('y1',NODES[a].y);
  winLine.setAttribute('x2',NODES[b].x); winLine.setAttribute('y2',NODES[b].y);
  winLine.style.display='block';
}

function highlight(set,on){
  [...nodesG.children].forEach(g=>{
    const id=g.getAttribute('data-id');
    if (set&&set.has(id)&&on) g.classList.add('active'); else g.classList.remove('active');
  });
}
function svgPoint(ev){ const pt=svg.createSVGPoint(); pt.x=ev.clientX; pt.y=ev.clientY; return pt.matrixTransform(svg.getScreenCTM().inverse()); }
function nearest(pt,allowed){
  const R=20; for (const id of allowed){ const n=NODES[id]; const d2=(n.x-pt.x)**2+(n.y-pt.y)**2; if (d2<=R*R) return id; } return null;
}

/** ====================== History (Undo) & Log ====================== */
function pushHistory(){
  history.push({ state: clone(state), winner });
}
function undo(){
  if (history.length===0) return;
  const prev = history.pop();
  state = prev.state;
  winner = prev.winner;
  if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
  winLine.style.display = winner ? 'block' : 'none';
  updateUI();
  renderPieces();
  log('(undo)');
}
function clearLog(){ logEl.innerHTML=''; }
function log(msg){
  const div = document.createElement('div');
  div.innerHTML = msg;
  logEl.appendChild(div);
  logEl.scrollTop = logEl.scrollHeight;
}

/** ====================== Sound FX ====================== */
const audioCtx = new (window.AudioContext || window.webkitAudioContext)();
function playTone(freq, dur){
  if (audioCtx.state === 'suspended') audioCtx.resume();
  const osc = audioCtx.createOscillator();
  const gain = audioCtx.createGain();
  osc.type = 'sine';
  osc.frequency.value = freq;
  osc.connect(gain);
  gain.connect(audioCtx.destination);
  gain.gain.value = 0.2;
  osc.start();
  gain.gain.exponentialRampToValueAtTime(0.0001, audioCtx.currentTime + dur);
  osc.stop(audioCtx.currentTime + dur);
}
function playMoveSound(){ playTone(660,0.08); }
function playWinSound(){ playTone(880,0.3); setTimeout(()=>playTone(660,0.3),150); }

/** ====================== Boot ====================== */
drawEdges(); drawNodes(); reset();
document.getElementById('reset').onclick = reset;
document.getElementById('undo').onclick = undo;
document.getElementById('mode').onclick = () => {
  botEnabled = !botEnabled;
  updateModeText();
};
const flipBtn = document.getElementById('flip');
flipBtn.onclick = () => {
  flipped = !flipped;
  svg.classList.toggle('flipped', flipped);
  flipBtn.textContent = flipped ? 'Unflip Board' : 'Flip Board';
};
const menu = document.getElementById('menu');
const startBtn = document.getElementById('start');
startBtn.onclick = () => {
  menu.style.display = 'none';
  reset();
};

const depthSel = document.getElementById('difficulty');
depthSel.onchange = (e) => { botDepth = parseInt(e.target.value,10); };
const timeSel = document.getElementById('movetime');
botTime = parseInt(timeSel.value,10);
timeSel.onchange = (e) => { botTime = parseInt(e.target.value,10); };
