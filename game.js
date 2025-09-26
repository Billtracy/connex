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
const analyzeBtn = document.getElementById('analyze');
const analysisPanel = document.getElementById('analysis-panel');
const analysisInfo = document.getElementById('analysis-info');
const analysisPrev = document.getElementById('analysis-prev');
const analysisNext = document.getElementById('analysis-next');
const analysisExit = document.getElementById('analysis-exit');
const resetBtn = document.getElementById('reset');
const undoBtn = document.getElementById('undo');
const hostBtn = document.getElementById('host-session');
const joinBtn = document.getElementById('join-session');
const leaveBtn = document.getElementById('leave-session');
const roomCodeEl = document.getElementById('room-code');
const joinCodeInput = document.getElementById('join-code');
const connectionStatusEl = document.getElementById('connection-status');

const configStatusEl = document.getElementById('config-status');
const applyConfigBtn = document.getElementById('apply-config');
const firebaseInputs = document.querySelectorAll('[data-firebase-key]');


svg.addEventListener('click',(ev)=>{
  if (analysisMode) return;
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
      if (analysisMode) return;
      if (!tapSel) return;
      const id=g.getAttribute('data-id');
      if (tapSel.legal.has(id)){
        pushHistory();
        const move = { side: tapSel.who, idx: tapSel.idx, from: tapSel.from, to: id };
        state.pieces[move.side][move.idx].at = move.to;
        state.turn = (state.turn==='p1') ? 'p2' : 'p1';
        updateHashAfterMove(state, move);
        log(`${move.side==='p1'?'P1':'P2'}: ${move.from} → ${move.to}`);
        postMoveActions(move);
        broadcastMove(move);
        highlight(tapSel.legal,false);
        tapSel=null;
        renderPieces();
        if (!winner && botEnabled && state.turn===botSide) {
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
let moveHistory = []; // moves played for post-game analysis
let botEnabled = true; // play against bot?
let botSide = 'p2'; // which side the bot controls
let flipped = false; // board orientation
let botDepth = 4; // max search depth for bot
let botTime = 1000; // ms allotted per bot move
let analysisData = null, analysisIdx = 0, analysisMode = false, analysisWinner = null;
let firebaseConfig = window.FIREBASE_DEFAULT_CONFIG || null;
let firebaseAppInstance = null;
let firestoreDb = null;
let peerConnection = null;
let dataChannel = null;
let roomDocRef = null;
let roomUnsub = null;
let candidateUnsubs = [];
let isHost = false;
let onlineSession = false;
let peerConnected = false;
let localSide = null;
let remoteSide = null;
let botEnabledBeforeOnline = null;
let pendingRoomCode = null;
let awaitingInitialState = false;
const ICE_SERVERS = [{ urls: 'stun:stun.l.google.com:19302' }];
const DATA_CHANNEL_LABEL = 'connex-moves';
const MULTIPLAYER_PROTOCOL_VERSION = 1;

function clone(obj){ return JSON.parse(JSON.stringify(obj)); }

// Zobrist hashing
const ZOBRIST = (() => {
  const rand = () => Math.floor(Math.random() * 2 ** 32);
  const table = { turn: rand() };
  for (const id of Object.keys(NODES)) {
    table['p1' + id] = rand();
    table['p2' + id] = rand();
  }
  return table;
})();

function computeHash(s){
  let h = s.turn === 'p2' ? ZOBRIST.turn : 0;
  for (const p of s.pieces.p1) h ^= ZOBRIST['p1' + p.at];
  for (const p of s.pieces.p2) h ^= ZOBRIST['p2' + p.at];
  return h;
}

function updateHashAfterMove(s, move){
  s.hash ^= ZOBRIST[move.side + move.from];
  s.hash ^= ZOBRIST[move.side + move.to];
  s.hash ^= ZOBRIST.turn;
}

function initialState(){
  const st = {
    turn: 'p1',
    pieces: {
      p1: START.p1.map(at=>({at})),
      p2: START.p2.map(at=>({at}))
    }
  };
  st.hash = computeHash(st);
  return st;
}

function reset(){
  state = initialState();
  botSide = Math.random() < 0.5 ? 'p1' : 'p2';
  history = [];
  moveHistory = [];
  winner = null;
  dragging = null;
  tapSel = null;
  winLine.style.display='none';
  analyzeBtn.style.display='none';
  analysisPanel.style.display='none';
  svg.classList.remove('analyzing');
  analysisData = null; analysisIdx = 0; analysisMode = false; analysisWinner = null;
  analysisInfo.textContent='Start position';
  highlight(null,false);
  TT.clear();
  updateUI();
  updateModeText();
  if (!onlineSession) setUndoAvailability(true);
  renderPieces();
  clearLog();
  log(`Game started. ${botSide==='p1'?'Bot':'Player'} as P1 moves first.`);
  if (botEnabled && botSide==='p1') setTimeout(botMove,220);
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
  const other = side==='p1' ? 'p2' : 'p1';
  s.pieces[side].forEach((p,idx)=>{
    for (const to of legalTargets(s,p.at)){
      // simulate board after move for ranking
      const youAt = new Set(s.pieces[side].map(q=>q.at));
      const oppAt = new Set(s.pieces[other].map(q=>q.at));
      youAt.delete(p.at); youAt.add(to);

      let rank = 0;
      if (to === 'X') rank += 3; // center move
      else if ((adj['X']??new Set()).has(to)) rank += 1; // toward center

      for (const [a,x,b] of WINS){
        const ya = youAt.has(a), yx = youAt.has(x), yb = youAt.has(b);
        const oa = oppAt.has(a), ox = oppAt.has(x), ob = oppAt.has(b);
        if (ya && yx && yb) rank += 5; // complete line
        else if ((ya && yx && !yb && !ob) || (yx && yb && !ya && !oa)) rank += 2; // create threat
      }

      moves.push({side, idx, from:p.at, to, rank});
    }
  });
  return moves;
}
function applyMove(s, move){
  const ns = clone(s);
  ns.hash = s.hash;
  ns.pieces[move.side][move.idx].at = move.to;
  ns.turn = (s.turn==='p1') ? 'p2' : 'p1';
  updateHashAfterMove(ns, move);
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
/* Simple positional heuristic (weights tuned via quick self‑play):
   +6 if you own a winning line completed (terminal)
   +2 for controlling X
   +1 per your piece adjacent to X
   +2 for each "two-in-line with X" (e.g., you at A and X, empty E)
   +0.5 per perimeter node you control
   +4 for potential forks (one move creates two winning threats)
   +0.2 per legal move (mobility)
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

  // Control of perimeter nodes encourages board presence
  for (const n of ['A','B','C','D','E','F','G','H'])
    if (youAt.has(n)) sc += 0.5;

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

  // Potential forks: empty nodes completing two lines at once
  for (const n of Object.keys(NODES)){
    if (youAt.has(n) || oppAt.has(n)) continue;
    let c = 0;
    for (const line of WINS){
      if (!line.includes(n)) continue;
      const [p,q] = line.filter(m=>m!==n);
      if (youAt.has(p) && youAt.has(q)) c++;
    }
    if (c >= 2) sc += 4;
  }

  // Mobility: more legal moves offers flexibility
  let mob = 0;
  for (const p of s.pieces[side]) mob += legalTargets(s,p.at).size;
  sc += mob * 0.2;
  return sc;
}

function evaluate(s){
  const opp = botSide==='p1' ? 'p2' : 'p1';
  return scoreSide(s,botSide) - scoreSide(s,opp);
}
const TIMEOUT = Symbol('timeout');
const TT = new Map(); // transposition table
let nodesSearched = 0; // count nodes visited during search
function minimax(s, depth, alpha, beta, maximizing, deadline){
  nodesSearched++;
  if (deadline && performance.now() > deadline) throw TIMEOUT;
  const hash = s.hash ?? computeHash(s);
  const tt = TT.get(hash);
  if (tt && tt.depth >= depth){
    if (tt.flag === 'exact') return tt.score;
    if (tt.flag === 'lower') alpha = Math.max(alpha, tt.score);
    else if (tt.flag === 'upper') beta = Math.min(beta, tt.score);
    if (alpha >= beta) return tt.score;
  }
  const win = isWin(s);
  if (win){
    const sc = (win.player===botSide) ? 1000 : -1000;
    TT.set(hash,{depth,score:sc,flag:'exact'});
    return sc;
  }
  if (depth===0){
    const sc = evaluate(s);
    TT.set(hash,{depth,score:sc,flag:'exact'});
    return sc;
  }

  const side = maximizing ? botSide : (botSide==='p1' ? 'p2' : 'p1');
  const moves = allMoves(s, side);
  if (moves.length===0){
    const sc = evaluate(s);
    TT.set(hash,{depth,score:sc,flag:'exact'});
    return sc;
  }
  moves.sort((a,b)=>b.rank - a.rank);

  const alphaOrig = alpha, betaOrig = beta;
  let best;
  if (maximizing){
    best = -Infinity;
    for (const m of moves){
      const ns = applyMove(s,m);
      const val = minimax(ns, depth-1, alpha, beta, false, deadline);
      best = Math.max(best, val);
      alpha = Math.max(alpha, val);
      if (beta <= alpha) break;
    }
  } else {
    best = Infinity;
    for (const m of moves){
      const ns = applyMove(s,m);
      const val = minimax(ns, depth-1, alpha, beta, true, deadline);
      best = Math.min(best, val);
      beta = Math.min(beta, val);
      if (beta <= alpha) break;
    }
  }
  let flag = 'exact';
  if (best <= alphaOrig) flag = 'upper';
  else if (best >= betaOrig) flag = 'lower';
  TT.set(hash,{depth,score:best,flag});
  return best;
}

function botMove(){
  if (!botEnabled || winner || state.turn!==botSide) return;
  const moves = allMoves(state,botSide);
  if (moves.length===0) return;
  nodesSearched = 0;
  moves.sort((a,b)=>b.rank - a.rank);

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
    log(`${botSide==='p1'?'P1':'P2'}: ${best.from} → ${best.to}`);
    log(`Nodes searched: ${nodesSearched}`);
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
  if (botEnabled){
    modeEl.textContent = `Mode: Human vs Bot (Bot: ${botSide==='p1'?'P1':'P2'})`;
  } else {
    modeEl.textContent = 'Mode: Human vs Human';
  }
}

function setUndoAvailability(enabled){
  if (!undoBtn) return;
  undoBtn.classList.toggle('disabled', !enabled);
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
        if (onlineSession && localSide && who!==localSide) return;
        if (winner || state.turn!==who || analysisMode) return;
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
          const move = { side: who, idx, from: dragging.from, to: drop };
          state.pieces[move.side][move.idx].at = move.to;
          state.turn = (state.turn==='p1')?'p2':'p1';
          updateHashAfterMove(state, move);
          log(`${move.side==='p1'?'P1':'P2'}: ${move.from} → ${move.to}`);
          postMoveActions(move);
          broadcastMove(move);
          if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
          highlight(dragging.legal,false); dragging=null; renderPieces();
          if (!winner && botEnabled && state.turn===botSide) {
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
        if (!winner && botEnabled && state.turn===botSide) {
          setTimeout(botMove, 220); // tiny delay feels natural
        }
      });

      g.addEventListener('focus',()=>{
        if (onlineSession && localSide && who!==localSide) return;
        if (winner || state.turn!==who || analysisMode) return;
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
        if (onlineSession && localSide && who!==localSide) return;
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
            const move = { side: who, idx, from: kbNav.from, to: kbNav.current };
            state.pieces[move.side][move.idx].at = move.to;
            state.turn = (state.turn==='p1')?'p2':'p1';
            updateHashAfterMove(state, move);
            log(`${move.side==='p1'?'P1':'P2'}: ${move.from} → ${move.to}`);
            postMoveActions(move);
            broadcastMove(move);
            highlight(kbNav.legal,false);
            kbNav=null;
            renderPieces();
            if (!winner && botEnabled && state.turn===botSide) {
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
  moveHistory.push(lastMove);
  const res = isWin(state);
  if (res){
    winner = res.player;
    drawWinLine(...res.line);
    log(`<b>${winner==='p1'?'P1':'P2'} wins</b> via ${res.line.join('–')}`);
    playWinSound();
    analyzeBtn.style.display='inline-block';
  }
  updateUI();
}

function broadcastMove(move){
  if (!peerConnected || !dataChannel || dataChannel.readyState !== 'open') return;
  if (localSide && move.side !== localSide) return;
  sendPeerMessage('move', { ...move, hash: state.hash });
}

function handleRemoteMove(payload){
  if (!payload || !onlineSession || !remoteSide) return;
  if (awaitingInitialState) return;
  const side = payload.side;
  const idx = Number(payload.idx);
  if (side !== remoteSide || Number.isNaN(idx)) return;
  if (analysisMode){
    analysisExit.onclick();
  }
  if (state.turn !== remoteSide){
    log('<span class="warn">Ignoring out-of-turn move from peer.</span>');
    return;
  }
  const pieceList = state.pieces[side];
  if (!pieceList || !pieceList[idx] || pieceList[idx].at !== payload.from){
    log('<span class="warn">Invalid move from peer (piece mismatch).</span>');
    return;
  }
  const legal = legalTargets(state, payload.from);
  if (!legal.has(payload.to)){
    log('<span class="warn">Invalid move from peer (illegal target).</span>');
    return;
  }
  pushHistory();
  pieceList[idx].at = payload.to;
  state.turn = (state.turn === 'p1') ? 'p2' : 'p1';
  updateHashAfterMove(state, { side, idx, from: payload.from, to: payload.to });
  if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
  highlight(null,false);
  dragging = null;
  log(`<i>Peer</i>: ${payload.from} → ${payload.to}`);
  postMoveActions({ side, idx, from: payload.from, to: payload.to });
  renderPieces();
  if (payload.hash !== undefined && state.hash !== payload.hash){
    log('<span class="warn">State hash mismatch. Consider resetting.</span>');
  }
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
  if (onlineSession){
    log('<b>Multiplayer:</b> Undo disabled during online play.');
    return;
  }
  if (history.length===0) return;
  const prev = history.pop();
  state = prev.state;
  winner = prev.winner;
  if (moveHistory.length>0) moveHistory.pop();
  analyzeBtn.style.display = winner ? 'inline-block' : 'none';
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

/** ====================== Post-game Analysis ====================== */
function analyzeGame(){
  if (moveHistory.length===0) return;
  analysisMode = true;
  analyzeBtn.style.display='none';
  analysisPanel.style.display='flex';
  svg.classList.add('analyzing');
  if (tapSel){ highlight(tapSel.legal,false); tapSel=null; }
  analysisInfo.textContent='Start position';
  TT.clear();
  analysisWinner = winner;
  log('<b>Post-game analysis:</b>');
  const states=[initialState()];
  const infos=[];
  let s = states[0];
  moveHistory.forEach((mv, i) => {
    const moves = allMoves(s, mv.side);
    if (moves.length===0) return;
    let best = moves[0];
    let bestScore = mv.side===botSide ? -Infinity : Infinity;
    for (const m of moves){
      const ns = applyMove(s, m);
      const sc = minimax(ns, botDepth-1, -Infinity, Infinity, ns.turn===botSide, null);
      if (mv.side===botSide){
        if (sc > bestScore){ bestScore = sc; best = m; }
      } else {
        if (sc < bestScore){ bestScore = sc; best = m; }
      }
    }
    const nsActual = applyMove(s,mv);
    const actualScore = minimax(nsActual, botDepth-1, -Infinity, Infinity, nsActual.turn===botSide, null);
    const diff = mv.side===botSide ? bestScore - actualScore : actualScore - bestScore;
    infos.push({move:mv,best,diff});
    states.push(nsActual);
    s = nsActual;
  });
  analysisData = {states,infos};
  analysisIdx = 0;
  showAnalysisStep(0);
}

function showAnalysisStep(idx){
  if (!analysisData) return;
  analysisIdx = Math.max(0, Math.min(idx, analysisData.states.length-1));
  state = clone(analysisData.states[analysisIdx]);
  winner = null;
  renderPieces();
  highlight(null,false);
  winLine.style.display='none';
  const res = isWin(state);
  if (res){ winner = res.player; drawWinLine(...res.line); }
  if (analysisIdx===0){
    analysisInfo.textContent = 'Start position';
  } else {
    const info = analysisData.infos[analysisIdx-1];
    analysisInfo.textContent = `Move ${analysisIdx} ${info.move.side==='p1'?'P1':'P2'} ${info.move.from} → ${info.move.to} | Best: ${info.best.from} → ${info.best.to} | Δ ${info.diff.toFixed(2)}`;
    highlight(new Set([info.move.from, info.move.to]), true);
  }
  analysisPrev.style.visibility = analysisIdx>0 ? 'visible' : 'hidden';
  analysisNext.style.visibility = analysisIdx<analysisData.states.length-1 ? 'visible' : 'hidden';
  updateUI();
}

/** ====================== Multiplayer ====================== */
const STATUS_LABELS = {
  offline: 'Offline',
  waiting: 'Waiting…',
  connecting: 'Connecting…',
  connected: 'Connected',
  error: 'Error'
};

function updateConnectionStatus(state, message){
  if (!connectionStatusEl) return;
  connectionStatusEl.dataset.state = state;
  connectionStatusEl.textContent = message || STATUS_LABELS[state] || state;
}

async function ensureFirebase(){
  if (firestoreDb) return firestoreDb;
  firebaseConfig = window.FIREBASE_DEFAULT_CONFIG || firebaseConfig;
  const cfg = firebaseConfig;

  if (!cfg || !cfg.apiKey) throw new Error('Firebase configuration is incomplete.');
  if (typeof firebase === 'undefined') throw new Error('Firebase SDK not loaded.');
  if (!firebase.apps.length){
    firebaseAppInstance = firebase.initializeApp(cfg);
  } else {
    firebaseAppInstance = firebase.app();
  }
  firestoreDb = firebase.firestore();
  return firestoreDb;
}

function generateRoomCode(){
  const alphabet = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let code = '';
  for (let i=0;i<6;i++) code += alphabet[Math.floor(Math.random()*alphabet.length)];
  return code;
}

function updateOnlineButtons(){
  if (hostBtn) hostBtn.classList.toggle('disabled', onlineSession);
  if (joinBtn) joinBtn.classList.toggle('disabled', onlineSession);
  if (leaveBtn) leaveBtn.classList.toggle('disabled', !onlineSession);
  if (resetBtn) resetBtn.classList.toggle('disabled', onlineSession);
  if (joinCodeInput){
    if (onlineSession) joinCodeInput.setAttribute('disabled','');
    else joinCodeInput.removeAttribute('disabled');
  }
}

function restoreSoloSettings(){
  if (botEnabledBeforeOnline !== null){
    botEnabled = botEnabledBeforeOnline;
    botEnabledBeforeOnline = null;
    updateModeText();
  }
  setUndoAvailability(true);
}

function startOnlineSession(role){
  onlineSession = true;
  isHost = role === 'host';
  peerConnected = false;
  awaitingInitialState = !isHost;
  localSide = isHost ? 'p1' : 'p2';
  remoteSide = localSide === 'p1' ? 'p2' : 'p1';
  if (botEnabledBeforeOnline === null) botEnabledBeforeOnline = botEnabled;
  botEnabled = false;
  updateModeText();
  if (analysisMode) analysisExit.onclick();
  reset();
  clearLog();
  log(`<b>Multiplayer:</b> Preparing online match. You are ${localSide==='p1'?'Player 1 (blue)':'Player 2 (gold)'}.`);
  setUndoAvailability(false);
  updateOnlineButtons();
}

function attachPeerConnectionStateListener(){
  if (!peerConnection) return;
  peerConnection.onconnectionstatechange = () => {
    if (!peerConnection) return;
    if (peerConnection.connectionState === 'failed'){
      updateConnectionStatus('error','Connection failed');
    } else if (peerConnection.connectionState === 'disconnected'){
      updateConnectionStatus('error','Disconnected');
    }
  };
}

function attachDataChannel(channel){
  if (dataChannel && dataChannel !== channel){
    try { dataChannel.close(); } catch (e) { /* ignore */ }
  }
  dataChannel = channel;
  dataChannel.onopen = () => {
    peerConnected = true;
    updateConnectionStatus('connected','Connected');
    const roleText = localSide==='p1'?'Player 1 (blue)':'Player 2 (gold)';
    log(`<b>Multiplayer:</b> Connected to peer as ${roleText}.`);
    if (isHost){
      awaitingInitialState = false;
      sendInitialState();
    } else if (awaitingInitialState){
      log('Waiting for host to sync the initial state…');
    }
  };
  dataChannel.onmessage = (event) => {
    try {
      const message = JSON.parse(event.data);
      handlePeerMessage(message);
    } catch (err){
      console.warn('Failed to parse peer message', err);
    }
  };
  dataChannel.onclose = () => {
    if (onlineSession){
      leaveMultiplayer('Peer disconnected.', { deleteRoom: isHost });
    }
  };
  dataChannel.onerror = (err) => {
    console.warn('Data channel error', err);
  };
}

function sendPeerMessage(type, payload){
  if (!dataChannel || dataChannel.readyState !== 'open') return;
  try {
    dataChannel.send(JSON.stringify({ type, payload, version: MULTIPLAYER_PROTOCOL_VERSION }));
  } catch (err){
    console.warn('Failed to send peer message', err);
  }
}

function handlePeerMessage(message){
  if (!message) return;
  if (message.version && message.version !== MULTIPLAYER_PROTOCOL_VERSION){
    log('<span class="warn">Peer is using an incompatible version.</span>');
    return;
  }
  switch(message.type){
    case 'move':
      handleRemoteMove(message.payload);
      break;
    case 'init':
      handlePeerInit(message.payload);
      break;
    case 'leave':
      leaveMultiplayer('Peer ended the match.', { deleteRoom: isHost });
      break;
    default:
      break;
  }
}

function handlePeerInit(payload){
  if (!payload || isHost) return;
  const incomingState = payload.state;
  if (incomingState){
    state = incomingState;
    state.hash = payload.hash ?? computeHash(state);
    state.turn = payload.turn ?? state.turn;
    winner = null;
    history = [];
    moveHistory = [];
    highlight(null,false);
    winLine.style.display='none';
    renderPieces();
    updateUI();
    log(`<b>Multiplayer:</b> Match synced. ${payload.hostSide==='p1'?'Host (P1)':'Host (P2)'} to move.`);
  }
  awaitingInitialState = false;
}

function sendInitialState(){
  if (!isHost) return;
  const snapshot = clone(state);
  sendPeerMessage('init', {
    state: snapshot,
    hash: state.hash,
    turn: state.turn,
    hostSide: localSide,
    version: MULTIPLAYER_PROTOCOL_VERSION
  });
}

async function clearRoom(roomRef){
  if (!roomRef || !firestoreDb) return;
  const offerSnap = await roomRef.collection('offerCandidates').get();
  const answerSnap = await roomRef.collection('answerCandidates').get();
  const batch = firestoreDb.batch();
  offerSnap.forEach(doc => batch.delete(doc.ref));
  answerSnap.forEach(doc => batch.delete(doc.ref));
  batch.delete(roomRef);
  await batch.commit();
}

async function leaveMultiplayer(reason, options = {}){
  const { deleteRoom = false, skipLog = false } = options;
  onlineSession = false;
  isHost = false;
  if (dataChannel){
    try { dataChannel.close(); } catch (e) { /* ignore */ }
  }
  dataChannel = null;
  if (peerConnection){
    try { peerConnection.close(); } catch (e) { /* ignore */ }
  }
  peerConnection = null;
  if (roomUnsub){ roomUnsub(); roomUnsub = null; }
  candidateUnsubs.forEach((fn)=>{ if (fn) fn(); });
  candidateUnsubs = [];
  if (roomDocRef && deleteRoom){
    try { await clearRoom(roomDocRef); } catch (err) { console.warn('Failed to clear room', err); }
  }
  roomDocRef = null;
  pendingRoomCode = null;
  peerConnected = false;
  awaitingInitialState = false;
  localSide = null;
  remoteSide = null;
  updateConnectionStatus('offline', 'Offline');
  if (roomCodeEl) roomCodeEl.textContent = 'Room: —';
  if (!skipLog && reason) log(`<b>Multiplayer:</b> ${reason}`);
  restoreSoloSettings();
  updateOnlineButtons();
  if (joinCodeInput){
    joinCodeInput.removeAttribute('disabled');
    if (!options.keepJoinCode) joinCodeInput.value='';
  }
}

async function hostOnlineMatch(){
  if (onlineSession) return;
  try {
    const db = await ensureFirebase();
    startOnlineSession('host');
    const code = generateRoomCode();
    pendingRoomCode = code;
    if (roomCodeEl) roomCodeEl.textContent = `Room: ${code}`;
    updateConnectionStatus('waiting','Waiting for opponent');
    const rooms = db.collection('rooms');
    roomDocRef = rooms.doc(code);
    const offerCandidates = roomDocRef.collection('offerCandidates');
    const answerCandidates = roomDocRef.collection('answerCandidates');
    peerConnection = new RTCPeerConnection({ iceServers: ICE_SERVERS });
    attachPeerConnectionStateListener();
    peerConnection.onicecandidate = (event) => {
      if (event.candidate) offerCandidates.add(event.candidate.toJSON());
    };
    attachDataChannel(peerConnection.createDataChannel(DATA_CHANNEL_LABEL, { ordered: true }));
    const offer = await peerConnection.createOffer();
    await peerConnection.setLocalDescription(offer);
    const timestamp = firebase.firestore && firebase.firestore.FieldValue && firebase.firestore.FieldValue.serverTimestamp ? firebase.firestore.FieldValue.serverTimestamp() : Date.now();
    await roomDocRef.set({
      offer: { type: offer.type, sdp: offer.sdp },
      createdAt: timestamp,
      version: MULTIPLAYER_PROTOCOL_VERSION
    });
    candidateUnsubs.push(answerCandidates.onSnapshot((snapshot)=>{
      snapshot.docChanges().forEach((change)=>{
        if (change.type === 'added'){
          const data = change.doc.data();
          if (data) peerConnection.addIceCandidate(new RTCIceCandidate(data));
        }
      });
    }));
    roomUnsub = roomDocRef.onSnapshot(async (snapshot)=>{
      const data = snapshot.data();
      if (!data) return;
      if (data.answer && !peerConnection.currentRemoteDescription){
        await peerConnection.setRemoteDescription(new RTCSessionDescription(data.answer));
      }
    });
    log(`<b>Multiplayer:</b> Share room code <b>${code}</b> with your opponent.`);
  } catch (err){
    console.error(err);
    log(`<span class="warn">Failed to host match: ${err.message}</span>`);
    updateConnectionStatus('error','Error');
    await leaveMultiplayer('Hosting failed.', { skipLog: true, deleteRoom: true });
  }
}

async function joinOnlineMatch(){
  if (onlineSession) return;
  const raw = joinCodeInput ? joinCodeInput.value.trim().toUpperCase() : '';
  if (!raw){
    updateConnectionStatus('error','Enter code');
    return;
  }
  try {
    const db = await ensureFirebase();
    const roomRef = db.collection('rooms').doc(raw);
    const snapshot = await roomRef.get();
    if (!snapshot.exists) throw new Error('Room not found');
    const roomData = snapshot.data();
    if (!roomData || !roomData.offer) throw new Error('Room is not ready yet');
    startOnlineSession('guest');
    pendingRoomCode = raw;
    if (roomCodeEl) roomCodeEl.textContent = `Room: ${raw}`;
    updateConnectionStatus('connecting','Connecting…');
    roomDocRef = roomRef;
    peerConnection = new RTCPeerConnection({ iceServers: ICE_SERVERS });
    attachPeerConnectionStateListener();
    peerConnection.onicecandidate = (event) => {
      if (event.candidate) roomDocRef.collection('answerCandidates').add(event.candidate.toJSON());
    };
    peerConnection.ondatachannel = (event) => {
      attachDataChannel(event.channel);
    };
    candidateUnsubs.push(roomDocRef.collection('offerCandidates').onSnapshot((snapshot)=>{
      snapshot.docChanges().forEach((change)=>{
        if (change.type === 'added'){
          const data = change.doc.data();
          if (data) peerConnection.addIceCandidate(new RTCIceCandidate(data));
        }
      });
    }));
    roomUnsub = roomDocRef.onSnapshot((snap)=>{
      if (!snap.exists){
        leaveMultiplayer('Host closed the room.', { deleteRoom: false });
      }
    });
    await peerConnection.setRemoteDescription(new RTCSessionDescription(roomData.offer));
    const answer = await peerConnection.createAnswer();
    await peerConnection.setLocalDescription(answer);
    await roomDocRef.update({ answer: { type: answer.type, sdp: answer.sdp }, version: MULTIPLAYER_PROTOCOL_VERSION });
    log('<b>Multiplayer:</b> Attempting to join match…');
  } catch (err){
    console.error(err);
    log(`<span class="warn">Failed to join match: ${err.message}</span>`);
    updateConnectionStatus('error','Error');
    await leaveMultiplayer('Join failed.', { skipLog: true, deleteRoom: false });
  }
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
updateConnectionStatus('offline');
updateOnlineButtons();

if (hostBtn) hostBtn.onclick = () => { if (!onlineSession) hostOnlineMatch(); };
if (joinBtn) joinBtn.onclick = () => { if (!onlineSession) joinOnlineMatch(); };
if (leaveBtn) leaveBtn.onclick = async () => {
  if (!onlineSession) {
    log('<b>Multiplayer:</b> No online match to leave.');
    return;
  }
  if (peerConnected) sendPeerMessage('leave', { reason: 'Peer left the match.' });
  await leaveMultiplayer('You left the online match.', { deleteRoom: isHost, keepJoinCode: true });
};
if (resetBtn) resetBtn.onclick = () => {
  if (onlineSession){
    log('<b>Multiplayer:</b> Reset disabled while connected online.');
    return;
  }
  reset();
};
if (undoBtn) undoBtn.onclick = undo;
analyzeBtn.onclick = analyzeGame;
analysisPrev.onclick = () => showAnalysisStep(analysisIdx-1);
analysisNext.onclick = () => showAnalysisStep(analysisIdx+1);
analysisExit.onclick = () => {
  analysisMode = false;
  analysisPanel.style.display='none';
  svg.classList.remove('analyzing');
  highlight(null,false);
  if (analysisData){
    state = clone(analysisData.states[analysisData.states.length-1]);
  }
  winner = analysisWinner;
  renderPieces();
  if (winner){ const res = isWin(state); if (res) drawWinLine(...res.line); }
  else winLine.style.display='none';
  analysisData = null;
  analysisWinner = null;
  updateUI();
  analyzeBtn.style.display='inline-block';
};
document.getElementById('mode').onclick = () => {
  if (onlineSession){
    log('<b>Multiplayer:</b> Bot toggle disabled during online play.');
    return;
  }
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
