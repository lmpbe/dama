// <<AI-ENGINE-START>>
function aiEngineFactory(opt){
  const INF=1000000, MATE=100000, QLIM=8;
  // pesi della valutazione e interruttori della ricerca (opt serve solo ai test)
  const W=Object.assign({
    man:100, adv:3, cen:2, back:5, edge:-4, prot:0, king:200, kcen:2, diag:4,
    pvs:1, lmr:1, kill:1, advq:4, mob:3, trap:0, basePen:30, baseNear:0, baseNearPly:6, cornerPen:20, edgePen:30, centerPen:20, bookPen:1,
    // valore della dama in funzione del numero totale di pezzi in tavola: punti [pezzi, valore], interpolati linearmente
    // (16 o piu' pezzi: 3,50 pedine; 12: 2,50; 10: 2,25; 8 o meno: 2,00); kingTab:null = valore fisso W.king
    kingTab:[[8,200],[10,225],[12,250],[13,275],[14,300],[15,325],[16,350]],
    // dama "debole" (appena promossa nell'angolo, ancora lontana dal centro): dama Bianca in 1 o in 5 con la 2 occupata da una
    // pedina Rossa, dama Rossa in 32 o in 28 con la 31 occupata da una pedina Bianca. Vale kingWeak centesimi in meno della tabella
    // normale (3,00 con 16 o piu' pezzi, 1,50 con 8 o meno); appena esce da quelle case torna al valore normale (0 = spenta)
    kingWeak:50,
    // penalita' "zeppa": con zeppaMin o piu' pezzi in tavola, zeppaPen centesimi se il Bianco muove 24-20 con una pedina nera in 16
    // e una pedina bianca in 23, o se il Nero muove 9-13 con una pedina bianca in 17 e una pedina nera in 10 (0 = spenta)
    zeppaPen:20, zeppaMin:14, zeppa2:0, baseEarly:20, baseEarlyMin:18,   // zeppa2: seconda penalita' (28-23 / 5-10), stessi valori; 0 = spenta
    // penalita' "zeppone": con zepponeMax o meno pezzi in tavola, tutte le pedine della base (29,30,31 e la 32 se manca la 31 per il
    // Bianco; 2,3,4 e la 1 se manca la 2 per il Nero) hanno la stessa penalita' zepponePen se il Bianco ha pedine in 16,20,24 e il Nero in
    // 4,7,11,12,15 (per il Nero la situazione speculare: sue pedine in 9,13,17 e pedine bianche in 18,21,22,26,29). 0 = spenta
    zepponePen:20, zepponeMax:16
  }, opt||{});

  // ── geometria: indice 0..31 = casella PDN 1..32 ──
  const ROW=new Int8Array(32), COL=new Int8Array(32), IDX=new Int8Array(64).fill(-1), CEN=new Int8Array(32), DIAG=new Int8Array(32);
  for(let i=0;i<32;i++){
    const r=i>>2, p=i&3;
    ROW[i]=r; COL[i]=(r&1)===0?p*2:p*2+1;
    IDX[ROW[i]*8+COL[i]]=i;
  }
  for(let i=0;i<32;i++){
    const r=ROW[i], c=COL[i];
    CEN[i]=(c>=2&&c<=5)?((r>=2&&r<=5)?4:2):0;
    DIAG[i]=r===c?1:0;
  }
  const DR=[-1,-1,1,1], DC=[-1,1,-1,1];
  const NB=new Int8Array(128).fill(-1), JP=new Int8Array(128).fill(-1);
  for(let i=0;i<32;i++) for(let d=0;d<4;d++){
    const r1=ROW[i]+DR[d], c1=COL[i]+DC[d], r2=ROW[i]+2*DR[d], c2=COL[i]+2*DC[d];
    if(r1>=0&&r1<8&&c1>=0&&c1<8) NB[i*4+d]=IDX[r1*8+c1];
    if(r2>=0&&r2<8&&c2>=0&&c2<8) JP[i*4+d]=IDX[r2*8+c2];
  }
  const WD=[0,1], BD=[2,3], ALL=[0,1,2,3];

  // celle: 0 vuota, 1 pedina bianca, 2 dama bianca, -1 pedina nera, -2 dama nera
  // side: +1 bianchi, -1 neri

  // ── generazione mosse ──
  function capDFS(b,s,cur,king,path,capt,kc,out){
    const dirs=king?ALL:(s>0?WD:BD);
    for(let k=0;k<dirs.length;k++){
      const d=dirs[k];
      const m=NB[cur*4+d], l=JP[cur*4+d];
      if(m<0||l<0) continue;
      const v=b[m];
      if(v===0||v*s>0) continue;
      if(!king&&(v===2||v===-2)) continue;   // la pedina non prende la dama
      if(b[l]!==0) continue;
      b[m]=0; path.push(l); capt.push(m);
      const nk=kc+((v===2||v===-2)?1:0);
      const promo=!king&&(s>0?ROW[l]===0:ROW[l]===7);
      if(promo){
        out.push({path:path.slice(),capt:capt.slice(),kc:nk,byKing:false});   // promozione: la presa finisce
      } else {
        const before=out.length;
        capDFS(b,s,l,king,path,capt,nk,out);
        if(out.length===before) out.push({path:path.slice(),capt:capt.slice(),kc:nk,byKing:king});
      }
      path.pop(); capt.pop(); b[m]=v;
    }
  }

  function genMoves(b,s){
    const caps=[];
    for(let i=0;i<32;i++){
      const v=b[i];
      if(v===0||v*s<0) continue;
      const king=(v===2||v===-2);
      b[i]=0;
      capDFS(b,s,i,king,[i],[],0,caps);
      b[i]=v;
    }
    if(caps.length>0){
      let max=0;
      for(let i=0;i<caps.length;i++) if(caps[i].capt.length>max) max=caps[i].capt.length;
      let best=caps.filter(c=>c.capt.length===max);
      let mk=0;
      for(let i=0;i<best.length;i++) if(best[i].kc>mk) mk=best[i].kc;
      best=best.filter(c=>c.kc===mk);
      const fk=best.filter(c=>c.byKing);
      if(fk.length>0) best=fk;
      return {moves:best,cap:true};
    }
    const mv=[];
    for(let i=0;i<32;i++){
      const v=b[i];
      if(v===0||v*s<0) continue;
      const king=(v===2||v===-2);
      const dirs=king?ALL:(s>0?WD:BD);
      for(let k=0;k<dirs.length;k++){
        const t=NB[i*4+dirs[k]];
        if(t>=0&&b[t]===0) mv.push({path:[i,t],capt:[],kc:0,byKing:king});
      }
    }
    return {moves:mv,cap:false};
  }

  function applyMove(b,m){
    const c=b.slice();
    const from=m.path[0], to=m.path[m.path.length-1];
    let v=c[from];
    c[from]=0;
    for(let i=0;i<m.capt.length;i++) c[m.capt[i]]=0;
    if(v===1&&ROW[to]===0) v=2;
    else if(v===-1&&ROW[to]===7) v=-2;
    c[to]=v;
    return c;
  }

  // ── valutazione (dal punto di vista di s) ──
  function evaluate(b,s){
    let sc=0, kv=W.king;
    if(W.kingTab){
      let n=0; for(let i=0;i<32;i++) if(b[i]!==0) n++;
      const T=W.kingTab, L=T.length;
      if(n>=T[L-1][0]) kv=T[L-1][1];
      else if(n<=T[0][0]) kv=T[0][1];
      else for(let j=1;j<L;j++) if(n<=T[j][0]){ kv=T[j-1][1]+(T[j][1]-T[j-1][1])*(n-T[j-1][0])/(T[j][0]-T[j-1][0]); break; }
    }
    for(let i=0;i<32;i++){
      const v=b[i];
      if(v===0) continue;
      const r=ROW[i], c=COL[i];
      let x;
      if(v===1||v===-1){
        const adv=v===1?(7-r):r;
        x=W.man+adv*W.adv+CEN[i]*W.cen;
        if(adv===0) x+=W.back;
        if(W.advq&&adv>=5) x+=(adv-4)*W.advq;
        if(c===0||c===7) x+=W.edge;
        if(W.prot){
          const d0=v===1?2:0;
          const n1=NB[i*4+d0], n2=NB[i*4+d0+1];
          if(n1<0||b[n1]!==0) x+=W.prot;
          if(n2<0||b[n2]!==0) x+=W.prot;
        }
      } else {
        const weak=(v===2&&(i===0||i===4)&&b[1]===-1)||(v===-2&&(i===31||i===27)&&b[30]===1);
        x=(weak?kv-W.kingWeak:kv)+CEN[i]*W.kcen+(DIAG[i]?W.diag:0);
      }
      sc+=v>0?x:-x;
    }
    if(W.mob){
      // mobilità: differenza di mosse semplici disponibili (solo posizioni senza prese)
      let mw=0,mb=0;
      for(let i=0;i<32;i++){
        const v=b[i];
        if(v===0) continue;
        const king=(v===2||v===-2);
        const dirs=king?ALL:(v>0?WD:BD);
        let n=0;
        for(let k=0;k<dirs.length;k++){ const t=NB[i*4+dirs[k]]; if(t>=0&&b[t]===0) n++; }
        if(v>0) mw+=n; else mb+=n;
      }
      sc+=(mw-mb)*W.mob;
    }
    return s>0?sc:-sc;
  }

  // ── hash di Zobrist + tabella di trasposizione ──
  const Z1=new Int32Array(160), Z2=new Int32Array(160);
  let seed=0x2545F491|0;
  function rnd(){ seed^=seed<<13; seed^=seed>>>17; seed^=seed<<5; return seed|0; }
  for(let i=0;i<160;i++){ Z1[i]=rnd(); Z2[i]=rnd(); }
  const S1=rnd(), S2=rnd();
  let H1=0, H2=0;
  function hash(b,s){
    let h1=0,h2=0;
    for(let i=0;i<32;i++){
      const v=b[i];
      if(v!==0){ const k=i*5+v+2; h1^=Z1[k]; h2^=Z2[k]; }
    }
    if(s<0){ h1^=S1; h2^=S2; }
    H1=h1; H2=h2;
  }
  const TTSIZE=1<<20, TTMASK=TTSIZE-1;
  let tkey=null, tdepth=null, tflag=null, tscore=null, tmove=null;
  function allocTT(){
    if(tkey) return;
    tkey=new Int32Array(TTSIZE); tdepth=new Int8Array(TTSIZE); tflag=new Uint8Array(TTSIZE);
    tscore=new Int32Array(TTSIZE); tmove=new Int16Array(TTSIZE);
  }
  function setPen(on){ if(on!==penOn){ penOn=on; if(tflag) tflag.fill(0); } }   // la tabella di trasposizione dipende dalla modalita'
  function toTT(sc,ply){ return sc>MATE-1000?sc+ply:(sc<-MATE+1000?sc-ply:sc); }
  function fromTT(sc,ply){ return sc>MATE-1000?sc-ply:(sc<-MATE+1000?sc+ply:sc); }


  // ── database dei finali (facoltativo, file libro-finali.js) ──
  // Contiene, per tutte le posizioni fino a 4 pezzi, esito esatto (vince/perde/patta) e distanza alla
  // conversione (presa o promozione) modulo DBM. Simbolo: 0 patta; 1..M vince (d=sym-1); M+1..2M perde (d=sym-1-M).
  const DBWIN=30000, DBWIN5=20000;
  let dbHits=0, DB=null, DB5=null, DBM=8, DBMAXP=4, DBCLS=null, DBC=null;
  function setDB(arr,mod,arr5){
    if(!arr){ DB=null; DB5=null; return; }
    DBM=mod||8; DBMAXP=arr5?5:4;
    const C=[]; for(let n=0;n<=32;n++){ C.push([1,0,0,0,0,0,0]); for(let k=1;k<=6;k++) C[n][k]= n===0?0:(C[n-1][k]+C[n-1][k-1]); }
    // C[n][k] costruito con Pascal: C[n][k]=C[n-1][k]+C[n-1][k-1]
    DBC=C; DBCLS=new Map(); let base=0, base5=0;
    for(let tot=2;tot<=DBMAXP;tot++) for(let men=0;men<=tot;men++)
      for(let bm=0;bm<=tot;bm++) for(let bk=0;bm+bk<=tot;bk++){
        const bp=bm+bk; if(bp<1) continue; const wp=tot-bp; if(wp<1) continue;
        for(let wm=0;wm<=wp;wm++){ const wk=wp-wm; if(bm+wm!==men) continue;
          if(bp<wp||(bp===wp&&bk<wk)) continue;
          const nbm=C[28][bm], nwm=C[28][wm], nbk=C[32][bk], nwk=C[32][wk];
          const size=nbm*nwm*nbk*nwk, nstm=(bm===wm&&bk===wk)?1:2;
          if(tot<=4){ DBCLS.set(bm*1000+bk*100+wm*10+wk,{base,size,nbm,nwm,nbk,nwk,p5:false}); base+=size*nstm; }
          else { DBCLS.set(bm*1000+bk*100+wm*10+wk,{base:base5,size,nbm,nwm,nbk,nwk,p5:true}); base5+=size*nstm; } }
      }
    if(base!==arr.length||(arr5&&Math.ceil(base5/4)!==arr5.length)){ DB=null; DB5=null; return; }   // file non coerente: non usato
    DB=arr; DB5=arr5||null;
  }
  // simbolo del database per (b,s) oppure -1 (fuori ambito). Da chiamare solo se chi muove non ha prese.
  function dbSym(b,s){
    let bm=0,bk=0,wm=0,wk=0;
    for(let i=0;i<32;i++){ const v=b[i]; if(v===0) continue; if(v===-1) bm++; else if(v===-2) bk++; else if(v===1) wm++; else wk++; }
    const tot=bm+bk+wm+wk;
    if(tot>DBMAXP||bm+bk===0||wm+wk===0) return -1;
    const bp=bm+bk, wp=wm+wk;
    let rev=false;
    if(wp>bp) rev=true; else if(wp===bp){ if(wk>bk) rev=true; else if(bm===wm&&bk===wk&&s>0) rev=true; }
    let c0=bm,c1=bk,c2=wm,c3=wk, ss=s;
    if(rev){ c0=wm;c1=wk;c2=bm;c3=bk; ss=-s; }
    const cl=DBCLS.get(c0*1000+c1*100+c2*10+c3); if(!cl) return -1;
    const C=DBC;
    let rbm=0,rwm=0,rbk=0,rwk=0,nbm=0,nwm=0,nbk=0,nwk=0;
    for(let j=0;j<32;j++){
      let v=rev?-b[31-j]:b[j];
      if(v===0) continue;
      if(v===-1){ if(j>27) return -1; rbm+=C[j][++nbm]; }
      else if(v===1){ if(j<4) return -1; rwm+=C[j-4][++nwm]; }
      else if(v===-2) rbk+=C[j][++nbk];
      else rwk+=C[j][++nwk];
    }
    const idx=((rbm*cl.nwm+rwm)*cl.nbk+rbk)*cl.nwk+rwk;
    const cell=cl.base+(ss<0?0:cl.size)+idx;
    if(cl.p5) return 100+((DB5[cell>>2]>>((cell&3)<<1))&3);   // 5 pezzi: solo esito (100 patta, 101 vince, 102 perde)
    return DB[cell];
  }
  // esito esatto per chi muove: 0 patta, 1 vince, 2 perde, -1 sconosciuto (risolve le prese forzate con una ricerca)
  function dbRes(b,s){
    const g=genMoves(b,s);
    if(g.moves.length===0) return 2;
    if(!g.cap){ const y=dbSym(b,s); if(y<0) return -1; return y>=100?y-100:(y===0?0:(y<=DBM?1:2)); }
    let anyL=false, allW=true;
    for(const m of g.moves){
      const r=dbRes(applyMove(b,m),-s);
      if(r<0) return -1;
      if(r===2) anyL=true;
      if(r!==1) allW=false;
    }
    return anyL?1:(allW?2:0);
  }
  // scelta alla radice quando la posizione e' nel database: {pick:mossa} oppure {moves:[...]} (mosse da cercare) oppure {}
  function dbRoot(b,s,moves){
    const rs=[];
    for(const m of moves){ const r=dbRes(applyMove(b,m),-s); if(r<0) return {}; rs.push(r); }
    const win=[]; for(let i=0;i<moves.length;i++) if(rs[i]===2) win.push(i);
    if(win.length){
      const conv=[], quiet=[];
      for(const i of win){
        const m=moves[i], nb=applyMove(b,m);
        const from=b[m.path[0]], to=nb[m.path[m.path.length-1]];
        const promo=from!==to&&(from===1||from===-1);
        const gc=genMoves(nb.slice(),-s);
        if(m.capt.length>0||promo||gc.cap) conv.push(m);
        else { const ys=dbSym(nb,-s); quiet.push({m,e:(ys>DBM&&ys<100)?ys-1-DBM:-1}); }
      }
      if(conv.length) return {pick:conv[0]};
      const y=dbSym(b,s);
      if(quiet.some(q=>q.e<0)||y>=100||y<0) return {moves:win.map(i=>moves[i])};   // 5 pezzi: niente distanza, la ricerca sceglie fra le sole mosse vincenti
      if(y>=1&&y<=DBM){
        const want=((y-1)-1+DBM*4)%DBM;
        for(const q of quiet) if(q.e%DBM===want) return {pick:q.m};
      }
      return {pick:quiet[0].m};
    }
    const dr=[]; for(let i=0;i<moves.length;i++) if(rs[i]===0) dr.push(moves[i]);
    if(dr.length>0&&dr.length<moves.length) return {moves:dr};
    return {};
  }

  // ── ricerca ──
  let nodes=0, abort=false, deadline=Infinity;
  let penOn=false;   // difesa della base attiva (non nella valutazione numerica ne' nel libro delle aperture)
  const hist=new Int32Array(1024);
  const killers=new Int16Array(256).fill(-1);

  function orderMoves(moves,ttMove,ply){
    const k1=W.kill?killers[ply*2]:-2, k2=W.kill?killers[ply*2+1]:-2;
    for(let i=0;i<moves.length;i++){
      const m=moves[i], p=m.path;
      const id=(p[0]<<5)|p[1];
      let k=hist[p[0]*32+p[p.length-1]];
      if(id===ttMove) k+=10000000;
      else if(id===k1) k+=900000;
      else if(id===k2) k+=800000;
      if(m.capt.length>0) k+=m.capt.length*1000+m.kc*500;
      m.k=k;
    }
    moves.sort((a,b)=>b.k-a.k);
  }

  // penalita' (centesimi di pedina) per la mossa/presa di una pedina che parte dalla propria base
  //  - pedine di base (29,30,31 Bianco; 2,3,4 Rosso): basePen, maggiorata nelle prime semimosse del calcolo
  //  - pedina 25 (Bianco) / 8 (Rosso): edgePen, solo se manca la pedina 29 (Bianco) / 4 (Rosso)
  //  - pedina d'angolo (32 Bianco; 1 Rosso): cornerPen, ma solo se la pedina 31 (Bianco) / 2 (Rosso) non c'e' piu'
  // maggiorazione per le prime semimosse del calcolo: baseNear alla 1a, scende linearmente fino a baseNear/6 alla 6a, poi 0
  function near(ply){ return (W.baseNear&&ply>=1&&ply<=W.baseNearPly)?Math.round(W.baseNear*(W.baseNearPly+1-ply)/W.baseNearPly):0; }
  function early(b){ let n=0; for(let i=0;i<32;i++) if(b[i]!==0) n++; return n>=W.baseEarlyMin; }   // proxy delle prime 10 mosse: ancora almeno baseEarlyMin pezzi
  function zepponeCond(b,s){
    let n=0; for(let i=0;i<32;i++) if(b[i]!==0) n++;
    if(n>W.zepponeMax) return false;
    if(s>0) return b[15]===1&&b[19]===1&&b[23]===1&&b[3]===-1&&b[6]===-1&&b[10]===-1&&b[11]===-1&&b[14]===-1;
    return b[8]===-1&&b[12]===-1&&b[16]===-1&&b[17]===1&&b[20]===1&&b[21]===1&&b[25]===1&&b[28]===1;
  }
  function basePenalty(b,s,f,ply){
    if(b[f]!==s) return 0;
    if(W.zepponePen>0&&(s>0?(f>=28&&f<=31):(f<=3))&&zepponeCond(b,s)){
      if(s>0?(f<31||b[30]!==1):(f>0||b[1]!==-1)) return W.zepponePen+near(ply);   // 29,30,31 / 2,3,4 e la 32 (1) solo se manca la 31 (2)
      return 0;
    }
    if(s>0){
      if(f===29) return (b[28]===1&&b[30]===1?W.centerPen:W.basePen)+near(ply);   // pedina 30: centerPen se ci sono ancora la 29 e la 31
      if(f===30&&b[31]===1&&b[29]===1&&early(b)) return W.baseEarly+near(ply);   // 31-28/31-27 con 32 e 30 presenti, nelle prime mosse
      if(f===28||f===30) return W.basePen+near(ply);
      if(f===31&&b[30]!==1) return W.cornerPen>0?W.cornerPen+near(ply):0;
      if(f===24&&b[28]!==1) return W.edgePen>0?W.edgePen+near(ply):0;
    } else {
      if(f===2) return (b[1]===-1&&b[3]===-1?W.centerPen:W.basePen)+near(ply);    // pedina 3: centerPen se ci sono ancora la 2 e la 4
      if(f===1&&b[0]===-1&&b[2]===-1&&early(b)) return W.baseEarly+near(ply);
      if(f===1||f===3) return W.basePen+near(ply);
      if(f===0&&b[1]!==-1) return W.cornerPen>0?W.cornerPen+near(ply):0;
      if(f===7&&b[3]!==-1) return W.edgePen>0?W.edgePen+near(ply):0;
    }
    return 0;
  }

  function zeppaPenalty(b,s,m){
    if(!(W.zeppaPen>0)||m.capt.length>0||m.path.length!==2) return 0;
    const f=m.path[0], t=m.path[1];
    if(s>0){
      const z1=f===23&&t===19&&b[23]===1&&b[15]===-1&&b[22]===1;                         // 24-20 con nera in 16 e bianca in 23
      const z2=W.zeppa2&&f===27&&t===22&&b[27]===1&&b[15]===-1&&b[19]===1;                // 28-23 con nera in 16 e bianca in 20
      if(!(z1||z2)) return 0;
    } else {
      const z1=f===8&&t===12&&b[8]===-1&&b[16]===1&&b[9]===-1;                           // 9-13 con bianca in 17 e nera in 10
      const z2=W.zeppa2&&f===4&&t===9&&b[4]===-1&&b[16]===1&&b[12]===-1;                  // 5-10 con bianca in 17 e nera in 13
      if(!(z1||z2)) return 0;
    }
    let n=0; for(let i=0;i<32;i++) if(b[i]!==0) n++;
    return n>=W.zeppaMin?W.zeppaPen:0;
  }

  function negamax(b,s,depth,alpha,beta,ply){
    if((++nodes&2047)===0&&Date.now()>deadline) abort=true;
    if(abort) return 0;
    const g=genMoves(b,s), moves=g.moves;
    if(moves.length===0) return -MATE+ply;
    if(DB!==null&&!g.cap){
      const y=dbSym(b,s);
      if(y>=100){ if(depth<=0){ dbHits++; return y===100?0:(y===101?DBWIN5-ply:-DBWIN5+ply); } }   // 5 pezzi: valore solo alle foglie, cosi' la ricerca cerca la conversione
      else if(y>=0){ dbHits++; return y===0?0:(y<=DBM?DBWIN-ply:-DBWIN+ply); }
    }
    if(depth<=0){
      if(!g.cap||depth<-QLIM) return evaluate(b,s);   // continua solo se c'è una presa forzata
    }
    let h1=0,h2=0,idx=0,ttMove=-1;
    const origAlpha=alpha, useTT=depth>0;
    if(useTT){
      hash(b,s); h1=H1; h2=H2; idx=h1&TTMASK;
      if(tflag[idx]!==0&&tkey[idx]===h2){
        ttMove=tmove[idx];
        if(tdepth[idx]>=depth){
          const sc=fromTT(tscore[idx],ply), fl=tflag[idx];
          if(fl===1) return sc;
          if(fl===2){ if(sc>alpha) alpha=sc; } else { if(sc<beta) beta=sc; }
          if(alpha>=beta) return sc;
        }
      }
    }
    orderMoves(moves,ttMove,ply);
    let best=-INF, bestId=-1, oppMen=-1;
    for(let i=0;i<moves.length;i++){
      const m=moves[i];
      const nb=applyMove(b,m);
      // difesa della base: ogni mossa di una pedina di base (29,30,31 Bianco; 2,3,4 Rosso) costa basePen, a qualunque profondita'
      let pm=0;
      if(penOn){
        const f=m.path[0];
        if(b[f]===s&&(s>0?f>=28:f<=3)){
          pm=basePenalty(b,s,f,ply);
          if(pm>0){
            if(oppMen<0){ oppMen=0; for(let q=0;q<32;q++) if(b[q]===-s){ oppMen=1; break; } }
            if(oppMen!==1) pm=0;
          }
        }
      }
      if(penOn&&W.zeppaPen>0) pm+=zeppaPenalty(b,s,m);
      let sc;
      if(i===0||!W.pvs){
        sc=-negamax(nb,-s,depth-1,-beta-pm,-alpha-pm,ply+1)-pm;
      } else {
        const red=(W.lmr&&depth>=3&&i>=3&&!g.cap)?1:0;
        sc=-negamax(nb,-s,depth-1-red,-alpha-1-pm,-alpha-pm,ply+1)-pm;
        if(!abort&&sc>alpha&&red>0) sc=-negamax(nb,-s,depth-1,-alpha-1-pm,-alpha-pm,ply+1)-pm;
        if(!abort&&sc>alpha&&sc<beta) sc=-negamax(nb,-s,depth-1,-beta-pm,-alpha-pm,ply+1)-pm;
      }
      if(abort) return 0;
      if(sc>best){ best=sc; bestId=(m.path[0]<<5)|m.path[1]; }
      if(sc>alpha){
        alpha=sc;
        if(alpha>=beta){
          if(!g.cap){
            const p=m.path;
            hist[p[0]*32+p[p.length-1]]+=depth*depth;
            const id=(p[0]<<5)|p[1];
            if(killers[ply*2]!==id){ killers[ply*2+1]=killers[ply*2]; killers[ply*2]=id; }
          }
          break;
        }
      }
    }
    if(useTT){
      tkey[idx]=h2; tdepth[idx]=depth;
      tflag[idx]=best<=origAlpha?3:(best>=beta?2:1);
      tscore[idx]=toTT(best,ply); tmove[idx]=bestId;
    }
    return best;
  }

  function posKey(cells,s){
    let k=s>0?'w':'b';
    for(let i=0;i<32;i++) k+=String.fromCharCode(99+cells[i]);
    return k;
  }

  const LEVELS={
    1:{iter:true,time:5000,maxDepth:30},          // Medio (fino a 5 s)
    2:{iter:true,time:15000,maxDepth:40}          // Forte (fino a 15 s)
  };

  function shuffle(a){
    for(let i=a.length-1;i>0;i--){ const j=Math.floor(Math.random()*(i+1)); const t=a[i]; a[i]=a[j]; a[j]=t; }
  }

  // o: {cells:[32], side:+1|-1, level:1..2, hist:[chiavi posizioni già viste], timeMs?, evalOnly?}
  function think(o){
    const t0=Date.now();
    const b=Int8Array.from(o.cells), s=o.side;
    const lv=LEVELS[o.level]||LEVELS[2];
    dbHits=0;
    let moves=genMoves(b,s).moves;
    if(moves.length===0) return {none:true};
    if(moves.length===1&&!o.evalOnly) return {path:moves[0].path.map(x=>x+1),score:0,depth:0,nodes:0,ms:0,forced:true};
    if(DB!==null&&!o.evalOnly){
      const r=dbRoot(b,s,moves);
      if(r.pick) return {path:r.pick.path.map(x=>x+1),score:DBWIN,depth:0,nodes:0,ms:Date.now()-t0,db:true,dbHits:1,stat:evaluate(b,s)};
      if(r.moves){ moves=r.moves; dbHits++; }
    }
    allocTT();
    setPen(W.basePen>0&&!o.evalOnly);
    hist.fill(0); killers.fill(-1);
    shuffle(moves);
    const seen={};
    (o.hist||[]).forEach(k=>{ seen[k]=(seen[k]||0)+1; });
    for(const m of moves) m.pen=15*(seen[posKey(applyMove(b,m),-s)]||0);   // piccolo malus alle ripetizioni
    // difesa della base: le pedine di base (29,30,31 per il Bianco; 2,3,4 per il Rosso) si muovono solo se la mossa
    // e' migliore delle alternative di almeno basePen centesimi di pedina (finche' l'avversario ha ancora pedine)
    if(W.basePen&&!o.evalOnly){
      let oppMen=false;
      for(let i=0;i<32;i++) if(b[i]===-s){ oppMen=true; break; }
      if(oppMen){
        for(const m of moves) m.pen+=basePenalty(b,s,m.path[0],99);
      }
    }
    if(W.zeppaPen>0&&!o.evalOnly){ for(const m of moves) m.pen+=zeppaPenalty(b,s,m); }
    nodes=0; abort=false;

    const time=o.timeMs||lv.time;
    let order=moves.slice(), best=order[0], bestScore=0, doneDepth=0;
    for(let depth=1;depth<=lv.maxDepth;depth++){
      abort=false;
      deadline=depth===1?Infinity:t0+time;
      let alpha=-INF, itBest=null, itScore=-INF;
      for(const m of order){
        const sc=-negamax(applyMove(b,m),-s,depth-1,-INF,-(alpha+m.pen),1)-m.pen;
        if(abort) break;
        if(sc>alpha){ alpha=sc; itBest=m; itScore=sc; }
      }
      if(abort&&depth>1) break;
      if(itBest){
        best=itBest; bestScore=itScore; doneDepth=depth;
        order=[best].concat(order.filter(x=>x!==best));
      }
      if(Math.abs(bestScore)>MATE-1000) break;
      if(Date.now()-t0>time*0.6) break;
    }
    return {path:best.path.map(x=>x+1),score:bestScore,depth:doneDepth,nodes,ms:Date.now()-t0,dbHits,stat:evaluate(b,s)};
  }

  // Classifica le mosse indicate in o.only ([da,a] in base 0) con ricerca a finestra piena: serve al libro delle aperture
  function rank(o){
    const t0=Date.now();
    const b=Int8Array.from(o.cells), s=o.side;
    let moves=genMoves(b,s).moves;
    if(o.only){
      const ok=new Set(o.only.map(p=>p[0]*32+p[1]));
      moves=moves.filter(m=>ok.has(m.path[0]*32+m.path[m.path.length-1]));
    }
    if(moves.length===0) return {none:true};
    if(moves.length===1) return {ranked:[{path:moves[0].path.map(x=>x+1),score:0}],depth:0,nodes:0,ms:0};
    allocTT(); setPen(W.bookPen>0&&W.basePen>0); hist.fill(0); killers.fill(-1);
    // difesa della base anche per le mosse del libro (bookPen=1): stessa penalita' della ricerca normale
    let usePen=false;
    if(W.bookPen>0&&W.basePen>0){ for(let i=0;i<32;i++) if(b[i]===-s){ usePen=true; break; } }
    nodes=0; abort=false;
    const time=o.timeMs||3000;
    let ranked=moves.map(m=>({m,score:0})), doneDepth=0;
    for(let depth=1;depth<=16;depth++){
      abort=false; deadline=depth<=2?Infinity:t0+time;
      const cur=[];
      for(const r of ranked){
        const sc=-negamax(applyMove(b,r.m),-s,depth-1,-INF,INF,1)-(usePen?basePenalty(b,s,r.m.path[0],99)+zeppaPenalty(b,s,r.m):0);
        if(abort) break;
        cur.push({m:r.m,score:sc});
      }
      if(abort) break;
      cur.sort((x,y)=>y.score-x.score);
      ranked=cur; doneDepth=depth;
      if(Date.now()-t0>time*0.6) break;
    }
    return {ranked:ranked.map(r=>({path:r.m.path.map(x=>x+1),score:r.score})),depth:doneDepth,nodes,ms:Date.now()-t0};
  }

  function run(o){ return o.rank?rank(o):think(o); }

  return {think,rank,run,genMoves,applyMove,posKey,evaluate,setDB,dbRes,basePenalty};
}

const E=aiEngineFactory();
onmessage=function(e){
  if(e.data&&e.data.cmd==='setDB'){ E.setDB(e.data.db,e.data.mod); return; }
  postMessage(Object.assign({id:e.data.id},E.run(e.data)));
};
