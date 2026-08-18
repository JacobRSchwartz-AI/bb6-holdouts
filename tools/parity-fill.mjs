// The halt rule is E reading 1, and E is only entered from D0/E0 during a
// leftward fill over zeros. So: HALT <=> some fill scan meets its first 1 at
// ODD distance. This tool measures the parity structure of every fill scan.
const CODE='1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows=CODE.split('_').map(s=>[0,1].map(b=>{const e=s.slice(b*3,b*3+3);return e==='---'?null:{w:+e[0],d:e[1],q:e.charCodeAt(2)-65};}));
const MAX=+(process.argv[2]??1e7);
const N=1<<24, ORIG=N>>1; const tape=new Uint8Array(N);
let pos=ORIG,q=0;
const gapPar=new Map(), entryPar=new Map(), tgtPar=new Map(), gapLen=new Map();
let fillStart=-1;
// parity census of every 1-run's endpoints, sampled
const runStart=new Map(), runEnd=new Map();
let steps=0;
for(;steps<MAX;steps++){
  const sym=tape[pos],t=rows[q][sym]; if(!t){console.log('HALT '+steps);break;}
  if(q===3&&sym===0&&fillStart<0) fillStart=pos;          // D0 begins a fill
  if((q===3||q===4)&&sym===1&&fillStart>=0){
    const gap=fillStart-pos, ep=((fillStart-ORIG)%2+2)%2, tp=((pos-ORIG)%2+2)%2;
    const k=`gap%2=${gap%2}`; gapPar.set(k,(gapPar.get(k)??0)+1);
    entryPar.set(ep,(entryPar.get(ep)??0)+1);
    tgtPar.set(tp,(tgtPar.get(tp)??0)+1);
    gapLen.set(gap,(gapLen.get(gap)??0)+1);
    fillStart=-1;
  }
  if(!((q===3||q===4)&&sym===0)) if(!(q===3&&sym===0)) fillStart= (q===3||q===4)?fillStart:-1;
  tape[pos]=t.w; pos+=t.d==='R'?1:-1; q=t.q;
}
const show=(m,l)=>console.log(l+': '+[...m.entries()].sort((a,b)=>String(a[0])<String(b[0])?-1:1).map(([k,v])=>`${k}:${v}`).join('  '));
console.log(`steps=${steps}`);
show(gapPar,'fill gap parity');
show(entryPar,'fill ENTRY position parity');
show(tgtPar,'fill TARGET (first 1) position parity');
show(gapLen,'gap lengths');
// global parity census of 1-cells at the end
let e=0,o=0; for(let i=0;i<N;i++) if(tape[i]) (((i-ORIG)%2+2)%2===0?e++:o++);
console.log(`final tape: 1s at even offsets=${e}, odd offsets=${o}`);
