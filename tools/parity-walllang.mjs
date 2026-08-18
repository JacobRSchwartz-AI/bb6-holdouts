// Characterise the wall language: at each deep F-turn, encode the wall as
// the gap/run structure  0^a0 1^b0 0^a1 1^b1 ...  and census the shapes.
const CODE='1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows=CODE.split('_').map(s=>[0,1].map(b=>{const e=s.slice(b*3,b*3+3);return e==='---'?null:{w:+e[0],d:e[1],q:e.charCodeAt(2)-65};}));
const MAX=+process.argv[2];
const N=1<<24; const tape=new Uint8Array(N);
let pos=N>>1,q=0,lo=pos,hi=pos,scan=0;
const shapes=new Map(), gapset=new Map(), runset=new Map(), firsts=new Map();
for(let s=0;s<MAX;s++){
  const sym=tape[pos],t=rows[q][sym]; if(!t){console.log('HALT '+s);break;}
  if(sym===0&&q===5&&scan>=4){
    // walk left from the head, RLE, stop at the blank tail
    const runs=[]; let i=pos, cur=tape[i], n=0;
    while(i>=lo){ if(tape[i]===cur)n++; else {runs.push([cur,n]); cur=tape[i]; n=1;} i--; }
    runs.push([cur,n]);
    while(runs.length&&runs[runs.length-1][0]===0) runs.pop();  // drop blank tail
    const shape=runs.map(([v,c])=>`${v}^${c}`).join(' ');
    shapes.set(shape,(shapes.get(shape)??0)+1);
    runs.forEach(([v,c],j)=>{ const m=(v===0?gapset:runset); m.set(c,(m.get(c)??0)+1); });
    if(runs.length) firsts.set(runs[0][1],(firsts.get(runs[0][1])??0)+1);
  }
  if((q===5&&sym===1)||(q===0&&sym===1))scan++; else if(!((q===5&&sym===0)||(q===0&&sym===0)))scan=0;
  tape[pos]=t.w; pos+=t.d==='R'?1:-1; q=t.q;
  if(pos<lo)lo=pos; if(pos>hi)hi=pos;
}
console.log(`deep F-turns sampled: ${[...shapes.values()].reduce((a,b)=>a+b,0)}`);
console.log(`distinct wall shapes: ${shapes.size}`);
console.log(`leading 0-run lengths: ${[...firsts.entries()].sort((a,b)=>a[0]-b[0]).map(([k,v])=>k+':'+v).join(' ')}`);
console.log(`all 0-run lengths:     ${[...gapset.keys()].sort((a,b)=>a-b).join(',')}`);
console.log(`all 1-run lengths:     ${[...runset.keys()].sort((a,b)=>a-b).join(',')}`);
console.log('\ntop shapes:');
for(const [k,v] of [...shapes.entries()].sort((a,b)=>b[1]-a[1]).slice(0,14)) console.log(`  ${String(v).padStart(5)}  ${k}`);
