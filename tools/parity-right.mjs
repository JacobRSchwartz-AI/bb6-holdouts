// At every deep turn, render the RIGHT side as a run word and census the
// shapes that the standard [0;1]^p [0] [1]^L parse rejects.
const CODE='1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows=CODE.split('_').map(s=>[0,1].map(b=>{const e=s.slice(b*3,b*3+3);return e==='---'?null:{w:+e[0],d:e[1],q:e.charCodeAt(2)-65};}));
const MAX=+(process.argv[2]??2e7);
const N=1<<24; const tape=new Uint8Array(N);
let pos=N>>1,q=0,lo=pos,hi=pos,scan=0;
function runs(start){
  let last=hi; while(last>=start&&tape[last]===0)last--;
  const out=[]; let i=start;
  while(i<=last){ let j=i; while(j<=last&&tape[j]===tape[i])j++; out.push(tape[i]+'^'+(j-i)); i=j; }
  return out.join(' ');
}
function rightParse(start){
  let last=hi; while(last>=start&&tape[last]===0)last--;
  if(last<start)return null;
  let bs=last; while(bs>start&&tape[bs-1]===1)bs--;
  const L=last-bs+1, span=bs-start;
  if(span<1||(span-1)%2!==0)return null;
  const P=(span-1)/2;
  for(let j=0;j<P;j++) if(tape[start+2*j]!==0||tape[start+2*j+1]!==1) return null;
  return {P,L};
}
const bad=new Map(); const ex=[];
for(let s=0;s<MAX;s++){
  const sym=tape[pos],t=rows[q][sym]; if(!t){console.log('HALT '+s);break;}
  if(sym===0&&(q===0||q===5)&&scan>=4){
    const isF=(q===5), start=isF?pos+1:pos, r=rightParse(start);
    if(!r){ const w=runs(start).split(' ').slice(0,7).join(' ');
      const key=('AF'[isF?1:0])+': '+w; bad.set(key,(bad.get(key)??0)+1);
      if(ex.length<6) ex.push(`s${s} ${'AF'[isF?1:0]} ${runs(start).split(' ').slice(0,14).join(' ')}`); }
  }
  if((q===5&&sym===1)||(q===0&&sym===1))scan++; else if(!((q===5&&sym===0)||(q===0&&sym===0)))scan=0;
  tape[pos]=t.w; pos+=t.d==='R'?1:-1; q=t.q;
  if(pos<lo)lo=pos; if(pos>hi)hi=pos;
}
console.log('unparsed right sides, by shape (first 7 runs):');
for(const [k,v] of [...bad.entries()].sort((a,b)=>b[1]-a[1]).slice(0,30)) console.log('  '+String(v).padStart(5)+'  '+k);
console.log('\nexamples:'); ex.forEach(e=>console.log('  '+e));
