const CODE='1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows=CODE.split('_').map(s=>[0,1].map(b=>{const e=s.slice(b*3,b*3+3);return e==='---'?null:{w:+e[0],d:e[1],q:e.charCodeAt(2)-65};}));
const FROM=+process.argv[2], TO=+process.argv[3];
const N=1<<22; const tape=new Uint8Array(N);
let pos=N>>1,q=0,lo=pos,hi=pos,scan=0;
function parse(start){
  let last=hi; while(last>=start && tape[last]===0) last--;
  if(last<start) return null;
  let bs=last; while(bs>start && tape[bs-1]===1) bs--;
  const L=last-bs+1;
  const span=bs-start;                       // cells before the block
  if(span<1 || (span-1)%2!==0) return {bad:'span',span,L};
  const P=(span-1)/2;
  for(let j=0;j<P;j++)
    if(tape[start+2*j]!==0||tape[start+2*j+1]!==1) return {bad:'pat',j,P,L};
  if(tape[bs-1]!==0) return {bad:'sep',P,L};
  return {P,L};
}
for(let s=0;s<TO;s++){
  const sym=tape[pos],t=rows[q][sym]; if(!t){console.log('HALT '+s);break;}
  if(s>=FROM && sym===0 && (q===0||q===5) && scan>=4){
    const r=parse(q===5?pos+1:pos);
    let L='';
    for(let i=pos-1;i>=Math.max(lo,pos-16);i--) L+=tape[i];
    console.log(`s${s} ${'ABCDEF'[q]}@${pos-(N>>1)} left=${L||'(blank)'} | ${r?(r.bad?('BAD:'+r.bad+' '+JSON.stringify(r)):`P=${r.P} L=${r.L}`):'none'}`);
  }
  if((q===5&&sym===1)||(q===0&&sym===1))scan++; else if(!((q===5&&sym===0)||(q===0&&sym===0)))scan=0;
  tape[pos]=t.w; pos+=t.d==='R'?1:-1; q=t.q;
  if(pos<lo)lo=pos; if(pos>hi)hi=pos;
}
