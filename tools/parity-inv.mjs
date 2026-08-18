// The halt criterion (proved: macro_fill / macro_gap0) is that some C-scan
// erases an ODD 1-run followed by a 0-run of length >= 2. Candidate local
// invariant: at every step, EVERY maximal 1-run followed by two or more 0s
// has even length. Test it, and if it fails, test it only for runs at or
// right of the head (which is all the criterion needs).
const CODE='1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows=CODE.split('_').map(s=>[0,1].map(b=>{const e=s.slice(b*3,b*3+3);return e==='---'?null:{w:+e[0],d:e[1],q:e.charCodeAt(2)-65};}));
const MAX=+(process.argv[2]??2e6);
const N=1<<22, ORIG=N>>1; const tape=new Uint8Array(N);
let pos=ORIG,q=0,lo=ORIG,hi=ORIG;
let violAll=0,violRight=0, firstAll=null, firstRight=null, checked=0;
function scan(step){
  let i=lo;
  while(i<=hi){
    if(tape[i]===0){i++;continue;}
    let j=i; while(j<=hi&&tape[j]===1)j++;          // run [i,j)
    let z=j; while(z<=hi&&tape[z]===0)z++;           // following 0-run [j,z)
    const after=(z>hi)?Infinity:(z-j);
    if(after>=2 && (j-i)%2===1){
      violAll++; if(!firstAll) firstAll=`s${step} run@${i-ORIG} len=${j-i} zeros=${after===Infinity?'inf':after}`;
      if(i>=pos){ violRight++; if(!firstRight) firstRight=`s${step} run@${i-ORIG} len=${j-i} zeros=${after===Infinity?'inf':after} head@${pos-ORIG} state=${'ABCDEF'[q]}`; }
    }
    i=j;
  }
  checked++;
}
for(let s=0;s<MAX;s++){
  const sym=tape[pos],t=rows[q][sym]; if(!t){console.log('HALT '+s);break;}
  scan(s);
  tape[pos]=t.w; pos+=t.d==='R'?1:-1; q=t.q;
  if(pos<lo)lo=pos; if(pos>hi)hi=pos;
}
console.log(`configs checked: ${checked}`);
console.log(`violations, whole tape:            ${violAll}   ${firstAll??''}`);
console.log(`violations, at or right of head:   ${violRight}   ${firstRight??''}`);
