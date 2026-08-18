// At every deep turn, decide which PROVEN lemma applies. Report any gaps.
const CODE='1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows=CODE.split('_').map(s=>[0,1].map(b=>{const e=s.slice(b*3,b*3+3);return e==='---'?null:{w:+e[0],d:e[1],q:e.charCodeAt(2)-65};}));
const MAX=+process.argv[2];
const N=1<<24; const tape=new Uint8Array(N);
let pos=N>>1,q=0,lo=pos,hi=pos,scan=0;
const tally={}, gaps=[]; const fill={gap0:0,even:0,ODD:0}; let fillStart=-1;
function W(h,n){let s='';for(let i=0;i<n;i++){const c=h-i; s+= (c<lo||c>hi)?0:tape[c];}return s;}
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
for(let s=0;s<MAX;s++){
  const sym=tape[pos],t=rows[q][sym]; if(!t){console.log('HALT '+s);break;}
  if(sym===0&&(q===0||q===5)&&scan>=4){
    const isF=(q===5), r=rightParse(isF?pos+1:pos);
    let tag;
    if(!r) tag='RIGHT-UNPARSED';
    else if(!isF){                       // A-turn: half_period family
      if(r.L%2!==0) tag='A:ODD-BLOCK';
      else if(r.P>=5) tag='half_period';
      else if(r.P===4) tag='half_period_4';
      else if(r.P===2) tag='half_period_2';
      else tag='A:P='+r.P;
    } else {                             // F-turn: wall cases
      const w=W(pos,40);
      const classA=(()=>{ if(w[0]!=='0'||w[1]!=='0')return null;
        let i=2,d=0;
        while(w.slice(i,i+4)==='1100'){d++;i+=4;}
        return (w[i]==='0'&&w[i+1]==='0')?d:null; })();
      const classB=(w.slice(0,5)==='01100');
      const restr=(()=>{ if(w[0]!=='0'||w[1]!=='0')return null;
        let i=2,d=0;
        while(w.slice(i,i+4)==='1100'){d++;i+=4;}
        let n=0; while(w[i+n]==='1')n++;
        return n>=3?{d,n}:null; })();
      if(r.P===1) tag = (classA!==null)?'era_boundary_d(d='+classA+')':'BOUNDARY-UNCOVERED';
      else if(r.P<3) tag='F:P='+r.P;
      else if(classA!==null) tag='f_to_a(d='+classA+')';
      else if(classB) tag='f_to_a_era';
      else if(restr) tag='restructure_'+(restr.n%2?'odd':'even');
      else tag='F-UNCOVERED:'+w.slice(0,12);
    }
    tally[tag]=(tally[tag]??0)+1;
    if(tag.includes('UNCOVERED')||tag.startsWith('A:')||tag.startsWith('F:')) if(gaps.length<8) gaps.push(`s${s} ${tag} P=${r?r.P:'?'} L=${r?r.L:'?'}`);
  }
  // halt-guard coverage: every D/E fill scan, classified by the lemma that
  // discharges it. macro_gap0 (gap 0) and macro_fill (even gap) are proved
  // for arbitrary context on both sides, so these two exhaust the safe cases.
  if(q===3&&sym===0&&fillStart<0) fillStart=pos;
  if((q===3||q===4)&&sym===1){
    if(fillStart<0) fill.gap0++;
    else { const g=fillStart-pos; fill[g%2===0?'even':'ODD']++; }
    fillStart=-1;
  }
  if((q===5&&sym===1)||(q===0&&sym===1))scan++; else if(!((q===5&&sym===0)||(q===0&&sym===0)))scan=0;
  tape[pos]=t.w; pos+=t.d==='R'?1:-1; q=t.q;
  if(pos<lo)lo=pos; if(pos>hi)hi=pos;
}
console.log('deep-turn coverage over '+MAX+' steps:');
for(const k of Object.keys(tally).sort()) console.log('  '+String(tally[k]).padStart(6)+'  '+k);
console.log('\nhalt-guard coverage (every fill scan the machine performs):');
console.log('  '+String(fill.gap0).padStart(6)+'  macro_gap0   gap 0, safe for any run length');
console.log('  '+String(fill.even).padStart(6)+'  macro_fill   even gap, safe');
console.log('  '+String(fill.ODD).padStart(6)+'  ODD GAP      this is the halt; must stay 0');
if(gaps.length){console.log('\nfirst gaps:'); gaps.forEach(g=>console.log('  '+g));} else console.log('\nNO GAPS.');
