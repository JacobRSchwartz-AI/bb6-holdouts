import { readFileSync, writeFileSync } from 'node:fs';

// Milestone 2a: group the sealed rulebook's 1,541 lemmas into skeleton
// families. Skeleton = (width, pre block-sequence); within a family, count
// positions either agree everywhere (structural) or vary (candidate symbolic
// parameters for the ∀-form lift). Grades prediction P-2026-08-13-c.
const text = readFileSync('data/rulebook.txt', 'utf8');
const lemmas = [];
const lines = text.split('\n');
for (let i = 0; i < lines.length; i++) {
  const m = lines[i].match(/^LEMMA w=(\d+) used=(\d+)/);
  if (!m) continue;
  const pre = lines[i + 1].replace(/^\s*pre : /, '');
  const post = lines[i + 2].replace(/^\s*post: /, '');
  const steps = lines[i + 3].match(/steps=(\S+)/)[1];
  const parseRuns = (s) => s.trim().split(/\s+/).filter((t) => t !== 'CTX').map((t) => {
    const [b, c] = t.split('^');
    return { b, c };
  });
  lemmas.push({ width: +m[1], used: +m[2], pre: parseRuns(pre), post: parseRuns(post), steps, hasCtx: pre.trim().startsWith('CTX') });
}
console.log(`${lemmas.length} lemmas parsed`);

const fams = new Map();
for (const l of lemmas) {
  const key = `${l.width}|${l.hasCtx ? 'ctx' : 'full'}|${l.pre.map((r) => r.b).join(' ')}`;
  if (!fams.has(key)) fams.set(key, []);
  fams.get(key).push(l);
}

const famList = [...fams.entries()].map(([key, ls]) => {
  const nRuns = ls[0].pre.length;
  const varying = [];
  for (let p = 0; p < nRuns; p++) {
    const vals = new Set(ls.map((l) => l.pre[p].c));
    if (vals.size > 1) varying.push({ pos: p, block: ls[0].pre[p].b, vals: [...vals] });
  }
  const used = ls.reduce((a, l) => a + l.used, 0);
  return { key, size: ls.length, used, varying, lemmas: ls };
}).sort((a, b) => b.size - a.size);

console.log(`\n${famList.length} skeleton families (prediction: <=120)`);
const bySize = {};
for (const f of famList) bySize[f.size] = (bySize[f.size] ?? 0) + 1;
console.log('family-size histogram:', JSON.stringify(bySize));
const byVarying = {};
for (const f of famList) byVarying[f.varying.length] = (byVarying[f.varying.length] ?? 0) + 1;
console.log('varying-position count histogram:', JSON.stringify(byVarying));

let contiguous = 0, gapped = 0;
for (const f of famList) {
  for (const v of f.varying) {
    const nums = v.vals.filter((x) => x !== 'n').map(Number).sort((a, b) => a - b);
    const hasN = v.vals.includes('n');
    const isContig = nums.every((x, i) => i === 0 || x === nums[i - 1] + 1);
    if (isContig || (hasN && nums.length === 0)) contiguous++;
    else gapped++;
  }
}
console.log(`varying positions: ${contiguous} contiguous ranges, ${gapped} with gaps`);

console.log('\ntop 20 families by lemma count:');
for (const f of famList.slice(0, 20)) {
  const varStr = f.varying.map((v) => {
    const nums = v.vals.filter((x) => x !== 'n').map(Number).sort((a, b) => a - b);
    const range = nums.length ? `${nums[0]}..${nums[nums.length - 1]}` : '';
    return `pos${v.pos}(${v.block}):${range}${v.vals.includes('n') ? '+n' : ''}`;
  }).join(', ');
  console.log(`  size=${String(f.size).padStart(3)} used=${String(f.used).padStart(6)} ${f.key.split('|').slice(0, 2).join('|')} | ${f.lemmas[0].pre.map((r) => r.b).join(' ')}`);
  if (f.varying.length) console.log(`      varying: ${varStr}`);
}

const out = [];
for (const f of famList) {
  out.push(`FAMILY size=${f.size} used=${f.used} ${f.key}`);
  for (const v of f.varying) out.push(`  varying pos${v.pos} (${v.block}): ${v.vals.join(',')}`);
  const sample = f.lemmas[0];
  out.push(`  sample pre : ${sample.pre.map((r) => `${r.b}^${r.c}`).join(' ')}`);
  out.push(`  sample post: ${sample.post.map((r) => `${r.b}^${r.c}`).join(' ')}`);
  out.push(`  sample steps=${sample.steps}`);
}
writeFileSync('data/families.txt', out.join('\n') + '\n');
console.log(`\nwrote data/families.txt`);
