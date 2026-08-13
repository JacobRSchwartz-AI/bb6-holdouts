// Standard format: states separated by '_', each state has one 5-char entry
// per symbol: <write><dir><next>, e.g. "1RB", "0LF", "---" (undefined = halt),
// or explicit halt "1RZ". States A.. map to 0.., symbols are '0'/'1'.

export const HALT = -1;

export function parseMachine(code) {
  const states = code.trim().split('_');
  const nStates = states.length;
  const nSymbols = states[0].length / 3;
  const write = new Int8Array(nStates * nSymbols);
  const move = new Int8Array(nStates * nSymbols);
  const next = new Int8Array(nStates * nSymbols);
  for (let s = 0; s < nStates; s++) {
    for (let b = 0; b < nSymbols; b++) {
      const t = states[s].slice(b * 3, b * 3 + 3);
      const i = s * nSymbols + b;
      if (t === '---') {
        write[i] = 1; move[i] = 1; next[i] = HALT;
      } else {
        write[i] = t.charCodeAt(0) - 48;
        move[i] = t[1] === 'R' ? 1 : -1;
        const q = t.charCodeAt(2) - 65;
        next[i] = q >= nStates ? HALT : q;
      }
    }
  }
  return { code: code.trim(), nStates, nSymbols, write, move, next };
}

export const stateName = (q) => (q === HALT ? 'Z' : String.fromCharCode(65 + q));
