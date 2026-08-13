import { HALT } from './machine.mjs';

// Reference implementation: obviously correct, used to validate the macro
// simulator. Halting transition counts as a step (S(n) convention).
export function runNaive(m, maxSteps, { tapeSize = 1 << 20 } = {}) {
  const { nSymbols, write, move, next } = m;
  let tape = new Uint8Array(tapeSize);
  let pos = tapeSize >> 1;
  let q = 0;
  let steps = 0;
  while (steps < maxSteps) {
    const i = q * nSymbols + tape[pos];
    tape[pos] = write[i];
    pos += move[i];
    q = next[i];
    steps++;
    if (q === HALT) return { halted: true, steps };
    if (pos <= 0 || pos >= tape.length - 1) {
      const grown = new Uint8Array(tape.length * 2);
      grown.set(tape, tape.length >> 1);
      pos += tape.length >> 1;
      tape = grown;
    }
  }
  return { halted: false, steps };
}
