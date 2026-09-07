# Mission

Conduct serious mathematical research in `/workspace/mathlab`. Produce genuine novelty or stop and say so. No fabricated theorems.

## Hard constraints
1. Never claim a theorem you have not proved (Lean preferred) or for which you lack a complete human-checkable proof.
2. Computational discoveries are fine: new examples, sharper bounds for finite n, counterexamples to folklore, exhaustive classifications for small parameters. Label them as such.
3. Literature check before claiming novelty (arXiv abstracts, OEIS, Wikipedia, papers you can fetch). If it already exists, cite and pivot.
4. Languages: Rust and/or Python for search and numerics; Lean 4 for formal proofs; Lua only when it earns its keep (glue / Wizard scripting). No cargo-cult stacks.
5. Paper style: spare, definition–lemma–proof–theorem. No hype, no "revolutionary", no em dashes, no AI filler. Think Annals / Acta / Inventiones tone without mimicking any specific author.
6. `README.md` at repo root: extremely short, casual, a little entropy. Not a product page.
7. Prefer one deep result over many shallow notes.

## Suggested attack surface (pick after a real survey; change if you find a better target)
Finite combinatorial / additive problems where machine search + Lean can lock something new:
- extremal configurations (e.g. maximal size of a set avoiding a pattern, for concrete n)
- explicit constructions beating or matching known bounds for small parameters
- formalization of a new elementary inequality that unlocks a computational certificate

If the first target dies under literature check, pick another in the same spirit.

## Deliverables
- `papers/` — one main paper (LaTeX or carefully typed Markdown with proper math), plus any short notes
- `lean/` — Lake project with the proved statements compiling
- `src/` or `scripts/` — reproducible experiments (Rust and/or Python), with how to rerun
- `notes/log.md` — dated research log (failures count)
- root `README.md` — minimal

## Done when
You have either (A) a novel, correctly stated result with proof and/or exhaustive computational certificate, written up, or (B) a clear negative: surveyed, attempted, documented why novelty failed, with salvage lemmas/formalizations that are still correct.

Go hard. Stay honest.
