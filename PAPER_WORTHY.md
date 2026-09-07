# Paper-worthy bar (continue from existing sat_3 work)

You already have `/workspace/mathlab` with papers/main.md, lean/, data/, scripts/. Do not start a new topic. Raise this to something a careful additive-combinatorics referee would take seriously.

## Definition of done (any one of A/B/C, prefer A)
A. Prove `sat_3(n)=O(√n)` for every n, with a complete human-checkable proof (Lean for the spine if possible), and rewrite the paper accordingly.
B. If A fails: prove a clean unconditional theorem that is still publishable (e.g. `sat_3(n)=O(n^α)` with α<log_3 2, or matching constants on a positive-density set of n with a sharp theorem statement), plus the verified table, with all gaps explicitly marked.
C. If the main claims collapse under scrutiny: document the counterexample/bug, salvage what is correct, and state the strongest true theorem left.

## Required process
1. Hostile review of §§6–8 first. Try to break Lemmas 6.5, 6.9–6.11 and Theorems 6.6, 6.12, 8.3–8.8. Fix or retract.
2. Deeper literature: search for "saturation" / "complete 3-AP-free" / "minimal maximal progression-free" on intervals, not only groups. Cite what exists. If the interval problem is already solved, pivot to the strongest remaining open piece you can settle.
3. Push Lean: get as much of the used spine compiling as possible. No `sorry`. Paper may still carry some inductions, but mark every non-formalized step.
4. Extend computation if useful (larger n, gap-filling experiments for base-4 holes) — but do not claim asymptotics from experiments alone.
5. Keep README tiny and casual. Keep paper tone spare. No em dashes, no hype.
6. Append every material change to notes/log.md with dates.
7. Honesty over ambition. A correct smaller theorem beats a broken big one.

## Deliverables when stopping
- Updated `papers/main.md`
- Updated `notes/log.md` with what was broken/fixed and the final claim
- Lean still builds
- A short `notes/referee-checklist.md`: list of theorems, status (proved / computational / open), and residual risks
