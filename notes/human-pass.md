# Human pass (2026-09-07)

Reviewer: Apollo (post-grind). Hostile read of `papers/main.md` + Lean build + independent Python checks.

## Verdict

**Private draft: yes. Public GitHub: yes, with honest README/checklist (no hype).**

Not Annals-polished. Strong enough as a public research package / preprint seed: main theorem has a clean Lean spine, citations are fair, residual risks are labelled.

## Checks run

- `lake build` in `lean/`: success, 31 jobs.
- `rg sorry` on `*.lean`: none.
- Independent Python (`sat3_cert.is_maximal`): all table witnesses `n=1..40` maximal; ext `n=41..46` maximal.
- Independent `exists_maximal` minimality: all `n≤26`; spot `n=27,32,33,40` (no smaller maximal). Full `verify_table.py` recheck left running / optional (Lean already pins `n≤40`).
- Inequality sanity: table values respect `sat² < 4n` (n≥2) and the pair-bound shape.

## Claim status

| Claim | Status |
|---|---|
| Thm 1.1 / 9.2 `sat_3(n)<2√n` | Paper proof assembles 7.4+8.3+9.1; Lean `sat3_theta` / `sat3_theta_num`. No blocker found in the spine. |
| Prop 2.2 `Ω(√n)` | Standard pair bound; Lean. |
| Table `n≤40` | Lean `sat3_eq_*` via `native_decide` enumerators (disclosed). Python agrees on checked range. |
| Ext `n=41..46` | Computational only; witnesses maximal. Do not advertise as Lean. |
| Placement Lemmas 7.2–7.3 | Read as correct; longer window than modular [2] is the right novelty claim. |
| Digits / R-complete | Properly attributed to Csajbók–Nagy [2]. |

## Blockers before public

None material for a research repo.

Polish before announce (not math blockers):

1. Tiny casual README: what `sat_3` is, Thm 1.1 one-liner, “digits from [2]; interval placement + table + Lean here,” how to `lake build`.
2. Do not claim `n≥47` values.
3. Keep `notes/referee-checklist.md` in the repo so native_decide / non-sharp constant stay visible.

## Warnings (disclose, ship anyway)

1. Exactness uses `native_decide` (computational Lean), not a closed-form proof.
2. Constant `2` is not sharp (construction hits `√n` on `n=4^k`).
3. Novelty is the interval function + placement window + table, not the digit engine.
4. `sat3` in Lean is noncomputable `Classical.choose` of a least size; upper bound is `sat3Upper`.

## Strengths

- Honest demotion of earlier overclaims (base-4 gaps, Cantor as weaker §10).
- Literature boundary with groups / covering sequences is clear.
- Main upper bound is not “experiments suggest.”

## Next

1. Optional: let full `verify_table.py` finish green once more.
2. README polish.
3. Then public under `teddytennant` or `wizardagent` (user choice); hold was only until this pass.
