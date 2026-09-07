# Hostile review of sat_3 (live spine §§6–9)

Date: 2026-09-07. Role: break the lemmas used for Theorem 1.1, or confirm them.

The 2026-09-06 Cantor audit is kept at the bottom. It is not the proof of Theorem 1.1.

Commands: `python3 scripts/hostile_lemma81.py`, `python3 scripts/rcomplete.py 256`, `python3 scripts/verify_table.py`, `cd lean && lake build`.

## Executive summary

| Claim | Verdict |
|---|---|
| Lemma 6.1–6.2 translate / shift | PASS (Lean) |
| Def. 7.1 / Lemmas 7.2–7.3 / Cor. 7.4 placement | PASS; 0 placement failures on every R in I_1..I_4 and every n in the window |
| Lemma 8.1 admissible digit | PASS; 54368 greedy steps k=1..5, 0 cex. Bounds d=2S and d=3S+2 fail on every greedy set |
| Lemma 8.2 / Cor. 8.3 | PASS (Lean `rcomplete_from_admissible`, `greedy_rcomplete`, `nodup_growFrom`) |
| Lemma 9.1 / Thm 9.2 / 1.1 | PASS (Lean `sat3_theta` for every n≥1) |
| Prop. 2.2 pair bound | PASS (Lean `HasMaximalOfSize_pairBound`) |
| Thm 4.1 table n≤40 | Lean PASS (`sat3_eq_one`..`sat3_eq_forty`); rechecked by `verify_table.py` |
| Former all-n O(√n) via base-4 tiling | retracted; variable digits close the gap |
| Interval problem already solved? | No. arXiv hit for interval saturation is still only Csajbók–Nagy on Z_m / F_p^n |

No proof bug found that collapses Theorem 1.1. Residual risks are naming (`sat3 n` is a noncomputable least size, not a closed form) and the constant 2.

## 1. Lemma 8.1

Hypotheses: A ⊆ [0,S] is S-complete, 2S+1 ≤ d ≤ 3S+1.
Conclusion: A ∪ (A+d) is (S+d)-complete.

Freeness uses d > 2S. Covering uses four intervals I-d, I, I+d, I+2d, which abut once d ≤ 3S+1.

```
$ python3 scripts/hostile_lemma81.py
admissible steps checked: 54368
counterexamples under stated hyps: 0
unexpected OK at d=2S: 0
unexpected OK at d=3S+2: 0
exhaustive S-complete S=1..6: checked 13 fail 0
placement failures inside window: 0
PASS
```

Sample tightness (not a bug): S=1, d=5=3S+2 leaves misses {-2,3,8}; S=4, d=14 leaves {-5,9,23}. The upper bound is load-bearing.

Lean: `separated_union_AP3Free`, `mixed_left_I`, `mixed_right_I`, `admissible_shift_covers`, `rcomplete_admissible_step`. Compiles; no `sorry`.

## 2. Placement (7.2–7.4)

Window R+1 ≤ n ≤ 3R+1. Left shift +1 when n ≤ 2R+1; right shift n-2R when n ≥ 2R+1.

Every greedy R-complete set for R in I_1..I_4, placed at every n in the window, is free and endpoint-covers [n]. Zero failures.

Lean: `rcomplete_place_left`, `rcomplete_place_right`, `rcomplete_place`.

## 3. Digits and the window (8.2, 8.3, 9.1)

`greedyPred_spec` is kernel `decide` on I_2={4,5} and an omega argument for k≥2 from ℓ_k ≥ 4. No `native_decide` on the spine.

`rcomplete.py 256`: every n=1..256, the placed greedy set is free, covers [n], has size 2^k, and (2^k)^2 < 4n.

## 4. Literature (arXiv, 2026-09-07)

Query `saturation` + `arithmetic progression` + interval/[1,n]: one hit, arXiv:2606.30186 (Csajbók–Nagy, cyclic groups and vector spaces). Query `R-complete` + progression: no extra hits. The interval function sat_3(n) is not independently tabulated.

Cite [2] for the digits and the R-complete definition. Novelty is the longer placement window without wrap-around, the table, and the Lean spine. Do not advertise "first O(√n) for intervals".

## 5. What was not broken

- No counterexample to Lemma 8.1 under stated hyps.
- Digit bounds are tight on greedy sets.
- Placement window has no interior holes on the probed range.
- Pair bound and sandwich compile.
- Table witnesses n≤40 recheck.

## 6. Residual (not bugs)

1. `sat3 n` is a noncomputable Lean `def` (`Classical.choose` of a least size), not a closed form.
2. Exact values through n=40 are Lean (`sat3_eq_*`); the enumerators use `native_decide`.
3. Constant 2 is an artefact of n just after a power of 4.
4. Cantor §10 is unused for Theorem 1.1; `mixed_fills_right` is Lean, the rest of §10 is paper.

---

## Appendix: 2026-09-06 Cantor audit (superseded for the main bound)

That review tested Lemmas 6.5, 6.9–6.11 and Theorems 6.6, 6.12, 8.5 against the S-block Cantor construction. Those statements were not used for Theorem 9.2. The gap after M_k was real for base-4 tiling and is closed by variable admissible digits. Keep the old computational notes in `scripts/hostile_lemma65.py`, `scripts/hostile_probe.py`, `scripts/cantor_blocks.py`.
