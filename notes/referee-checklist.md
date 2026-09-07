# Referee checklist

Date: 2026-09-07. Claims as in `papers/main.md`.

## Theorems

| Statement | Status | Residual risk |
|---|---|---|
| Lemma 2.1 pair-bound identity | proved (Lean `pairBound_double`) | none |
| Prop. 2.2 `sat_3(n) ≥ √(2n/3)` | Lean `sat3_quadratic` / `HasMaximalOfSize_pairBound` | none |
| Lemmas 3.1–3.2, Cor. 3.3 block `S(a)` | proved (Lean `S_AP3Free`, `S_covers_interval`, `S6_maximal_16`, `sat3_exact_16`) | none |
| Lemma 3.4 / Cor. 3.5 two blocks | Lean `twoBlock_covers_11`..`16` and `twoBlocks_maximal_32` | none |
| Thm 4.1 exact `sat_3(n)` for `n≤40` | Lean `sat3 n` equals the table at every `n=1` through `40`. Rechecked by `verify_table.py` (`no_maximal_below`). Boolean checker is equivalent to maximality (`maximal_iff`) | none |
| Computational `sat_3(n)` for `n=41..46` | exhaustive backtrack, witnesses in `data/sat3_values_ext.json` | not Lean; `n=47,48` unfinished |
| §5 minimiser counts `n≤26` | computational | same |
| Lemmas 6.1–6.2 translate / shift | proved (Lean) | none |
| Def. 7.1 `R`-complete | definition, from [2] | citation |
| Lemmas 7.2–7.3 placement | proved (Lean `rcomplete_place_left`, `rcomplete_place_right`) | none |
| Cor. 7.4 | proved from 7.2–7.3 | none |
| Lemma 8.1 admissible digit step | covering and freeness in Lean (`rcomplete_admissible_step`); 54368 greedy steps k=1..5 with 0 cex; d=2S and d=3S+2 fail on every greedy set (`scripts/hostile_lemma81.py`) | none material |
| Lemma 8.2 binary `R`-complete sets | covering and freeness Lean (`rcomplete_from_admissible`). Distinct nested doubling Lean (`nodup_growFrom`). Nested union identified with that list (`greedy_set_iff`) of length `2^k` (`greedy_growFrom_length`) | none |
| Cor. 8.3 every `R∈I_k` | Lean `greedy_rcomplete` plus `greedy_growFrom_nodup` plus `greedy_growFrom_length` | none |
| Lemma 9.1 window covering | proved (Lean `chosenR_window`) | none |
| `2^k < 2√n` | proved (Lean `two_pow_sq_lt`) | none |
| Thm 9.2 / 1.1 `sat_3(n)<2√n` | Lean `sat3_theta_num` on the numerical `sat3 n`; construction `sat3_theta` | no `sorry` |
| Lemma 9.4 `sat_3(n+1)≤sat_3(n)+1` | Lean `sat3_succ_le` (and `HasMaximalOfSize_succ`) | none |
| Cor. 9.5 `sat_3(4^k+t)≤2^k+t` | Lean `sat3_le_interp`; `sat3_le_seventeen_num` | linear walk, does not improve the global constant 2 |
| §10 Cantor `O(n^{log_3 2})` | proved in the previous writeup; not used for Thm 1.1. Lean has `mixed_fills_right` | unused for the main bound |
| Former all-n `O(√n)` via base-4 tiling | retracted as an all-n statement; recovered as the extreme digits `d_i=4^{i-1}` inside Lemma 8.2 | gap after `M_k` was real for that tiling |

## Literature

- [1], [2] Csajbók–Nagy: groups and vector spaces, not `[n]`. Digit construction and `R`-complete sets are theirs; cited. Modular window `2R<m≤3R+1` is shorter than the interval window `R+1≤n≤3R+1`.
- [3] Savchev–Chen: large free sets.
- [5], [6], [7] Chen, Fang, Kiss–Sándor–Yang (arXiv:1710.01939): `AP_3`-covering sequences (saturating, not 3-AP-free).
- OEIS: no hit for the table (2026-09-07).

## Residual risks

1. `sat3 n` is a noncomputable Lean `def` (`Classical.choose` of a least size). It is not a closed form. The explicit upper bound is `sat3Upper n`.
2. Exact values for `n=1` through `40` are Lean (`sat3_eq_*`). The enumerators use `native_decide`, labelled computational.
3. The constant `2` is not sharp; along `n=4^k` the construction uses `√n` points. For `n≤40` it matches `sat_3(n)` at those powers and is strictly larger just after them.
4. Novelty is `sat_3` on the interval plus placement and the table, not the digits.
5. Spine `greedyPred_spec` no longer uses `native_decide` (kernel `decide` on `I_2={4,5}`). Table and two-block certificates still use `native_decide`, as labelled computational.
