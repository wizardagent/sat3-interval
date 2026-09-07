# Research log

## 2026-09-06

Empty tree. Lean 4.33.1, Python 3.13, Rust 1.98. No mathlib (deliberate).

### Survey

Rejected as already tabulated:
- r_3(n) = A003002 (to n=211, Cariboni)
- integer-ratio GP-free A230490, rational-ratio A208746
- min complete 3-AP-free in Z_m and F_p^n: Csajbok-Nagy arXiv:2401.06283 and 2606.30186
- distinct-variable Rado x+y=nz: A394445 to n=500
- graceful / sparse rulers A004137

Candidate: sat_3(n) = min size of a *maximal* 3-AP-free subset of [n].
OEIS sequence search for 1,2,2,2,3,4,4,4,4,4,4,4,4,4,4,4,5,6,... : no hit.
arXiv/Crossref: Csajbok-Nagy treat groups, not the interval. Savchev-Chen 2006 is uniqueness of large free sets. Eggleton 2015 is digit-restricted midpoint-free subsets of Z, not sat_3([n]).

### Computation

Backtrack over increasing k, prune by midpoint, test maximality via pair completions.

sat_3(n) for n=1..40:
1,2,2,2,3, then 4 (n=6..16), 5 (n=17), 6 (n=18..26), 7 (n=27..32), 8 (n=33..40).

Counts of minimisers n=1..26:
1,1,3,1,2,4,10,25,34,24,21,12,7,4,2,1,2,154,146,104,78,46,26,13,6,2.
Also absent from OEIS.

### Construction

S(a)={a,a+1,a+4,a+5} is 3-AP-free and pair-completions fill [a-5,a+10] (16 points).
S(6) is the unique minimiser in [16].
S(6) U S(22) is maximal in [32].
S(0) U S(d) is free for d=11..16; d=16 fills 64 consecutive integers in Z (not necessarily a translate of [64] inside [n]).
Three blocks at distance 16 are not free (0,16,32).

Recursive lift of a minimiser in [m] by replacing each point with S(6+16(b-1)) is *not* always maximal in [16m]. Some minimisers lift, some leave holes. Not a theorem.

### Formalisation

Lake project `lean/` without mathlib.
Proved: S_AP3Free, S0_covers, S_covers_interval, S6_maximal_16, twoBlocks_maximal_32, pairBound_double.
Boolean certificates via native_decide for selected n.

### Honesty

Exact values are computational (exhaustive search). The covering lemmas and the pair identity are proofs. Asymptotics of sat_3(n) remain open; only Omega(sqrt(n)) from the pair bound and O(n) trivial.

## 2026-09-06, later

Tried to get a matching O(sqrt(n)) construction.

Failed: tiling S-blocks at distance 16 produces 3-APs of centres (0,16,32).
Failed: convex / square centre progressions are not 3-AP-free after expanding S.
Failed: Sidon sets are too sparse to cover.

Worked: centres at 6+11b with b in the Cantor set B (ternary digits in {0,1}).
Proof that the infinite union is 3-AP-free: 2T-T-T subset [-10,10] forces the centre equation 2b=b'+b'' after dividing by 11, then T-degenerate. Human-checkable; T-lemmas in Lean (`T_degenerate`).

Covering is *not* proved. Computational: A_k covers [1, 11*3^k+5] for k=0..7 (n up to 24062, 512 points). Clipped construction misses a few n (1-10, 20-21, 42-43, 53-54, 999-1000).

Upper bound sat_3(L_k) <= 4*2^k = O(L_k^{log_3 2}). Exponent 0.63 > 1/2, so this does not match the pair bound. Recorded as computational covering plus a proved freeness theorem.

Covering induction found and written as Theorem 6.6.

Lemma: if A endpoint-covers [1, d+5] then A ∪ (A+d) endpoint-covers [1, 3d+5], by splitting into left (A), middle (A+d), right (mixed pairs 2(A+d)-A). Distinctness on the right uses u≥6.

Base: S(6) covers [1,16]. Recurrence A_{k+1}=A_k ∪ (A_k + 11·3^k) matches L_{k+1}=3d+5.

Monotonicity of sat_3 is false in general (a maximal set in [n] need not remain maximal in [n-1]), so the all-n bound does not follow from the L_k case by padding. The truncated construction plus at most one point (Theorem 6.12) is the actual all-n argument.

Lean: endpoint_covers_translate and mixed_fills_right (Lemma 6.5) compile, the latter with support A ⊆ [1,d+5]. Theorem 6.6 itself is a paper induction, not a Lean theorem.

Predecessor cover proved (Lemma 6.9): induction on the Cantor integer b=3^k+m. Left copy A_k covers [1,d+5]; the strictly smaller predecessor A^{<c_m} translates by d=11*3^k onto [d+1,c-1].

No pair from A^{<c} completes the hole c+3 (Lemma 6.10): the Theorem 6.2 rearrangement, with third vertex offset 3 rather than a T-point, still forces the centre equation in B after bounding 2T-T-{3} and 6-T-T inside (-11,11).

Last-block classification (Lemma 6.11) plus one-point repair (Lemma 6.7) give sat_3(n) <= 4 N(n) + 1 for every n (Theorem 6.12), hence O(n^{log_3 2}) unconditionally. Along L_k the +1 is unnecessary.

one_point_repair still not in Lean.

Tried base-4 centres B^{(4)} (digits {0,1} in base 4). Freeness is a theorem: no carry in 2eps = eps'+eps'' with digits 0,1, so B^{(4)} is 3-AP-free, and Theorem 6.2 carries over (Theorem 8.2).

Covering of I(A)=[2min-max, 2max-min] for base-4 is now an induction (Theorem 8.5). Three pieces: I(A), I(A)+D, I(A)+2D. The last is mixed endpoints 2(A+D)-A. They overlap by 5 because 3(max-min)=D+4. Distinctness of mixed triples uses 2(max-min)<D, which is D>8.

mixed_double_shift compiles once the diameter bound 2(hi-lo)<d is an explicit hypothesis (omega can then keep d). Formalised as mixed_parents_distinct / mixed_double_shift. The four-interval abutment (Lemma 8.4) and the identification I(A_k)=[2min-max, 2max-min] remain paper arithmetic.

Corollary 8.6: A_k is already maximal in every [n] with max(A_k) <= n <= M_k, because A_k subset [n] and the covering of [1,M_k] restricts. That is a positive-density set of n (about 1/3 of each dyadic block) with sat_3(n)=O(sqrt n).

Hard range: (M_k, max A_{k+1}), length Theta(4^k). Truncation of A_{k+1} leaves Theta(4^k) holes. One extra S-block extends the covered run by at most 16 (k<=2). Greedy fill from A_k into the gap adds up to about |A_k| points (still O(sqrt n) experimentally) but is not a proof.

Lemma 8.7: sat_3(n+1) <= sat_3(n)+1, by adjoining n+1 if unblocked. Linear interpolation, useless for the exponent.

Corrected overclaim: mixed_double_shift uses 2|I|<d, which fails for I(A) (length 3 diam +1). Paper Lemma 8.3 uses 2(max-min)<D on the support. Lean lemma is a different, stronger-diameter statement.

Lemma 8.7: L ∪ (L + 4^k-1) is 3-AP-free by separation (max L = (4^k-1)/3, min R = 4^k-1, 2 max L < min R and 2 min R - max R > max L). Digit profiles {0,1} vs {1,2}.

Theorem 8.8: U_k = A_k ∪ (A_k + 11(4^k-1)) is free (6.2 + 8.7) and fills I(U_k) by Lemma 8.3 (2 diam < D' for k>=1; overlap 16). |U|=8*2^k, max = m_{k+1}-11. Does not close the gap just after M_k, because the right copy starts at 11*4^k-5 > M_k for k>=2.

All-n O(sqrt n) still open. All-n bound remains Theorem 6.12.

## Hostile review landed (external)
See notes/hostile-review.md and PRIORITY.md. Citation gap vs Csajbók–Nagy 2606.30186 is load-bearing for novelty.

## 2026-09-07

Hostile review of former §§6–8: Lemmas 6.5, 6.9–6.11 and Theorems 6.6, 6.12, 8.3–8.8 stand computationally (Cantor k=0..5, base-4 k=0..5, repair n=11..400). No counterexample. Lean mixed_fills_right still matches Lemma 6.5.

Literature: Csajbók–Nagy arXiv:2606.30186 already introduce R-complete sets on Z (A subset [0,R] endpoint-fills [-R,2R]) and use them to get a(3-AP, Z_m)<2 sqrt(m). Interval [n] is not treated. Their modular window is 2R<m<=3R+1 (wrap-around). Chen / Fang AP3-covering sequences saturate N without 3-AP-freeness. OEIS still has no hit for the sat_3 table. The interval problem was open.

The former all-n bound was O(n^{log_3 2}) via Cantor centres. Base-4 centres gave O(sqrt n) only on [m_k, M_k]. The gap after M_k is real for that construction.

Closed the gap by importing the CN digit construction (Lemma 8.2 / Corollary 8.3, cited) and adding two placement lemmas that do not wrap around: an R-complete set of size 2^k sits in [n] whenever R+1 <= n <= 3R+1. For 4^{k-1}<n<=4^k such an R exists in I_k. Hence sat_3(n) <= 2^k < 2 sqrt(n) for every n>=2.

Novelty: not the digits (those are [2]), but the function sat_3 on the interval, the longer placement window, the exact table, and the Lean spine.

Lean: Sat3/RComplete.lean compiles. Proved: IsRComplete, rcomplete_01, separated_union_AP3Free, mixed_left_I, mixed_right_I, admissible_shift_covers, rcomplete_admissible_step, rcomplete_place_left, rcomplete_place_right. No sorry. Paper still carries digit existence, S_k=I_k, and 2^k<2 sqrt(n).

Scripts: rcomplete.py checks the placed sets for n=1..200 (and the construction for n=1..5000 earlier). verify_table.py still green.

Final claim: sat_3(n)<2 sqrt(n) for every n (Theorem 1.1 / 9.2). Pair bound Omega(sqrt n). Exact values n<=40 computational.

## 2026-09-07, later

Pushed the remaining arithmetic of Theorem 9.2 into Lean (`Sat3/Bounds.lean`): Ilo/Ihi recurrences, Ilo_le_Ihi, four_pow_Ihi, three_pow_Ilo, lower_window, two_pow_sq_lt, chosenR_window. No sorry. lake build green.

Digit reconstruction: greedy largest previous sum works for every R in I_k, k=1..7 (4369 values at k=7). scripts/rcomplete.py now uses that instead of a search.

Paper Lemma 9.1 rewritten around the explicit R = max(Ilo_k, ceil((n-1)/3)).

## 2026-09-07, evening

Tried to Lean-prove the greedy predecessor `S = min(Ihi k, floor((R-1)/3))` for R in I_{k+1}. Init-only omega/min lemmas fought the k=1 edge (S=1). Reverted that block so lake build stays green.

Wrote a complete paper proof of the same step in Corollary 8.3: lower digit bound from 3S ≤ R-1; upper bound by cases S = Ihi_k (then R ≤ 4S+1) or S = floor((R-1)/3) (then R ≤ 3S+3, and S ≥ 2 for k ≥ 2; k=1 falls in the first case). Dropped the k≤7 computational hedge.

Lemma 9.1 notation cleaned (A,B instead of Ilo_k).

## 2026-09-07, night

Lean now has `greedyPred_spec` in `Sat3/Digits.lean`. The `k=1` step is `native_decide` on `I_2={4,5}`. The `k≥2` step uses `Ilo_ge_four` (`ℓ_k ≥ 4`) so that `R ≤ 3S+3` implies `R ≤ 4S+1`. No sorry. lake build green (12 jobs).

`scripts/rcomplete.py` now property-tests greedy predecessors for every R in I_k, k=2..6, before placing sets in [n].

Paper Corollary 8.3 cites `greedyPred_spec`. Remaining paper-only pieces: digitwise avoidance in Lemma 8.2, and `S_k=I_k` by overlapping unions.

## 2026-09-07, later night

Lean `admissible_sum_in_I`: an admissible digit from I_k lands in I_{k+1}. Together with `greedyPred_spec` this is both directions of the I_k recurrence, minus the overlapping-union argument that consecutive images [3S+1,4S+1] cover I_{k+1} without holes.

## 2026-09-07, cycle 12

Rewrote Corollary 8.3 around the greedy predecessor (already Lean) instead of the overlapping-union slogan. Existence of digits for every R in I_k is now: greedyPred_spec + induction on k + Lemma 8.2. Overlapping unions demoted to a parenthetical; consecutive_images_overlap is Lean but unused for the main bound.

Added greedyPred_in_image and consecutive_images_overlap. lake build green.

## 2026-09-07, cycle 12 continued

Lean `greedyDigits k R` is the k-fold greedy sequence. Theorems `greedyDigits_length` and `greedyDigits_sum` compile: for R in I_k the list has length k and sums to R. Corollary 8.3 is now constructive in Lean except Lemma 8.2's digitwise avoidance, which is still paper.

## 2026-09-07, cycle 12 last-digit

`greedyDigits_last_admissible`: unfolding plus `greedyPred_spec`. Every greedy prefix is an admissible step. lake build green. Remaining paper step in Cor 8.3 is Lemma 8.2 applied to that list.

## 2026-09-07, cycle 12 admissible

`IsAdmissible` / `AdmissibleFrom` encode the digit bounds. `greedyDigits_admissible` proves the greedy list for every R in I_k is admissible. lake build green, no sorry. Corollary 8.3 now: Lean supplies the digits; Lemma 8.2 (paper) turns them into an R-complete set.

## 2026-09-07, cycle 12 covering iteration

`Sat3/FromDigits.lean`: `rcomplete_from_admissible` iterates `rcomplete_admissible_step` along an admissible list. `greedy_rcomplete` is Corollary 8.3 covering: greedy digits yield an R-complete set. lake build green (13 jobs), no sorry.

The upper bound sat_3(n) ≤ 2^k only needs |nested union| ≤ 2^k, which is doubling, not distinctness. Digitwise avoidance is no longer load-bearing for Theorem 9.2.

## 2026-09-07, cycle 13 cardinality

`Sat3/Card.lean`: `subsetSums` of a digit list has length `2^{length}` by construction (`P ++ mapAdd d P`). Combined with `greedyDigits_length`, `greedy_subsetSums_length` gives multiplicity `2^k`. lake build green (14 jobs), no sorry.

The nested-doubling count for Theorem 9.2 is now Lean. Remaining paper step is distinctness (not needed for the O(sqrt n) bound).

## 2026-09-07, cycle 13 nested union = subset sums

`Sat3/Card.lean`: `Mem` is list membership without mathlib. `buildFrom_spec` says a point of the nested union is a base point plus a subset sum of the remaining digits. `buildFrom_01_subsetSums` specialises to `{0,1}`. `greedyDigits_cons_one` plus `greedy_support` identify every point of the greedy `R`-complete set with an entry of `subsetSums (greedyDigits k R)`, a list of length `2^k`. lake build green (14 jobs), no sorry.

The R-complete predicate and the `2^k` list are now identified. Distinctness (hence exact cardinality) remains paper; Theorem 9.2 only needs the upper bound.

## 2026-09-07, cycle 14 Theorem 9.2

`Sat3/Thm.lean`: `windowK n = (n-1).log2/2 + 1` is the unique `k` with `4^{k-1}<n≤4^k`. `rcomplete_place` is Corollary 7.4. `placedGreedy_maximal` places the greedy nested union into `[n]`. `placedGreedy_support` identifies every point with a shifted subset sum. `sat3_construction` packages maximality, the `2^k` list, and `(2^k)^2<4n` for every `n≥2`. lake build green (15 jobs), no sorry.

Literature check (arXiv API, 2026-09-07): the only hit for complete 3-AP-free / saturation in this area remains Csajbók–Nagy on groups and vector spaces, not `[n]`. No hit for "maximal 3-AP-free" or "saturation number" + arithmetic progression.

Remaining paper: distinct subset sums (not needed for the O(√n) bound); the name `sat_3` as a min-cardinality; exact table minimality. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 15 distinct subset sums

`Sat3/Distinct.lean`: `Nodup` and `Bounded` on `List Nat`. If `P ⊆ [0,S]` is duplicate-free and `d ≥ 2S+1`, then `P` and `P+d` are disjoint (`disjoint_shift`), so `P ++ mapAdd d P` is duplicate-free (`nodup_grow`). Iterating along `AdmissibleFrom` gives `nodup_growFrom`. The greedy nested union is exactly `growFrom [0,1] tail` (`greedy_set_iff`) of length `2^k` (`greedy_growFrom_length`) and duplicate-free (`greedy_growFrom_nodup`). lake build green (16 jobs), no sorry.

Lemma 8.2 cardinality is now Lean. Remaining paper: the name `sat_3` as a min-cardinality; exact table minimality; the unused digitwise 3-AP coefficient argument (freeness is already the inductive step). Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 16 exact size 2^k

`sat3_construction` now packages: maximality of the placed greedy set; identification with the shifted nested-doubling list (`placedGreedy_iff`); that list is `Nodup` of length `2^k`; and `(2^k)^2<4n`. lake build green (16 jobs), no sorry.

The construction is a maximal 3-AP-free subset of `[n]` of size exactly `2^k`. Remaining paper: the name `sat_3` as a min-cardinality; exact table minimality. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 17 existence form

`sat3_upper`: for every `n≥2` there exists a maximal 3-AP-free subset of `[n]` equal to a shifted duplicate-free list of length `2^{windowK n}`, with `(2^k)^2<4n`. Stale "paper induction" line in §8 removed (`greedyDigits_admissible` is Lean). Python `k_for` / `choose_R` / `place_shift` now match Lean `windowK` / `chosenR` / `placeShift`; `check_lean_window` asserts the window identities.

## 2026-09-07, cycle 18 named existence bound

`HasMaximalOfSize n k` is the Lean stand-in for `sat_3(n) ≤ k`. `sat3_le_two_pow` and `sat3_O_sqrt` package Theorem 9.2 as `HasMaximalOfSize n (2^k)` together with `(2^k)^2<4n`. Literature: Csajbók–Nagy [2] treat `Z_m` and `F_p^n`, not `[n]`; no arXiv hit for independent domination of 3-APs on the interval. lake build green (16 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 19 referee polish

Moved the Lean inventory out of §1 into §11; added a four-sentence lead. Compared construction size `2^k` to the table: equals `sat_3(n)` at `n=1,4,16` and throughout `6..16` and `33..40`; strictly larger just after each power of 4 (`5,17..32`). Max ratio `2^k/sat_3` on `n≤40` is 1.6. Remark 9.3 records this. No Lean change. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 20 pair bound quadratic

`pairBound_half`: `k(3k-1)/2 = pairBound k`. `pairBound_quadratic`: `n ≤ pairBound k` implies `2n ≤ 3k²`, the Lean half of Proposition 2.2. Stale `PRIORITY.md` (all-n O(√n) still OPEN) rewritten to match Theorem 9.2. lake build green (16 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 21 table vs construction

`scripts/verify_table.py` now also checks, for each `n≤40`, that the greedy placed set is maximal of size `2^k` and that `sat_3(n) ≤ 2^k`. Chen [5] already cites Kiss–Sándor–Yang for covering sequences; no extra bibliography entry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 22 all-n Lean theorem

`sat3_O_sqrt` now covers every `n≥1`: `{1}` when `n=1`, and `HasMaximalOfSize n (2^k)` with `(2^k)^2<4n` when `n≥2`. Trimmed the unused digitwise 3-AP coefficient paragraph in Lemma 8.2; the Lean nested-doubling proof is the one used. lake build green (16 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 23 construction-agnostic size

`HasMaximalOfSize n k` no longer mentions `placeShift` or greedy digits: it is a maximal set equal to a duplicate-free `List Int` of length `k`. `sat3_le_two_pow` realises it by shifting the nested-doubling list. lake build green (16 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 24 Lemma 3.4 certificates

Boolean `twoBlockCovers d` checks that `S(0) ∪ S(d)` is 3-AP-free and endpoint-covers `[-d-5, d+10]`. Native-decide theorems for `d=11..16`. Checklist no longer lists inspection as residual risk. lake build green (16 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 25 Lemma 3.4 independent check

Python recomputation: for each `d=11..16`, `S(0)∪S(d)` is 3-AP-free and endpoint-miss on `[-d-5,d+10]` is empty. Lean window length `2d+16` equals the span. Marked `notes/hostile-review.md` superseded: all-n `O(√n)` is Theorem 9.2. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 26 rust verifier

`src/verify.rs` is a no-crate second check of the 40 table examples. `rustc -O` and run: `verified 40 examples`. Wired into the README command list. Independent of Python `sat3_cert`. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 27 boolean soundness

`Sat3/Sound.lean`: `maximal n A = true` implies `MaximalAP3Free n (ofIntList A)`. Lifted table certificates (`maximal_of_cert_n1`, `_n2`, `_n4`, `_n5`, `_n16`, `_n40`). lake build green (17 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 28 pair covering

`Sat3/PairCover.lean`: `coverList A = A ++ pairsCover A` concatenates the three third-points of each pair. `coverList_covers` says every point of `[n]` lies in that list. `interval_le_cover` injects `[n]` into it, so `n ≤ |coverList A|`. `coverList_length` equals `pairBound |A|`. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 29 pairBound length

`pairsCover_length`: the concatenated third-point list has length `3 * C(|A|,2)`. `coverList_length` equals `pairBound |A|`. Combined with `interval_le_cover`, `pairBound_of_maximal` is Proposition 2.2 for list-encoded sets. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 30 HasMaximalOfSize pair bound

`MemInt` identified with `List.Mem`. `MaximalAP3Free_ofIntList` transfers maximality. `HasMaximalOfSize_pairBound`: a maximal set of size `k` forces `n ≤ pairBound k`. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 31 sandwich

`sat3_theta`: for `n≥2`, `HasMaximalOfSize n (2^k)` and `(2^k)^2<4n`, and every maximal set of size `k` satisfies `2n≤3k²`. That is Theorem 1.1 without naming `sat_3`. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 32 all-n sandwich

`sat3_theta` now holds for every `n≥1`: `HasMaximalOfSize 1 1` at `n=1`, and `sat3Upper n = 2^k` with `(2^k)^2<4n` for `n≥2`, plus `2n≤3k²` for every maximal set of size `k`. Stale log line about covering-list length being paper is corrected (`coverList_length` is Lean). lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 33 hostile spine

Hostile review of the live spine (§§6–9), not the unused Cantor writeup. Lemma 8.1: 54368 greedy admissible steps k=1..5, 0 counterexamples; d=2S and d=3S+2 fail on every greedy set. Placement window: 0 failures for every R in I_1..I_4. `greedyPred_spec_one` no longer uses `native_decide` (kernel `decide` on I_2={4,5}). arXiv still has no independent solution of interval sat_3. `notes/hostile-review.md` rewritten. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 34 exact pin

`pairBound_mono` and `HasMaximalOfSize_ge`: if a maximal set of size `k` exists and `pairBound (k-1) < n`, every maximal set has size at least `k`. Instantiated as `sat3_exact_when_pin` at the construction size, and as `sat3_exact_16` (Corollary 3.3) plus `n=1,2,3,4,13,14,15`. Those eight values of `sat_3` are now Lean, not just the table. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 35 one-step extension

`maximal_extend_right`: a maximal set in `[n]` extends to `[n+1]` by adjoining `n+1` at most. Lifted to `HasMaximalOfSize_succ` and `Sat3Le_succ` (`sat_3(n+1)≤sat_3(n)+1`). Interpolation `sat3_interp`: `Sat3Le (4^k+t) (2^k+t)`. Instances `sat3_le_five` and `sat3_le_seventeen` match the table jumps. Linear walk does not improve the global constant 2. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 36 retract n=5 pair-bound overclaim

Corollary 9.5 claimed the pair bound forces `k≥3` at `n=5`. False: `pairBound 2 = 5`. Retracted. Replaced by a case analysis: no two-point set is maximal in `[5]` (`not_maximal_pair_five`, `not_HasMaximalOfSize_5_2`), so with the interpolation upper bound one has `sat3_exact_5`. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 37 literature and table honesty

Kiss–Sándor–Yang cited as [7] (arXiv:1710.01939, as in Chen [5]); covering sequences, not 3-AP-free. Abstract and Theorem 4.1 no longer call every `n≤40` computational: Lean exactness at `n=1,2,3,4,5,13,14,15,16` is stated up front. Remaining table witnesses lift through `maximal_sound` (`maximal_of_cert_n3`, `_n6`, `_n9`, `_n17`, `_n18`, `_n22`, `_n26`, `_n27`, `_n32`, `_n33`). lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 38 numerical least size

`exists_least_maximal` (strong rec on the construction size) supplies a least `k` with `HasMaximalOfSize n k`. `sat3_min` packages that least `k` with `k≤sat3Upper n` and `2n≤3k²`. `sat3_min_O_sqrt` adds `k²<4n` for `n≥2`. The numerical `sat_3` is no longer paper-only as an existence statement. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 39 sat3 as a Lean definition

Noncomputable `sat3 n` is `Classical.choose` of `sat3_min`. Specs: `sat3_spec`, `sat3_le_upper`, `sat3_quadratic`, `sat3_sq_lt`. Stale Theorem 9.2 line ("least such k in ordinary mathematics") removed. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 40 numerical Theorem 1.1

`sat3_succ_le`: `sat3 (n+1) ≤ sat3 n + 1`. `sat3_theta_num` is Theorem 1.1 for the numerical function. Exact values `sat3_eq_one`..`five` and `sat3_eq_sixteen`. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 41 numerical exact 13-15

`sat3_eq_thirteen`..`fifteen` pin `sat3 13=sat3 14=sat3 15=4`. `sat3_le_interp` is Corollary 9.5 for the numerical function; `sat3_le_seventeen_num` is `sat3 17 ≤ 5`. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 42 table minimality recheck

`verify_table.py` now also exhausts sizes `pair_lb .. sat-1` (`no_maximal_below`) for every `n≤40`. All 40 rows pass: the stored example is maximal of the claimed size, and no smaller maximal set exists. This is still computational, not Lean. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 43 boolean checker complete

`maximal_complete` is the converse of `maximal_sound`. `maximal_iff`: the boolean checker on a list is equivalent to `MaximalAP3Free` of `ofIntList`. Table certificates are now a decision procedure, not a one-way lift. lake build green (18 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 44 Lean exact n=6..12

`anyMaximal3 n` enumerates all ordered triples in `[n]` and asks the boolean checker. Native-decide `false` for `n=6..12`. Combined with `pairBound 2 = 5` (no 2-point maximal set) and the size-4 construction, `sat3_eq_six`..`sat3_eq_twelve`. Lean exactness now covers every `n≤16`. lake build green (19 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 45 Lean exact n=17

`anyMaximal4_17`: no 4-point maximal set in `[17]` (native_decide on ordered 4-tuples). Interpolation gives `sat3 17 ≤ 5`, so `sat3_eq_seventeen`. Lean exactness now covers every `n≤17`. lake build green (20 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 46 Lean exact n=18

Increasing-tuple enumerator `incK` / `anyMaximalInc` (combinations, not n^k). Native-decide: no maximal 4-set or 5-set in `[18]`. Size-6 witness from the table. `sat3_eq_eighteen`. Lean exactness now covers every `n≤18`. lake build green (22 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 47 Lean exact n=19,20

Same increasing-tuple argument as n=18: no maximal 4-set or 5-set (`anyMaximal4inc_19`, `_20`, `anyMaximal5inc_19`, `_20`), size-6 witnesses. `sat3_eq_nineteen`, `sat3_eq_twenty`. Lean exactness now covers every `n≤20`. lake build green (22 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 48 Lean exact n=21..26

Size-6 plateau. For n=21,22: no maximal 4-set or 5-set (`anyMaximalInc`). For n=23..26: `pairBound 4 = 22` kills size 4, and no maximal 5-set. Size-6 witnesses from the table. `sat3_eq_twentyone`..`sat3_eq_twentysix`. Lean exactness now covers every `n≤26`. lake build green (22 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 49 Lean exact n=27..32

3-AP-free enumerator `freeFrom` / `anyMaximalFree` (prefix prune by midpoints). Native-decide: no maximal 5-set or 6-set in `[27]`..`[32]`. Size-7 witnesses from the table. `sat3_eq_twentyseven`..`sat3_eq_thirtytwo`. Lean exactness now covers every `n≤32`. lake build green (23 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 50 Lean exact n=33

Recursive DFS `existsMax` / `anyMaximalSearch` (no giant free-set list). Native-decide: no maximal 5-, 6-, or 7-set in `[33]`. Size-8 witness from the table. `sat3_eq_thirtythree`. Python confirms the same for n=34..40, but Lean native_decide of those seven-set searches together exceeded a 10-minute budget, so they stay computational. Lean exactness now covers every `n≤33`. lake build green (24 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 51 Lean exact n=34..40

Split the remaining seven-set searches into one module per n (`Sat3/N34.lean`..`N40.lean`). Native-decide: no maximal 5/6/7-set at n=34,35; `pairBound 5 = 35` kills size 5 for n=36..40, and no maximal 6- or 7-set. Size-8 witnesses. `sat3_eq_thirtyfour`..`sat3_eq_forty`. Lean exactness now covers every `n≤40`. lake build green (31 jobs), no sorry. Main claim unchanged: `sat_3(n)<2√n`.

## 2026-09-07, cycle 52 table honesty and n=41..46

Stale Theorem 9.2 line (`sat3_eq_one`..`five` and `sixteen`) replaced by `sat3_eq_one`..`forty`. Hostile review residual updated: table n≤40 is Lean. README matches. Computational continuation: `sat_3(n)=8` for n=41..46 (exhaustive backtrack, witnesses in `data/sat3_values_ext.json`). n=47,48 not finished. Not Lean. Main claim unchanged: `sat_3(n)<2√n`.
