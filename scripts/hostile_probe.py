#!/usr/bin/env python3
"""Hostile probes for Lemmas 6.5, 6.11/Thm 6.12, Thm 8.5 / Cor 8.6."""
from __future__ import annotations
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cantor_blocks import (
    S, is_free, cover_bitset, build, cantor_gen, check, check_generation
)


def endpoint_completions(A):
    """Only endpoint thirds 2y-x, 2a-b (no midpoints)."""
    hit = set(A)
    L = sorted(A)
    for i, a in enumerate(L):
        for b in L[i + 1 :]:
            hit.add(2 * b - a)
            hit.add(2 * a - b)
    return hit


def endpoint_covers(A, lo, hi):
    hit = endpoint_completions(A)
    miss = [t for t in range(lo, hi + 1) if t not in hit]
    return miss


def probe_lemma65():
    """Reconstruct mixed_fills_right; weaken hypotheses for counterexamples."""
    print("=" * 70)
    print("LEMMA 6.5 (mixed_fills_right) PROBES")
    print("=" * 70)

    # Base case used in paper: A = S(6) = {6,7,10,11}, d=11, covers [1,16]
    A0 = list(S(6))
    d = 11
    assert max(A0) <= d + 5 and min(A0) >= 1
    miss0 = endpoint_covers(A0, 1, d + 5)
    print(f"base A=S(6)={A0} d={d}: endpoint-cover [1,{d+5}] miss={miss0}")
    assert not miss0

    A1 = sorted(set(A0 + [x + d for x in A0]))
    miss1 = endpoint_covers(A1, 1, 3 * d + 5)
    print(f"A∪(A+d)={A1}: endpoint-cover [1,{3*d+5}] miss={miss1}")
    assert not miss1 and is_free(A1)
    print("PASS: paper instance d=11 works")

    # Several inductive steps
    for k in range(0, 6):
        d = 11 * (3**k)
        A = []
        for b in cantor_gen(3**k - 1):
            A.extend(S(6 + 11 * b))
        A = sorted(set(A))
        missL = endpoint_covers(A, 1, d + 5)
        Ad = sorted(set(A + [x + d for x in A]))
        missR = endpoint_covers(Ad, 1, 3 * d + 5)
        print(f"k={k} d={d} |A|={len(A)} left_miss={len(missL)} right_miss={len(missR)} free={is_free(Ad)}")
        assert not missL and not missR and is_free(Ad)
    print("PASS: inductive instances k=0..5")

    # Weaken: drop support A ⊆ [1,d+5]
    print("\n--- weaken support: allow points outside [1,d+5] ---")
    # A covers [1,d+5] via endpoints but has a far point
    # Take A = S(6) ∪ {100} — does it endpoint-cover [1,16]? Extra point may help/hurt freeness
    for extra in [0, 17, 18, -1, 20]:
        A = sorted(set(list(S(6)) + ([extra] if extra not in S(6) else [])))
        d = 11
        miss = endpoint_covers(A, 1, d + 5)
        Ad = sorted(set(A + [x + d for x in A]))
        missR = endpoint_covers(Ad, 1, 3 * d + 5)
        # check distinctness failure: any mixed triple with collision?
        print(f"  A={A} cover_left_miss={miss} cover_right_miss={missR[:10]} nmissR={len(missR)} free={is_free(Ad)}")

    # Weaken: allow d<=0
    print("\n--- weaken d>0: d=0 ---")
    A = list(S(6))
    Ad = A  # A ∪ (A+0)
    miss = endpoint_covers(Ad, 1, 5)  # 3*0+5=5
    print(f"  d=0 trivial: miss[1,5]={miss} (lemma requires d>0)")

    # Weaken: A covers with MIDPOINTS but not endpoints only
    print("\n--- weaken to full maximality (incl midpoints) vs endpoint-only ---")
    # Construct a set that is maximal via midpoints but does NOT endpoint-cover
    # e.g. {1,2,4} in small interval?
    for cand in [[1, 2, 4, 5], [1, 3, 4], [2, 3, 5, 6], [1, 2, 5, 6]]:
        for dtry in [5, 6, 7, 8, 9, 10, 11]:
            if max(cand) > dtry + 5:
                continue
            if min(cand) < 1:
                continue
            em = endpoint_covers(cand, 1, dtry + 5)
            full = cover_bitset(cand, dtry + 5)
            if em and not full:
                Ad = sorted(set(cand + [x + dtry for x in cand]))
                missR = endpoint_covers(Ad, 1, 3 * dtry + 5)
                fullR = cover_bitset(Ad, 3 * dtry + 5)
                print(f"  cand={cand} d={dtry}: end_left_miss={em} full_left_miss={full}")
                print(f"    after union: end_right_miss={missR[:8]} (n={len(missR)}) full_right_miss={fullR[:8]}")

    # Critical: does the proof need u>=6? Paper uses u in [6,d+5]
    # What if we claim covers [1,3d+5] but right piece starts earlier?
    print("\n--- check right-piece boundary: need u>=6 for distinctness? ---")
    # Suppose A endpoint-covers [1,d+5] and we try to cover t=2d+5 (u=5) via mixed
    # Paper only claims from 2d+6. Is 2d+5 already covered by middle?
    # Middle is [d+1, 2d+5] via A+d. So 2d+5 is in middle. Good.
    # What about if support lower bound dropped so A can have points <1?
    A_bad = [0, 1, 4, 5]  # S(0), not in [1,d+5] for d=11 fully? 0 not in [1,16]
    d = 11
    # Does S(0) endpoint-cover [1,16]? From paper, completions of S(0) fill [-5,10], so [1,10] yes, [11,16] NO
    miss = endpoint_covers(A_bad, 1, d + 5)
    print(f"  S(0) on [1,{d+5}] miss={miss} (expected holes near right)")

    # Counterexample attempt: A covers [1,d+5] but violates support (point > d+5)
    # Can we cover [1,d+5] with a point outside?
    print("\n--- search small counterexample: cover [1,d+5] with support violating ---")
    found_cex = []
    for d in range(3, 20):
        # brute small free sets that endpoint-cover [1,d+5]
        # Allow points in [1-5, d+5+5] = expanded support
        lo_s, hi_s = 1 - 3, d + 5 + 3
        # too big to brute; instead take known cover and move a point
        # Use S(6) translated? 
        # Try A = list of S(a) clipped/padded
        for a in range(1, d + 2):
            A = [x for x in S(a) if 1 - 5 <= x <= d + 10]
            A = sorted(set(A))
            if not A:
                continue
            if not all(1 <= x <= d + 5 for x in A):
                # support violated
                if endpoint_covers(A, 1, d + 5):
                    Ad = sorted(set(A + [x + d for x in A]))
                    missR = endpoint_covers(Ad, 1, 3 * d + 5)
                    if missR:
                        found_cex.append((d, A, missR[:6]))
                        print(f"  CEX? d={d} A={A} right_miss={missR[:6]}")
    if not found_cex:
        print("  no easy support-violating S(a) counterexample found for d=3..19")

    # Drop the u≠x parent condition / try A that covers via midpoints only on left piece needing endpoint for right
    print("\n--- numerical stress: random maximal-ish sets with support ---")
    import itertools
    stress_fail = []
    for d in [5, 6, 7, 8, 9, 10, 11, 12, 15]:
        hi = d + 5
        # all 3-AP-free subsets of [1,hi] of size <=6 that endpoint-cover
        univ = list(range(1, hi + 1))
        for ksz in range(2, min(7, hi + 1)):
            for comb in itertools.combinations(univ, ksz):
                A = list(comb)
                if not is_free(A):
                    continue
                if endpoint_covers(A, 1, hi):
                    Ad = sorted(set(A + [x + d for x in A]))
                    missR = endpoint_covers(Ad, 1, 3 * d + 5)
                    if missR:
                        stress_fail.append((d, A, missR[:5]))
            if stress_fail:
                break
        # also report how many covering sets found
    print(f"  stress counterexamples under stated hyps: {stress_fail[:5]} (total {len(stress_fail)})")
    if stress_fail:
        print("  FAIL: lemma false under claimed hypotheses!")
    else:
        print("  PASS: no counterexample among free covering subsets size<=6 for d in {5..15}")

    # One more weaken: remove freeness of A (lemma doesn't assume freeness!)
    print("\n--- note: Lemma 6.5 does NOT assume A is 3-AP-free ---")
    for d in [5, 8, 11]:
        hi = d + 5
        # {1,2,3} has APs but may cover
        for A in [[1, 2, 3, hi], [1, 2, 3, 4, 5], list(range(1, hi + 1))]:
            A = [x for x in A if 1 <= x <= hi]
            if not endpoint_covers(A, 1, hi):
                continue
            Ad = sorted(set(A + [x + d for x in A]))
            missR = endpoint_covers(Ad, 1, 3 * d + 5)
            print(f"  d={d} A={A} (free={is_free(A)}) right_miss={len(missR)}")
            if missR:
                print(f"    CEX without freeness: miss={missR[:8]}")
                break


def probe_611_612():
    print("\n" + "=" * 70)
    print("LEMMA 6.11 / THEOREM 6.12 PROBES")
    print("=" * 70)

    # Extended repair check
    N = 2000
    repair_fail = []
    free_fail = []
    max_fail = []
    n_repair = 0
    n_ok_plain = 0
    pattern_fail = []

    for n in range(1, N + 1):
        cs, A = build(n)
        if not cs:
            # n < 6 maybe
            miss = cover_bitset(A, n) if A else list(range(1, n + 1))
            if n <= 10:
                continue  # Thm 6.12 uses table for n<=10
            continue
        c = cs[-1]
        miss = cover_bitset(A, n)
        free = is_free(A)
        if not free:
            free_fail.append(n)

        if n in (c + 3, c + 4):
            # claim: unique hole is c+3
            if miss != [c + 3]:
                pattern_fail.append((n, c, miss))
            else:
                A2 = sorted(set(A + [c + 3]))
                if not is_free(A2):
                    repair_fail.append(("free", n, c))
                m2 = cover_bitset(A2, n)
                if m2:
                    repair_fail.append(("max", n, c, m2))
                n_repair += 1
        else:
            # claim: A itself maximal (for n>=11)
            if n >= 11:
                if miss:
                    # Should not happen per Lemma 6.11 case 2
                    max_fail.append((n, c, miss[:8]))
                else:
                    n_ok_plain += 1

    print(f"n=1..{N}: plain_ok={n_ok_plain} repair_used={n_repair}")
    print(f"free_fail={free_fail[:20]} (n={len(free_fail)})")
    print(f"pattern_fail (expected miss=[c+3]) count={len(pattern_fail)} sample={pattern_fail[:5]}")
    print(f"repair_fail count={len(repair_fail)} sample={repair_fail[:5]}")
    print(f"max_fail (claimed maximal but holes) count={len(max_fail)} sample={max_fail[:10]}")

    # Also check claimed size bound
    size_ok = True
    for n in [11, 16, 17, 20, 21, 32, 42, 43, 53, 54, 100, 200, 500, 999, 1000, 2000]:
        cs, A = build(n)
        c = cs[-1]
        k = len(A)
        if n in (c + 3, c + 4):
            k += 1
        bound = 4 * len(cs) + 1
        print(f"  n={n:4d} c={c:4d} |A_circ|={len(A):3d} claimed_size<={k} bound={bound} centres={len(cs)}")
        if k > bound:
            size_ok = False
            print("    SIZE BOUND FAIL")
    print("size bound OK" if size_ok else "SIZE BOUND FAIL")

    # generations
    print("\ngeneration covering (Thm 6.6):")
    for k in range(0, 8):
        r = check_generation(k)
        status = "PASS" if r["free"] and r["nmiss"] == 0 else "FAIL"
        print(f"  k={k} L={r['L']} |A|={r['nA']} free={r['free']} miss={r['nmiss']} {status}")

    return {
        "free_fail": free_fail,
        "pattern_fail": pattern_fail,
        "repair_fail": repair_fail,
        "max_fail": max_fail,
    }


def base4_set(k):
    A = []
    for mask in range(2**k):
        s = 0
        p = 1
        t = mask
        for _ in range(k):
            s += (t & 1) * p
            t >>= 1
            p *= 4
        A.extend(S(6 + 11 * s))
    return sorted(set(A))


def probe_85_86():
    print("\n" + "=" * 70)
    print("THEOREM 8.5 / COROLLARY 8.6 PROBES")
    print("=" * 70)

    results = []
    for k in range(0, 8):
        A = base4_set(k)
        mk = max(A)
        Mk = 2 * max(A) - min(A)
        # formula check
        Mk_formula = (22 * (4**k) + 26) // 3
        mk_formula = 11 * (4**k + 2) // 3
        miss = cover_bitset(A, Mk)
        free = is_free(A)
        # Cor 8.6: for n in [mk, Mk], A maximal in [n]
        cor_fail = []
        # sample n in interval
        sample_ns = sorted(set([mk, mk + 1, (mk + Mk) // 2, Mk - 1, Mk] + list(range(mk, min(mk + 20, Mk + 1))) + list(range(max(mk, Mk - 20), Mk + 1))))
        for n in sample_ns:
            if n < mk or n > Mk:
                continue
            m = cover_bitset(A, n)
            if m or not free:
                cor_fail.append((n, m[:5] if m else "notfree"))
        status = "PASS" if free and not miss and Mk == Mk_formula and mk == mk_formula and not cor_fail else "FAIL"
        print(f"k={k} |A|={len(A):4d} m={mk:6d} M={Mk:6d} (form M={Mk_formula}) free={free} miss={len(miss)} cor_fail={len(cor_fail)} {status}")
        results.append(status)
        if miss:
            print(f"  first misses: {miss[:10]}")
        if cor_fail:
            print(f"  cor fails: {cor_fail[:5]}")

    # Gap (M_k, m_{k+1})
    print("\n--- gap (M_k, m_{k+1}) ---")
    for k in range(0, 6):
        A = base4_set(k)
        Mk = 2 * max(A) - min(A)
        mk1 = 11 * (4 ** (k + 1) + 2) // 3
        gap_lo, gap_hi = Mk + 1, mk1 - 1
        gap_len = gap_hi - gap_lo + 1
        print(f"k={k}: M={Mk}, m_{{k+1}}={mk1}, gap=({gap_lo},{gap_hi}) len={gap_len}")

        # Truncation of A_{k+1} at n just above M_k
        A1 = base4_set(k + 1)
        for n in [Mk + 1, Mk + 2, Mk + 10, (Mk + mk1) // 2, mk1 - 1]:
            if n < 1:
                continue
            Aclip = [x for x in A1 if 1 <= x <= n]
            miss = cover_bitset(Aclip, n)
            print(f"  trunc A_{{k+1}} at n={n}: |A|={len(Aclip)} miss={len(miss)} free={is_free(Aclip)}")

        # Does A_k cover past M_k?
        miss_past = cover_bitset(A, min(Mk + 50, mk1))
        past = [t for t in miss_past if t > Mk]
        print(f"  A_k holes in (M, M+50∩m]: {past[:15]} (n={len(past)})")

        # One extra S-block: try to extend covered run
        best_ext = 0
        best_c = None
        for c in range(Mk - 20, Mk + 40):
            Aext = sorted(set(A + list(S(c))))
            if not is_free(Aext):
                continue
            # find largest N>=Mk such that covers [1,N]
            # binary search
            lo, hi = Mk, Mk + 100
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if not cover_bitset([x for x in Aext if x <= mid], mid):
                    lo = mid
                else:
                    hi = mid - 1
            if lo > best_ext:
                best_ext = lo
                best_c = c
        print(f"  best single extra S(c): c={best_c} covers up to {best_ext} (delta={best_ext - Mk})")

        # U_k construction
        if k >= 1:
            Dp = 11 * (4**k - 1)
            U = sorted(set(A + [x + Dp for x in A]))
            minR = min(x for x in U if x > max(A))
            print(f"  U_k: |U|={len(U)} minR={minR} vs M+1={Mk+1} (right absent from [M+1] if minR>M+1: {minR > Mk+1})")
            # cover of I(U)
            IU_hi = 2 * max(U) - min(U)
            missU = cover_bitset(U, IU_hi)
            print(f"  U covers I(U)=[?,{IU_hi}]? miss={len(missU)} free={is_free(U)}")

    # Greedy fill experiment for gap
    print("\n--- greedy fill from A_k into gap (experimental, not a proof) ---")
    for k in [1, 2, 3]:
        A = base4_set(k)
        Mk = 2 * max(A) - min(A)
        mk1 = 11 * (4 ** (k + 1) + 2) // 3
        # For n = M_k + gap_len//2, start from A_k and greedily add unblocked points
        n = (Mk + mk1) // 2
        Aset = [x for x in A if x <= n]
        # repeatedly add smallest unblocked
        while True:
            miss = cover_bitset(Aset, n)
            if not miss:
                break
            # add first miss if free
            added = False
            for t in miss:
                cand = Aset + [t]
                if is_free(cand):
                    Aset = sorted(cand)
                    added = True
                    break
            if not added:
                # can't add any miss while free — need different point?
                # try any point in miss that keeps free — already did
                break
        miss_final = cover_bitset(Aset, n)
        print(f"k={k} n={n} |A_k|={len(A)} greedy_size={len(Aset)} miss={len(miss_final)} O(sqrt)={len(Aset) <= 20 * (n**0.5)}")

    return results


if __name__ == "__main__":
    probe_lemma65()
    r611 = probe_611_612()
    r85 = probe_85_86()
    print("\n" + "=" * 70)
    print("SUMMARY FLAGS")
    print("=" * 70)
    print("6.11 free_fail", len(r611["free_fail"]))
    print("6.11 pattern_fail", len(r611["pattern_fail"]))
    print("6.11 repair_fail", len(r611["repair_fail"]))
    print("6.11 max_fail", len(r611["max_fail"]))
    print("8.5 statuses", r85)
