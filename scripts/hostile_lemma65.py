#!/usr/bin/env python3
"""Corrected hostile probe for Lemma 6.5."""
from __future__ import annotations
import itertools
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cantor_blocks import S, is_free, cantor_gen


def endpoint_hit(A):
    hit = set(A)
    L = sorted(A)
    for i, a in enumerate(L):
        for b in L[i+1:]:
            hit.add(2*b - a)
            hit.add(2*a - b)
    return hit


def misses(A, lo, hi):
    hit = endpoint_hit(A)
    return [t for t in range(lo, hi+1) if t not in hit]


def covers(A, lo, hi):
    return len(misses(A, lo, hi)) == 0


print("=== Lemma 6.5 under STATED hypotheses ===")
# Exhaustive: free OR not free, A ⊆ [1,d+5], covers [1,d+5]
hyp_fail = []
cover_count = 0
for d in range(1, 16):
    hi = d + 5
    univ = list(range(1, hi+1))
    for ksz in range(1, min(8, hi+1)):
        for comb in itertools.combinations(univ, ksz):
            A = list(comb)
            if not covers(A, 1, hi):
                continue
            cover_count += 1
            Ad = sorted(set(A + [x+d for x in A]))
            mR = misses(Ad, 1, 3*d+5)
            if mR:
                hyp_fail.append((d, A, mR[:8], is_free(A)))
print(f"covering subsets checked (size<=7, d=1..15): {cover_count}")
print(f"counterexamples under stated hyps: {len(hyp_fail)}")
for row in hyp_fail[:10]:
    print(" ", row)
if hyp_fail:
    print("BUG: Lemma 6.5 FALSE as stated")
else:
    print("PASS: no counterexample under A⊆[1,d+5], d>0, endpoint-covers [1,d+5]")

print("\n=== Without support bound (A may leave [1,d+5]) ===")
# Allow points in expanded range but require covering [1,d+5]
supp_fail = []
for d in range(3, 12):
    hi = d + 5
    univ = list(range(1-5, hi+6))  # expanded
    for ksz in range(1, 6):
        for comb in itertools.combinations(univ, ksz):
            A = list(comb)
            # must violate support
            if all(1 <= x <= hi for x in A):
                continue
            if not covers(A, 1, hi):
                continue
            Ad = sorted(set(A + [x+d for x in A]))
            mR = misses(Ad, 1, 3*d+5)
            if mR:
                supp_fail.append((d, A, mR[:8]))
print(f"support-violating covering counterexamples: {len(supp_fail)}")
for row in supp_fail[:8]:
    print(" ", row)

print("\n=== Distinctness edge cases on paper right-piece argument ===")
# Reconstruct: for each covering A with support, check every t in [2d+6,3d+5]
# whether the constructed parents are distinct
dist_fail = []
for d in [5, 8, 11, 15, 33]:
    # use Cantor A_k when applicable
    if d % 11 == 0:
        k = 0
        while 11 * (3**k) < d:
            k += 1
        if 11 * (3**k) == d:
            A = []
            for b in cantor_gen(3**k - 1):
                A.extend(S(6+11*b))
            A = [x for x in sorted(set(A)) if 1 <= x <= d+5]
        else:
            A = list(S(6))
            if max(A) > d+5:
                continue
    else:
        # find any covering set via S if possible
        A = None
        for a in range(1, d+2):
            cand = [x for x in S(a) if 1 <= x <= d+5]
            if len(cand) >= 2 and covers(cand, 1, d+5):
                A = cand
                break
        if A is None:
            # try denser
            for ksz in range(2, 6):
                found = False
                for comb in itertools.combinations(range(1, d+6), ksz):
                    if covers(list(comb), 1, d+5):
                        A = list(comb)
                        found = True
                        break
                if found:
                    break
        if A is None:
            print(f"d={d}: no covering set found, skip")
            continue
    assert covers(A, 1, d+5), (d, A, misses(A,1,d+5))
    Ad = sorted(set(A + [x+d for x in A]))
    mR = misses(Ad, 1, 3*d+5)
    print(f"d={d} A={A} |A|={len(A)} right_miss={mR} free={is_free(Ad)}")
    # manual distinctness check for right piece
    for t in range(2*d+6, 3*d+5+1):
        u = t - 2*d
        hit = endpoint_hit(A)
        if u in A:
            x, y = u, u+d
            if len({x,y,t}) < 3:
                dist_fail.append(("mem", d, t, x, y))
        else:
            # find parents
            found_p = False
            for x in A:
                for y in A:
                    if x != y and u == 2*y - x:
                        # check distinctness of {x, y+d, t}
                        if len({x, y+d, t}) < 3:
                            dist_fail.append(("comp", d, t, x, y, y+d))
                        found_p = True
            if not found_p and u not in hit:
                dist_fail.append(("uncovered_u", d, t, u))

print(f"distinctness failures: {dist_fail[:10]} (n={len(dist_fail)})")

print("\n=== Does left cover require endpoints only? Midpoint-only maximal sets ===")
# A maximal via midpoints but NOT endpoint-covering — lemma wouldn't apply
from cantor_blocks import cover_bitset
for d in [5, 8, 11]:
    hi = d+5
    for ksz in range(2, 5):
        for comb in itertools.combinations(range(1, hi+1), ksz):
            A = list(comb)
            if not is_free(A):
                continue
            full_miss = cover_bitset(A, hi)
            end_miss = misses(A, 1, hi)
            if not full_miss and end_miss:
                Ad = sorted(set(A + [x+d for x in A]))
                print(f"d={d} A={A} full-maximal but end_miss={end_miss}; after union end_missR={misses(Ad,1,3*d+5)[:6]} full_missR={cover_bitset(Ad,3*d+5)[:6]}")

print("\n=== Paper inductive chain only ===")
for k in range(0, 7):
    d = 11 * (3**k)
    A = []
    for b in cantor_gen(3**k - 1):
        A.extend(S(6 + 11*b))
    A = sorted(set(A))
    assert all(1 <= x <= d+5 for x in A), (k, min(A), max(A), d+5)
    assert covers(A, 1, d+5)
    Ad = sorted(set(A + [x+d for x in A]))
    assert covers(Ad, 1, 3*d+5)
    print(f"k={k} d={d} PASS")
print("All paper instances PASS")
