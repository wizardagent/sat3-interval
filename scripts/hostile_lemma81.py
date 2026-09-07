#!/usr/bin/env python3
"""Hostile probe of Lemma 8.1 and Corollary 7.4 (live spine, not Cantor).

Lemma 8.1: if A is S-complete and 2S+1 <= d <= 3S+1, then A u (A+d)
is (S+d)-complete. Bounds d=2S and d=3S+2 should fail on greedy sets.

Corollary 7.4: an R-complete set of size 2^k places into [n] throughout
R+1 <= n <= 3R+1.
"""
from __future__ import annotations

import sys
from itertools import combinations

sys.path.insert(0, "/workspace/mathlab/scripts")
from rcomplete import (  # noqa: E402
    I_bounds,
    digits_for,
    endpoint_miss,
    is_free,
    subset_sums,
)


def is_R_complete(A: list[int], R: int) -> bool:
    if not A:
        return False
    if min(A) < 0 or max(A) > R:
        return False
    if not is_free(A):
        return False
    return endpoint_miss(A, -R, 2 * R) == []


def grow(A: list[int], d: int) -> list[int]:
    return sorted(set(A) | {x + d for x in A})


def main() -> None:
    fails_in: list = []
    ok_at_2S: list = []
    ok_at_hi: list = []
    checked = 0

    for k in range(1, 6):
        lo, hi = I_bounds(k)
        for S in range(lo, hi + 1):
            A = subset_sums(digits_for(S, k))
            assert is_R_complete(A, S), (k, S, A)
            for d in range(2 * S + 1, 3 * S + 2):
                U = grow(A, d)
                checked += 1
                if not is_R_complete(U, S + d):
                    fails_in.append((k, S, d))
            if S > 0:
                d = 2 * S
                if is_R_complete(grow(A, d), S + d):
                    ok_at_2S.append((k, S, d))
            d = 3 * S + 2
            if is_R_complete(grow(A, d), S + d):
                ok_at_hi.append((k, S, d))

    exh_checked = 0
    exh_fail: list = []
    for S in range(1, 7):
        pts = list(range(0, S + 1))
        for r in range(2, min(6, S + 2)):
            for comb in combinations(pts, r):
                A = list(comb)
                if not is_R_complete(A, S):
                    continue
                for d in range(2 * S + 1, 3 * S + 2):
                    exh_checked += 1
                    if not is_R_complete(grow(A, d), S + d):
                        exh_fail.append((S, d, A))

    place_fail: list = []
    for k in range(1, 5):
        lo, hi = I_bounds(k)
        for R in range(lo, hi + 1):
            A = subset_sums(digits_for(R, k))
            for n in range(R + 1, 3 * R + 2):
                s = 1 if n <= 2 * R + 1 else n - 2 * R
                P = [x + s for x in A]
                if not all(1 <= x <= n for x in P):
                    place_fail.append((k, R, n, "support"))
                    continue
                if not is_free(P) or endpoint_miss(P, 1, n):
                    place_fail.append((k, R, n, "cover"))

    print(f"admissible steps checked: {checked}")
    print(f"counterexamples under stated hyps: {len(fails_in)}")
    print(f"unexpected OK at d=2S: {len(ok_at_2S)}")
    print(f"unexpected OK at d=3S+2: {len(ok_at_hi)}")
    print(f"exhaustive S-complete S=1..6: checked {exh_checked} fail {len(exh_fail)}")
    print(f"placement failures inside window: {len(place_fail)}")
    if fails_in or ok_at_2S or ok_at_hi or exh_fail or place_fail:
        print("FAIL")
        sys.exit(1)
    print("PASS: Lemma 8.1 and Cor. 7.4 hold on the probed range")
    print("tightness: d=2S and d=3S+2 fail on every greedy set checked")


if __name__ == "__main__":
    main()
