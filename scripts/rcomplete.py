#!/usr/bin/env python3
"""Binary R-complete sets (Csajbok-Nagy) placed in [n].

For 4^{k-1} < n <= 4^k an R-complete set of size 2^k sits in [n],
hence sat_3(n) <= 2^k < 2 sqrt(n).
"""
from __future__ import annotations

import math
import sys


def I_bounds(k: int) -> tuple[int, int]:
    return (3**k - 1) // 2, (4**k - 1) // 3


def digits_for(R: int, k: int) -> list[int]:
    """Greedy admissible digits of length k summing to R.

    At each step take the largest previous sum in I_{i-1} that still
    leaves an admissible digit. The step is proved in papers/main.md, Corollary 8.3.
    """
    ds: list[int] = []
    S = R
    for i in range(k, 1, -1):
        Ai, Bi = I_bounds(i - 1)
        Sp = min(Bi, (S - 1) // 3)
        d = S - Sp
        if not (Ai <= Sp <= Bi and 2 * Sp + 1 <= d <= 3 * Sp + 1):
            raise ValueError(f"no digits for R={R} k={k} at i={i}")
        ds.append(d)
        S = Sp
    if S != 1:
        raise ValueError(f"no digits for R={R} k={k}")
    ds.append(1)
    ds.reverse()
    return ds


def subset_sums(ds: list[int]) -> list[int]:
    P = {0}
    for d in ds:
        P = P | {x + d for x in P}
    return sorted(P)


def is_free(A: list[int]) -> bool:
    S = set(A)
    L = A
    for i, a in enumerate(L):
        for b in L[i + 1 :]:
            if 2 * b - a in S:
                return False
    return True


def endpoint_miss(A: list[int], lo: int, hi: int) -> list[int]:
    hit = set(A)
    L = A
    for i, a in enumerate(L):
        for b in L[i + 1 :]:
            hit.add(2 * b - a)
            hit.add(2 * a - b)
    return [t for t in range(lo, hi + 1) if t not in hit]


def k_for(n: int) -> int:
    """Lean `windowK n = (n-1).log2 / 2 + 1` for n ≥ 2."""
    if n <= 1:
        return 0
    return ((n - 1).bit_length() - 1) // 2 + 1


def choose_R(n: int, k: int) -> int:
    """Lean `chosenR k n = max(Ilo k, (n+1)/3)`."""
    A, B = I_bounds(k)
    R = max(A, (n + 1) // 3)
    if not (A <= R <= B):
        raise ValueError(f"no R for n={n} k={k}")
    return R


def place_shift(R: int, n: int) -> int:
    """Lean `placeShift R n`."""
    if n <= 2 * R + 1:
        return 1
    return n - 2 * R


def place(n: int) -> tuple[int, int, list[int], list[int]]:
    """Return (k, R, digits, placed set in [n])."""
    if n == 1:
        return 0, 0, [], [1]
    k = k_for(n)
    R = choose_R(n, k)
    ds = digits_for(R, k)
    P = subset_sums(ds)
    s = place_shift(R, n)
    A = [x + s for x in P]
    return k, R, ds, A


def check_n(n: int) -> None:
    k, R, ds, A = place(n)
    if n == 1:
        assert A == [1]
        return
    assert min(A) >= 1 and max(A) <= n, (n, A)
    assert is_free(A), n
    miss = endpoint_miss(A, 1, n)
    assert not miss, (n, miss[:8])
    assert len(A) == 2**k
    assert (2**k) ** 2 < 4 * n


def check_greedy(kmax: int = 6) -> None:
    """Every R in I_k has an admissible greedy predecessor in I_{k-1}."""
    for k in range(2, kmax + 1):
        A, B = I_bounds(k)
        Ap, Bp = I_bounds(k - 1)
        for R in range(A, B + 1):
            S = min(Bp, (R - 1) // 3)
            d = R - S
            assert Ap <= S <= Bp, (k, R, S)
            assert 2 * S + 1 <= d <= 3 * S + 1, (k, R, S, d)
    print(f"greedy predecessors ok k=2..{kmax}")


def check_lean_window(N: int = 400) -> None:
    """`k_for` and `choose_R` match Lean `windowK` / `chosenR`."""
    for n in range(2, N + 1):
        k = k_for(n)
        assert 4 ** (k - 1) < n <= 4 ** k, (n, k)
        A, B = I_bounds(k)
        R = choose_R(n, k)
        assert A <= R <= B, (n, k, R)
        assert R + 1 <= n <= 3 * R + 1, (n, k, R)
        assert R == max(A, (n + 1) // 3)
        s = place_shift(R, n)
        if n <= 2 * R + 1:
            assert s == 1
        else:
            assert s == n - 2 * R
    print(f"lean window ok n=2..{N}")


def main() -> None:
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    check_greedy(6)
    check_lean_window(N)
    for n in range(1, N + 1):
        check_n(n)
        if n <= 40 or n in (64, 65, 81, 256, 257) or n == N:
            k, R, ds, A = place(n)
            print(f"n={n:4d} k={k} R={R:4d} |A|={len(A):4d} 2sqrt={2 * math.sqrt(n):7.3f} A[:8]={A[:8]}")
    print(f"ok n=1..{N}")


if __name__ == "__main__":
    main()
