#!/usr/bin/env python3
"""Reproduce sat_3(n) for n<=40 and dump certificates.

sat_3(n) = min |A| over A subset [n] that are maximal 3-AP-free.

A 3-AP is three distinct integers x<y<z with 2y=x+z.

Maximality: every t in [n]\\A is the third term of a 3-AP whose other two
terms lie in A.
"""
from __future__ import annotations
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def completions(a: int, b: int) -> list[int]:
    """Third points of a 3-AP on {a,b}, a!=b. Unbounded."""
    out = [2 * b - a, 2 * a - b]
    if (a + b) % 2 == 0:
        out.append((a + b) // 2)
    return out


def is_free(A: list[int]) -> bool:
    S = set(A)
    L = A
    for i in range(len(L)):
        a = L[i]
        for j in range(i + 1, len(L)):
            if 2 * L[j] - a in S:
                return False
    return True


def blocked(A: list[int], n: int) -> set[int]:
    B = set(A)
    m = len(A)
    for i in range(m):
        ai = A[i]
        for j in range(i + 1, m):
            for c in completions(ai, A[j]):
                if 1 <= c <= n:
                    B.add(c)
    return B


def is_maximal(A: list[int], n: int) -> bool:
    return is_free(A) and len(blocked(A, n)) == n


def pair_lb(n: int) -> int:
    k = 1
    while (3 * k * k - k) // 2 < n:
        k += 1
    return k


def exists_maximal(n: int, k: int) -> bool:
    """True iff some 3-AP-free k-subset of [n] is maximal."""
    A: list[int] = []

    def rec(start: int) -> bool:
        if len(A) == k:
            return is_maximal(A, n)
        need = k - len(A)
        Aset = set(A)
        last = n + 1 - need
        for x in range(start, last + 1):
            ok = True
            for a in A:
                if (a + x) % 2 == 0 and ((a + x) // 2) in Aset:
                    ok = False
                    break
            if not ok:
                continue
            A.append(x)
            if rec(x + 1):
                A.pop()
                return True
            A.pop()
        return False

    return rec(1)


def no_maximal_below(n: int, sat: int) -> bool:
    """Exhaust k = pair_lb .. sat-1; none of those sizes is maximal."""
    for k in range(pair_lb(n), sat):
        if exists_maximal(n, k):
            return False
    return True


def find_min(n: int, max_examples: int = 8):
    """Increasing-k backtrack. Returns (k, examples)."""
    k0 = pair_lb(n)
    universe = set(range(1, n + 1))
    found: list[list[int]] = []
    A: list[int] = []

    def rec(start: int, k_target: int, stop_after: int) -> bool:
        if len(A) == k_target:
            if is_maximal(A, n):
                found.append(list(A))
                return len(found) >= stop_after
            return False
        need = k_target - len(A)
        Aset = set(A)
        last = n + 1 - need
        for x in range(start, last + 1):
            ok = True
            for a in A:
                if (a + x) % 2 == 0 and ((a + x) // 2) in Aset:
                    ok = False
                    break
            if not ok:
                continue
            A.append(x)
            if rec(x + 1, k_target, stop_after):
                A.pop()
                return True
            A.pop()
        return False

    for k in range(k0, n + 1):
        found.clear()
        rec(1, k, max_examples)
        if found:
            return k, found, k0
    raise RuntimeError("no maximal set")


def count_all(n: int, k: int) -> int:
    A: list[int] = []
    cnt = 0

    def rec(start: int) -> None:
        nonlocal cnt
        if len(A) == k:
            if is_maximal(A, n):
                cnt += 1
            return
        need = k - len(A)
        Aset = set(A)
        last = n + 1 - need
        for x in range(start, last + 1):
            ok = True
            for a in A:
                if (a + x) % 2 == 0 and ((a + x) // 2) in Aset:
                    ok = False
                    break
            if not ok:
                continue
            A.append(x)
            rec(x + 1)
            A.pop()

    rec(1)
    return cnt


def S(a: int) -> tuple[int, int, int, int]:
    return (a, a + 1, a + 4, a + 5)


def two_block_covers(n: int) -> list[int] | None:
    """Search S(a) cup S(b) of size 8 covering [n]."""
    for a in range(1, n):
        for b in range(a + 11, n):
            A = list(S(a) + S(b))
            if max(A) > n:
                continue
            if is_maximal(A, n):
                return A
    # single block
    for a in range(1, n):
        A = list(S(a))
        if max(A) > n:
            continue
        if is_maximal(A, n):
            return A
    return None


def main() -> None:
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    rows = []
    print(f"{'n':>3} {'sat':>4} {'lb':>3} {'nex':>6}  example")
    t0 = time.time()
    for n in range(1, N + 1):
        t1 = time.time()
        k, exs, k0 = find_min(n, max_examples=1)
        if n <= 26:
            nex = count_all(n, k)
        else:
            nex = None
        print(f"{n:3d} {k:4d} {k0:3d} {str(nex):>6}  {exs[0]}  ({time.time()-t1:.2f}s)", flush=True)
        rows.append(
            {
                "n": n,
                "sat": k,
                "pair_lb": k0,
                "n_min_examples": nex,
                "example": exs[0],
            }
        )
    DATA.mkdir(exist_ok=True)
    out = {"sat3": rows, "seconds": time.time() - t0, "N": N}
    (DATA / "sat3_values.json").write_text(json.dumps(out, indent=2) + "\n")
    print("wrote", DATA / "sat3_values.json", "in", time.time() - t0, "s")


if __name__ == "__main__":
    main()
