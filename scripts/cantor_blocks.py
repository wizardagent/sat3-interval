#!/usr/bin/env python3
"""Cantor (base-3 digits in {0,1}) centres for S-blocks.

B = { integers whose ternary digits lie in {0,1} }  (A003278, including 0)
centres c = 6 + 11 b,  b in B
A(n) = union of S(c) intersect [n], over those c with c <= n
     where S(c) = {c, c+1, c+4, c+5}.
"""
from __future__ import annotations


def is_free(A):
    S = set(A)
    L = sorted(S)
    for i, a in enumerate(L):
        for b in L[i + 1 :]:
            if 2 * b - a in S:
                return False
    return True


def S(c):
    return (c, c + 1, c + 4, c + 5)


def cantor_gen(limit):
    """Yield b in B, b <= limit."""
    k = 0
    while True:
        s = 0
        p = 1
        t = k
        while t:
            s += (t & 1) * p
            t >>= 1
            p *= 3
        if s > limit:
            return
        yield s
        k += 1


def build(n, offset=6, scale=11):
    cs = []
    A = []
    for b in cantor_gen(max(0, (n - offset) // scale + 2)):
        c = offset + scale * b
        if c > n:
            break
        cs.append(c)
        for x in S(c):
            if 1 <= x <= n:
                A.append(x)
    A = sorted(set(A))
    return cs, A


def cover_bitset(A, n):
    """Return missing points in [1,n] using a bytearray."""
    hit = bytearray(n + 2)
    for x in A:
        if 1 <= x <= n:
            hit[x] = 1
    L = A
    m = len(L)
    for i in range(m):
        a = L[i]
        for j in range(i + 1, m):
            b = L[j]
            for t in (2 * b - a, 2 * a - b):
                if 1 <= t <= n:
                    hit[t] = 1
            s = a + b
            if s % 2 == 0:
                t = s // 2
                if 1 <= t <= n:
                    hit[t] = 1
    miss = [i for i in range(1, n + 1) if not hit[i]]
    return miss


def check(n):
    cs, A = build(n)
    miss = cover_bitset(A, n)
    return {
        "n": n,
        "k": len(A),
        "ncentres": len(cs),
        "free": is_free(A),
        "nmiss": len(miss),
        "miss": miss[:8],
        "last_c": cs[-1] if cs else None,
    }


def check_generation(k: int):
    """A_k = union S(6+11b) for b in B cap [0, 3^k). Covers [1, 11*3^k+5]?"""
    cs = []
    A = []
    for b in cantor_gen(3**k - 1):
        c = 6 + 11 * b
        cs.append(c)
        A.extend(S(c))
    A = sorted(set(A))
    L = 11 * (3**k) + 5
    Aclip = [x for x in A if 1 <= x <= L]
    miss = cover_bitset(Aclip, L)
    return {
        "k": k,
        "L": L,
        "nA": len(A),
        "free": is_free(A),
        "nmiss": len(miss),
        "miss": miss[:8],
    }


if __name__ == "__main__":
    print("generation covering [1, 11*3^k + 5]")
    for k in range(0, 8):
        r = check_generation(k)
        print(f"k={r['k']} L={r['L']:6d} |A|={r['nA']:4d} free={r['free']} miss={r['nmiss']}")
        assert r["free"] and r["nmiss"] == 0
    print("generations 0..7 OK")
    print()
    print(f"{'n':>6} {'k':>4} {'c':>3} {'free':>5} {'miss':>5} sample")
    ns = list(range(1, 81))
    ns += [100, 128, 150, 200, 256, 300, 400, 512, 729, 800, 999, 1000, 1024, 2000, 2187, 3000]
    fails = []
    for n in ns:
        r = check(n)
        flag = "" if r["nmiss"] == 0 and r["free"] else " FAIL"
        if n <= 80 or r["nmiss"] or n in (100, 128, 256, 512, 1000, 2000, 2187, 3000):
            print(f"{n:6d} {r['k']:4d} {r['ncentres']:3d} {str(r['free']):>5} {r['nmiss']:5d} {r['miss']}{flag}")
        if r["nmiss"] or not r["free"]:
            fails.append(r)
    print("n_checked", len(ns), "fails", len(fails))
    if fails:
        print("fail n", [f["n"] for f in fails])

    # Repair: adjoin c+3 when n in {c+3,c+4} for last centre c.
    print("\nrepair check n=11..500")
    repair_fail = []
    n_repair = 0
    for n in range(11, 501):
        cs, A = build(n)
        miss = cover_bitset(A, n)
        if not miss:
            continue
        c = cs[-1]
        assert miss == [c + 3], (n, miss, c)
        assert n in (c + 3, c + 4), (n, c)
        A2 = sorted(set(A + [c + 3]))
        if (not is_free(A2)) or cover_bitset(A2, n):
            repair_fail.append(n)
        n_repair += 1
    print("n_repair", n_repair, "repair_fail", repair_fail)

    # Predecessor cover: A^{<c} covers [1,c-1] for centres up to 6+11*3^4.
    print("\npredecessor cover")
    pred_fail = []
    Bs = list(cantor_gen(3**4))
    for i, b in enumerate(Bs):
        if b == 0:
            continue
        c = 6 + 11 * b
        A = []
        for bp in Bs[:i]:
            A.extend(S(6 + 11 * bp))
        A = sorted(set(A))
        miss = cover_bitset(A, c - 1)
        if miss:
            pred_fail.append((b, c, miss[:6]))
    print("pred_fail", pred_fail)

    # Base-4 centres: B^{(4)} sums of distinct powers of 4.
    print("\nbase-4 covering [1, M_k] with M_k = 2*max(A)-min(A)")
    for k in range(0, 8):
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
        A = sorted(set(A))
        Mk = 2 * max(A) - min(A)
        miss = cover_bitset(A, Mk)
        print(f"k={k} M={Mk:6d} |A|={len(A):4d} free={is_free(A)} miss={len(miss)}")
        assert is_free(A) and not miss
    print("base-4 generations 0..7 OK")

    print("\nbase-4 offset D'=11*(4^k-1): U_k free and covers [1, m_{k+1}]")
    for k in range(1, 6):
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
        A = sorted(set(A))
        Dp = 11 * (4**k - 1)
        U = sorted(set(A + [x + Dp for x in A]))
        mk1 = 11 * (4 ** (k + 1) + 2) // 3
        miss = cover_bitset([x for x in U if 1 <= x <= mk1], mk1)
        print(f"k={k} |U|={len(U):4d} maxU={max(U):6d} m={mk1:6d} free={is_free(U)} miss={len(miss)}")
        assert is_free(U) and not miss
        assert max(U) == mk1 - 11
    print("offset U_k for k=1..5 OK")
