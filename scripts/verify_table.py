#!/usr/bin/env python3
"""Verify every example in data/sat3_values.json is maximal 3-AP-free of the claimed size."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from sat3_cert import is_maximal, no_maximal_below, pair_lb  # noqa: E402
from rcomplete import k_for, place  # noqa: E402


def window_k(n: int) -> int:
    if n <= 1:
        return 0
    return k_for(n)


def main() -> None:
    path = ROOT / "data" / "sat3_values.json"
    data = json.loads(path.read_text())
    rows = data["sat3"]
    assert len(rows) == 40
    ext_path = ROOT / "data" / "sat3_values_ext.json"
    if ext_path.exists():
        extra = json.loads(ext_path.read_text())["sat3"]
        assert [r["n"] for r in extra] == list(range(41, 41 + len(extra)))
        rows = rows + extra
    for row in rows:
        n = row["n"]
        A = row["example"]
        sat = row["sat"]
        assert len(A) == sat, (n, A, sat)
        assert is_maximal(A, n), (n, A)
        assert row["pair_lb"] == pair_lb(n)
        assert sat >= row["pair_lb"]
        k = window_k(n)
        twop = 1 if n == 1 else 2 ** k
        assert sat <= twop, (n, sat, twop)
        _, _, _, B = place(n)
        assert len(B) == twop, (n, len(B), twop)
        assert is_maximal(B, n), (n, B)
        assert no_maximal_below(n, sat), (n, sat)
        print(f"ok n={n} sat={sat} 2^k={twop} A={A} min")
    nmax = rows[-1]["n"]
    print(f"all {len(rows)} examples n=1..{nmax} verified; construction maximal of size 2^k; no smaller maximal set")


if __name__ == "__main__":
    main()
