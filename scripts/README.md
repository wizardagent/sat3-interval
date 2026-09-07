`sat3_cert.py n` recomputes `sat_3(1..n)` by backtracking and writes `data/sat3_values.json`.

`verify_table.py` checks every stored example is maximal 3-AP-free of the claimed size, and that no smaller 3-AP-free set is maximal (`no_maximal_below`).

`cantor_blocks.py` checks ternary Cantor covering of `[1, 11*3^k+5]`, the truncated repair at n=c+3,c+4, and base-4 covering of `[1, M_k]` for k=0..7.

`rcomplete.py n` builds an R-complete set of size 2^k in [1..n] and checks freeness plus endpoint covering.

For n=40 the enumerator takes about a minute. The committed JSON is the certificate; re-running is optional.
