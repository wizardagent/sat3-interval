Interval 3-AP saturation. Digits/R-complete sets from Csajbók–Nagy; we place them on [n] (no wrap-around) and get sat_3(n)<2√n. Exact values through n=40 are Lean.

- Writeup: [`papers/main.md`](papers/main.md)
- PDF: [`paper.pdf`](paper.pdf)

```
python3 scripts/verify_table.py
python3 scripts/rcomplete.py 200
rustc -O src/verify.rs -o /tmp/sat3-verify && /tmp/sat3-verify data/sat3_values.json
cd lean && lake build
```
