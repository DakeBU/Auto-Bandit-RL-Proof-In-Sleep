# Chapter 14 block source coding route

Source TXT-LATTIMORE-SZEPESVARI-2020, author p. 187: the average number of
bits per symbol tends to entropy and is unimprovable. Independent block
distributions need an explicit entropy tensorization bridge before applying
the compiled finite-code sandwich to an n-symbol alphabet.

First prove the zero-safe scalar entropy product identity, then finite
product entropy additivity with normalized marginals. APIs: Real.log_inv,
Real.log_mul, Fintype.sum_prod_type, Finset.sum_mul and mul_sum. Zero factors
are split explicitly. Cards MLIB-REAL-LOG-SQRT, MLIB-FINSET-SUMS,
MLIB-PROBABILITY-INDEPENDENCE. These are Mathlib-candidate arithmetic leaves.
Next: iterate products, apply actual prefix-code existence, divide by n,
and squeeze rates between H2 and H2+1/n. This proves a block-code theorem;
the specifically named arithmetic-coding algorithm and Huffman optimality
remain separate source obligations, not consequences of this route alone.

The module now includes a nested-product n-symbol type, its IID mass,
nonnegativity and normalization, and exact n-fold entropy. The finite-block
terminals expose a realizable code rate between H2 and H2+1/n and the H2
lower bound for every block prefix code. Zero masses are allowed throughout.
The limit/choice-of-code-family argument and specifically arithmetic coding
remain separate from these finite-n statements. The ongoing full check at
2ce1976 does not cover this new module.

Focused build passed (2,674 jobs), as did the full typed finite-n canary and
the three-symbol entropy instance. All six axiom reports contain only
propext, Classical.choice, and Quot.sound. No new own-module warnings remain.
