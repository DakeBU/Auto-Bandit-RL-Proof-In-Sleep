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

Asymptotic continuation: choose an actual code for each positive block size
n+1 using the finite-n theorem, then apply squeeze_zero/addition using
tendsto_one_div_add_atTop_nhds_zero_nat. The family is existential proof data,
not claimed to be an executable arithmetic coder. For any other convergent
prefix-code rate family, pass the universal entropy lower bound to the limit
with le_of_tendsto. This closes asymptotic block achievability and converse
while leaving the specifically named algorithms as separate requirements.

The asymptotic achievability and converse focused-build (2,674 jobs).
`exists_sourceBlock_code_family_tendsto_entropy` selects actual positive-block
prefix codes and proves convergence using the 1/(n+1) squeeze.
`sourceBlock_code_family_limit_ge_entropy` handles every convergent family;
the earlier pointwise lower bound remains available without convergence.
Both allow zero source masses. The proof uses `ge_of_tendsto` for the lower
bound direction. The arithmetic-coding algorithm is still not constructed.

The focused typed canary passed; all eight reported axiom sets are standard
propext/Classical.choice/Quot.sound only. BlockEntropy and its root-import
canary are now registered for aggregate verification. The ongoing 2ce1976
check predates this module and must not be cited as its integration evidence.

Full integration at d256f27 passed: root/Tests (8,917 jobs), exporter and
placeholder checks, 400 Python tests (7 skipped, 208.383s). Log:
C:/a14/tmp/ch14-block-coding-full-check.log. Thus the finite and asymptotic
block-code results are integrated; the separately named arithmetic coder
and Huffman algorithm are not established by this gate.
