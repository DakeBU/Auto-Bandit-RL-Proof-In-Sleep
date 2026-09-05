# Proof Export: Chapter 14 Information-Theory Spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Status: whole-chapter coverage remains `partial`. The original spine below
is supplemented by the current terminal update at the end. Huffman,
common-density, overlap and Gaussian terminals have full local gates;
arithmetic coding is focused-validated with its full gate running. Additional
body assertions and export/site closure remain open in the body-closure audit.

## Lean Declarations

- `LowerBounds.BinaryPrefixCode`
- `LowerBounds.BinaryPrefixCode.uniquelyDecodable_range`
- `LowerBounds.BinaryPrefixCode.kraft_inequality`
- `LowerBounds.discreteEntropy`
- `LowerBounds.discreteEntropyBaseTwo`
- `LowerBounds.discreteEntropyBaseTwo_eq_div_log_two`
- `LowerBounds.discreteEntropy_nonneg`
- `LowerBounds.expectedCodeLength`
- `LowerBounds.expectedCodeLength_nonneg`
- `LowerBounds.relativeEntropy`
- `LowerBounds.absolutelyContinuous_iff_atom_support`
- `LowerBounds.rnDeriv_mul_atom`
- `LowerBounds.rnDeriv_atom_eq_div`
- `LowerBounds.relativeEntropy_eq_top_of_atom_support_mismatch`
- `LowerBounds.relativeEntropy_finite_klFun`
- `LowerBounds.relativeEntropy_finite_sum_log`
- `LowerBounds.relativeEntropy_finite_eq_if`
- `LowerBounds.relativeEntropy_finite_eq_top_iff`
- `LowerBounds.finitePartitionRelativeEntropy`
- `LowerBounds.totalMass_klFun_le_relativeEntropy`
- `LowerBounds.sum_relativeEntropy_restrict_fibers`
- `LowerBounds.relativeEntropy_finite_map_le`
- `LowerBounds.finitePartitionRelativeEntropy_le_relativeEntropy`
- `LowerBounds.relativeEntropy_map_le_finitePartitionRelativeEntropy`
- `LowerBounds.finitePartitionRelativeEntropy_fin_eq`
- `LowerBounds.relativeEntropy_finite_map_eq_if`
- `LowerBounds.exists_binary_map_relativeEntropy_eq_top_of_event`
- `LowerBounds.finitePartitionRelativeEntropy_eq_top_of_not_absolutelyContinuous`
- `LowerBounds.finitePartitionRelativeEntropy_eq_relativeEntropy_of_not_absolutelyContinuous`
- `LowerBounds.relativeEntropy_trim_eq_lintegral_condExp`
- `LowerBounds.relativeEntropy_map_eq_trim_of_absolutelyContinuous`
- `LowerBounds.relativeEntropy_eq_iSup_trim_of_density_measurable`
- `LowerBounds.densityApproximationFiltration`
- `LowerBounds.measurable_density_iSup_approximationFiltration`
- `LowerBounds.relativeEntropy_eq_iSup_densityApproximation_trim`
- `LowerBounds.exists_fin_encoding_of_finite_range`
- `LowerBounds.exists_fin_observation_densityApproximation`
- `LowerBounds.relativeEntropy_trim_mono`
- `LowerBounds.finitePartitionRelativeEntropy_eq_relativeEntropy`
- `LowerBounds.relativeEntropy_of_absolutelyContinuous_of_integrable`
- `LowerBounds.relativeEntropy_of_probability_absolutelyContinuous_of_integrable`
- `LowerBounds.relativeEntropy_eq_top_of_not_absolutelyContinuous`
- `LowerBounds.relativeEntropy_ne_top_iff`
- `LowerBounds.relativeEntropy_eq_zero_iff`
- `LowerBounds.relativeEntropy_trim_le`
- `LowerBounds.bernoulliRelativeEntropy`
- `LowerBounds.bernoulliRelativeEntropy_event_le`
- `LowerBounds.binaryBretagnolleHuber`
- `LowerBounds.bretagnolleHuberScale`
- `LowerBounds.bretagnolleHuber`

## Natural-Language Proof

### Coding and entropy

A `BinaryPrefixCode` assigns each source symbol an injective nonempty bit list,
with no codeword prefixing a distinct codeword. The nonempty condition matters:
a singleton empty codeword is prefix-free but concatenations of repeated source
symbols are not uniquely decodable. Induction on the first message list shows
that equal concatenations have equal leading codewords, after which prefix
freedom identifies the symbols and cancellation supplies the induction step.
Thus the code range is uniquely decodable. Its finite codebook can therefore
be passed to Mathlib's Kraft--McMillan theorem to obtain

```text
sum (word in codebook) (1/2)^word.length <= 1.
```

For finite support, natural entropy and base-two entropy are defined by

```text
H(P)  = sum_x p(x) log(p(x)^(-1)),
H2(P) = sum_x p(x) (log(p(x)^(-1)) / log 2).
```

Factoring the constant through the finite sum gives `H2(P)=H(P)/log 2`.
Each summand is nonnegative when `p(x)` lies in `[0,1]`, including the zero
term under Lean's total logarithm convention. Expected code length is the
finite sum `sum_x p(x) * length(code(x))` and is nonnegative for nonnegative
masses. These are exact definition-level nodes plus the Kraft leaf; they are
not the missing optimal-coding terminals.

### Relative entropy and full data processing

For a finite alphabet with measurable singletons, write `p(x)=P({x})` and
`q(x)=Q({x})` for two probability measures. Finite additivity over singletons
shows that `P << Q` is equivalent to `q(x)=0 -> p(x)=0` for every symbol.
Evaluating `Q.withDensity (dP/dQ)=P` on a singleton gives
`(dP/dQ)(x) q(x)=p(x)`. Thus the density is `p(x)/q(x)` on positive reference
atoms. Every real function on this finite space is integrable, so expansion
of the log-likelihood integral proves Eq. (14.4):

```text
D(P || Q) = ofReal (sum_x p(x) log(p(x)/q(x)))  if support(P) <= support(Q),
D(P || Q) = infinity                          otherwise.
```

Zero source atoms contribute zero. In the second branch an actual atom of
positive source mass and zero reference mass witnesses non-absolute-continuity.
No strict positivity or additional log-integrability premise is imposed.
The finite-measure `klFun` identity is also exposed, separately from the
probability-normalized logarithmic formula.

### Finite-discretisation supremum and Theorem 14.1

For each natural number `n` and measurable map `f : alpha -> Fin n`, the
singleton preimages give a finite measurable partition. Define
`finitePartitionRelativeEntropy P Q` as the supremum of the KL values of
`P.map f` and `Q.map f` over all such observations. Empty cells contribute zero.

The upper bound follows by splitting the RN convex-integrand lower integral
over the fibers of `f` and applying Jensen's total-mass bound on each fiber.
If `P` is not absolutely continuous with respect to `Q`, a measurable Q-null
set of positive P mass gives a binary observation with infinite KL, proving
equality in that branch.

For `P << Q`, the real RN density is integrable even when KL is infinite.
The natural filtration of its finite-valued simple approximants resolves the
density in its limiting sigma-algebra. The upward conditional-expectation
convergence theorem, continuity of `klFun`, and Fatou recover original KL as
the supremum of the trimmed KL values. Each finite stage's joint approximant
values have finite range; encoding that range into `Fin n` supplies an actual
finite observation whose generated sigma-algebra contains the stage. Trim
monotonicity and the equality between observation KL and comap-trim KL then
bound every recovered stage by the finite-partition supremum. Hence

```text
finitePartitionRelativeEntropy P Q = relativeEntropy P Q.
```

The compiled equality assumes only finite measures on an arbitrary measurable
space, so in particular proves Eq. (14.5) and its RN identification for
probability measures. It does not assume absolute continuity, finite KL, or
countable generation of the ambient sigma-algebra. Combining it with the
existing RN branch adapters retains both singular and nonintegrable infinity.

Define `relativeEntropy P Q` as Mathlib's extended-real `klDiv P Q`. Its
finite branch requires `P << Q` and integrability of the log likelihood ratio;
the singular branch is infinity, and finite-measure KL is zero exactly when
the two measures agree.

For measurable spaces `m <= m0`, let `P` and `Q` be finite measures on `m0`.
If `D(P||Q)=infinity`, monotonicity is immediate. Otherwise finite KL yields
absolute continuity and integrability. The Radon--Nikodym derivative of the
trimmed measures is the conditional expectation, with respect to `m`, of the
original density. Conditional Jensen for the convex KL integrand gives

```text
klFun(E_Q[dP/dQ | m]) <= E_Q[klFun(dP/dQ) | m].
```

Integrating, using equality of integrals of `m`-measurable functions under
`Q` and `Q.trim`, proves the full Exercise 14.10 inequality

```text
D(P.trim m || Q.trim m) <= D(P || Q).
```

No probability normalization or mutual absolute continuity is assumed.

### Bretagnolle--Huber

The separately compiled event specialization sends a measurable event `A` to
the Bernoulli pair `P(A),Q(A)` and proves `d(P(A),Q(A)) <= D(P||Q)`. The binary
proof lower-bounds likelihood affinity by `exp(-d/2)`, compares half its square
with `p+(1-q)`, and handles every endpoint using the exact extended-real
Bernoulli convention. With a real testing scale equal to `exp(-D)/2` for
finite `D` and zero for infinite `D`, antitonicity and event data processing
give the unconditional source theorem

```text
bretagnolleHuberScale (D(P || Q)) <= P(A) + Q(A complement).
```

The KL direction is `P` to `Q`; the complement belongs to `Q`. Adaptive
same-policy history KL is a Chapter 15 consumer, not a Chapter 14 claim.

## Verification boundary

- The root-import canary exercises the coding/entropy, zero-KL, full DPI,
  event-DPI, endpoint, and measure-level testing declarations.
- Imported Mathlib coding, conditional-expectation, and KL APIs are dependencies,
  not new local theorems.
- Whole-chapter status is deliberately retained as `partial` until every body
  row in the frozen completion contract compiles and is canaried.

## Current terminal update

For a finite nonnegative normalized law p, let H2 denote its base-two entropy.
`huffmanOptimalCode` recursively merges two least weights; `huffmanCode_optimal`
proves global prefix-code optimality and `huffmanCode_entropy_sandwich` proves
H2 <= E length <= H2+1. Full local gate: dff13cb. Codewords are nonempty,
including the singleton convention.

`arithmeticBlockCode` is an exact-real classical interval-address code with
a one-bit positive-support/zero-mass escape tag. For blocks of n>0 symbols
on Fin k, `arithmeticBlockCode_rate_sandwich` proves H2 <= E length/n <=
H2+3/n. `arithmeticBlockCode_rate_tendsto_entropy` proves convergence to H2;
`sourceBlock_code_family_limit_ge_entropy` gives the universal prefix-code
converse. Zero masses are allowed. This is not an executable finite-precision
implementation. Arithmetic full gate at 2a31a01 is still pending.

`relativeEntropy_commonDensity_eq_if` gives the common sigma-finite density
formula with exact infinite branches (gate 78846b8).
`bretagnolleHuberScale_le_half_commonDensityAffinity_sq` and
`half_commonDensityAffinity_sq_le_overlap` give the source Jensen/Le Cam
route (gate b8325c2). `klDiv_gaussianReal_same_variance`,
`gaussian_testing_error_lower_bound`, `gaussian_testing_error_three_tenths`
and `gaussian_testing_max_error_three_twentieths` cover common positive
variance and the exact SNR constants (gate 1e8af14).

All names above are in BanditRLProof.LowerBounds. Unresolved source-mapping
items include explicit metric counterexamples and the supporting exposition
claims enumerated in `reviews/2026-09-05-chapter-14-body-closure-audit.md`.
No new unproved concentration or measurability premise is introduced.
