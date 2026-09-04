# Proof Export: Chapter 14 Information-Theory Spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Status: the declarations listed below compile locally. Whole-chapter coverage
remains `partial`: this export does not claim Huffman optimality, the one-bit
entropy sandwich, asymptotic source coding, the finite-discretisation supremum
equivalence, the full common-density/measure-overlap route, or the general-
variance Gaussian testing application.

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
