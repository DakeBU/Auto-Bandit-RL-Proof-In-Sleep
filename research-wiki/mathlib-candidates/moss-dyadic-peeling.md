# MOSS dyadic peeling route

Parent: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`.
Source: Lattimore--Szepesvari Lemma 9.3, author-online pp. 124--125.
Cards: `TXT-LATTIMORE-SZEPESVARI-2020`, `MLIB-EXP-LOG-INEQUALITIES`,
`MLIB-REAL-LOG-SQRT`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`.

Target remains the source probability bound 15*delta/gap^2 for positive
gap and delta in (0,1). The already compiled finite maximal subgaussian
bound supplies each dyadic level; the union ranges over positive sample
counts, with centered independent strongly measurable 1-subgaussian rewards.

## Analytic route refinement

The source bounds its dyadic series by a unimodal integral plus a maximum.
A stronger telescoping bound is available from Mathlib's
`Real.self_le_sinh_iff` at x/3:

`x*exp(-x) <= (3/2)*(exp(-2*x/3)-exp(-4*x/3))`, x>=0.

At x=a*2^j, the exponential differences telescope. Hence
`sum_j 2^j*exp(-a*2^j) <= 3/(2*a)` for a>0. With a=gap^2/4 this
bounds the source series by 12*delta/gap^2, which implies its required
15*delta/gap^2 bound. This is a stronger intermediate estimate, not a
change to the target or its assumptions. The reason for the refinement is
to reuse an existing convex-exponential inequality and avoid a separate
unimodal integral-comparison theorem.

Imports/APIs: `Trigonometric.DerivHyp`, `Real.sinh_eq`, exponential addition,
finite sum induction, nonnegative series order APIs. Search-memory dyadic
found no existing local result. Analytic leaves are mathlib-candidates;
source event peeling and MOSS radius consumers stay project-local.
Status: scalar exponential comparison, finite dyadic sums, and the countable
source-constant series bound compile in `ConcentrationDyadicExponential`.
Probability peeling and normalization to the actual empirical-mean event
compile in `Algorithms/MOSSPeeling.lean`. The source constant is 15;
the intermediate series estimate is 12. The MOSS expected-regret theorem
is still pending: centered arm-stream instantiation, expected optimism
deficit, large-gap occupancy, and concrete history regret assembly remain.

## Source event bridge

Use the source-equivalent scaled event
`S_s + sqrt(4*s*logPlus(1/(s*delta))) + s*gap <= 0`, s>=1.
For 2^j<=s<=2^(j+1), monotonicity of logPlus and nonnegative products
lower-bound the barrier by
`A_j=sqrt(4*2^j*logPlus(1/(2^(j+1)*delta)))+2^j*gap`.
Apply the compiled independent maximal tail to -X through 2^(j+1),
then bound exp(-A_j^2/(4*2^j)) by
`delta*2^(j+1)*exp(-gap^2*2^j/4)`.
Union over j and consume the compiled countable series bound. Natural-log
dyadic coverage uses `Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`.
Finally normalize the scaled event to the actual empirical-mean/radius event.
All mean-zero, independence and subgaussian assumptions stay explicit until
instantiated by the centered arm-stream model. No tail premise is assumed.
