# MOSS large-gap occupancy route

Source TXT-LATTIMORE-SZEPESVARI-2020, author-online p.126, Theorem 9.1
and Lemma 8.2. Parent TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE.
Project-local first bridge: for delta>0, gap>0 and s*gap^2>=1,
logPlus(1/(s*delta)) <= logPlus(gap^2/delta). Thus the variable-radius
index exceedance is contained in the fixed-log exceedance. Split the finite
indicator count into s*gap^2<1 and the fixed-log count, pointwise, without
assuming a probability or occupancy bound. APIs: existing MOSS.logPlus_mono,
sqrt_le_sqrt, positive denominator multiplication, finite indicator sums.
No new model assumptions; deterministic leaf. Next: bound the small-count
correction by gap^-2; integrate the fixed-log count using independent centered
unit-subgaussian coordinates and the source Lemma 8.2 constants. Actual
pull-count/history connection remains a separate required node.

Compiled progress: `Algorithms/MOSSOccupancy.lean` proves the radius
comparison, pointwise indicator-count split, and exact small-sample count
bound gap^-2. The resulting source correction inequality is
`indexExceedanceCount <= gap^-2 + fixedLogExceedanceCount`.
Focused module build passed 3508 jobs. No expectation bound for the fixed-log
count or actual selected-arm count is yet claimed. API repairs concerned
explicit sum_range_succ unfolding and inequality addition; route unchanged.

Next source target (Lemma 8.2): for epsilon>0 and a>0,
E[sum_{s=1}^n 1{mean_s+sqrt(2a/s)>=epsilon}]
<= 1 + 2/epsilon^2*(a+sqrt(pi*a)+1).
For MOSS substitute epsilon=gap/2 and a=2*logPlus(gap^2/delta).
The large-gap condition gap>=8*sqrt(delta) ensures the logarithm is positive.
The source final arithmetic is gap*E[kappa] <= gap+15/sqrt(delta).
These numerical/count expectation claims are not yet compiled; the current
proof establishes only the deterministic radius/correction reduction.

Analytic next leaf: source substitution z=epsilon*sqrt(t)-sqrt(2a)
reduces the tail integral to integral over z>0 of
(2/epsilon^2)*(z+sqrt(2a))*exp(-z^2/2). Reuse integral_gaussian_Ioi
and port the real analogue of integral_mul_cexp_neg_mul_sq using FTC on Ioi.
Integrability comes from integrable_mul_exp_neg_mul_sq and
integrable_exp_neg_mul_sq, positive variance coefficient. General real
weighted-Gaussian leaf is a mathlib-candidate. The change of variables and
discrete sum comparison remain separate pending obligations.

Compiled in `ConcentrationGaussianOccupancy.lean`: real weighted Gaussian
integral, exact transformed occupancy integral, and antitonicity of
exp(-(epsilon*sqrt(t)-sqrt(2a))^2/2) on [2a/epsilon^2,infinity).
Focused module build passed 3344 jobs. Repairs were explicit Ioi integration
domains and scalar multiplication/division normalization. The original-variable
integral equality, integer sum comparison and probability consumer are pending;
the exact transformed integral alone is not Lemma 8.2.

Change-of-variables route: use inverse map phi(z)=((z+sqrt(2a))/epsilon)^2
on Ioi 0. Its image is Ioi(2a/epsilon^2), derivative
2*(z+sqrt(2a))/epsilon^2>0, and it is injective there. Apply
integral_image_eq_integral_abs_deriv_smul from JacobianOneDim; then normalize
the composed kernel and consume the compiled transformed integral. No assumed
integral identity or integrability is added; the change-of-variables theorem
applies directly with derivative and injection evidence.

Update: inverse-map image, injectivity, derivative, original-variable exact
integral, integrability, and shifted finite tail-sum bound now compile.
`sum_occupancyTail_shift_le` bounds sum_{i<N} tail(r+i+1) by
(2/epsilon^2)*(1+sqrt(pi*a)) whenever r>=2a/epsilon^2.
The import `SumIntegralComparisons` supplies the monotone integral comparison;
the tail's nonnegativity and integrability justify enlarging the integration set.
Remaining: integer cutoff accounting and subgaussian probability/count
consumer, then source MOSS constants and concrete history connection.

Integer cutoff route: m=ceil(2a/epsilon^2). For n<=m use probability<=1;
otherwise split the first m entries and the remaining n-m entries. The latter
start at m+1 and are bounded by sum_occupancyTail_shift_le. Since m<u+1,
the combined bound is 1+2/epsilon^2*(a+sqrt(pi*a)+1), exactly the source.
This generic numeric aggregation lemma must subsequently consume proved
pointwise subgaussian event bounds, not be called the probability theorem itself.

Update: integer cutoff aggregation and the actual source expected-count
conclusion now compile in `ConcentrationGaussianOccupancy` and
`ConcentrationIndexOccupancy`. The latter derives the fixed-radius empirical
mean tail from the compiled independent maximal bound, proves measurability,
expands the finite indicator-count integral, and obtains
E[kappa]<=1+2/epsilon^2*(a+sqrt(pi*a)+1). Strong measurability, independence,
zero means and unit-subgaussian MGF contracts are explicit; no tail premise
is assumed in the final theorem. This covers the expected-count conclusion,
not a separate formal definition/comparison of the source auxiliary kappa-prime.
Next required MOSS step is substituting a=2*logPlus(gap^2/delta), epsilon=gap/2,
then proving the large-gap constant 15 and connecting actual selected counts.

MOSS expectation consumer route: identify the fixed-log count definition with
fixedRadiusCount at a=2*logPlus(gap^2/delta), epsilon=gap/2; prove the derived
fixed count integrable from measurable indicators; integrate the existing
pointwise correction. Positivity of logPlus follows from delta<gap^2, which
will be derived from the required large-gap condition, not assumed in the
final regret statement. APIs: integral_mono_of_nonneg, integrable_finset_sum,
integral_add and finite-measure constant integral. Source and constants unchanged.

Compiled: `MOSSExpectedOccupancy.integral_indexExceedanceCount_le` (namespace
MOSS) now yields the actual variable-radius count expectation bounded by
gap^-2+1+8/gap^2*(2L+sqrt(2*pi*L)+1), L=logPlus(gap^2/delta).
The fixed-count integrability producer is also compiled. This still requires
the numerical large-gap simplification and actual selected-count connection.
Next scalar route: q=gap^2/delta>=64, use Real.log_div_sqrt_antitoneOn and
Real.log_div_self_antitoneOn (Log.Monotone), sqrt monotonicity, log_two_lt_d9,
and pi_lt_d2. Bound log(64)<=17/4 and sqrt(2*pi*log(64))<=21/4;
the resulting rational bound 119/8 is below 15. No change of source constant.
Update: `MOSSConstants.largeGap_constant_fifteen` and
`largeGap_scaled_constant_fifteen` now compile. `MOSSExpectedOccupancy`
consumes them in `gap_mul_integral_indexExceedanceCount_le`, proving
gap*E[kappa] <= gap+15/sqrt(delta) under gap>=8*sqrt(delta).
The proof uses exact rational upper bounds for log(64) and pi, no numerical
oracle or added axiom. Next required node is actual selected-count transport,
with complete initialization, count-consistent empirical rewards, optimal-arm
index controlled by the derived deficit, and the finite-horizon regret split.

## Initialization audit and target-preserving correction

The source prose T_i(n)<=kappa_i omits the initial pull in the zero-based
implementation. Counterexample: n=k, deterministic centered stream zero,
positive suboptimality gap. Every arm is initialized once, while its MOSS
radius is zero at every s>=1 (delta=k/n=1), hence kappa_i=0.
The valid transport is T_i<=1+kappa_i. Do not assume the stronger false claim.
To retain exactly 39*sqrt(n*k)+sum gaps, strengthen the Lemma 8.2 count bound
by removing its loose additive 1: extend the tail kernel by 1 below
u=2a/epsilon^2, apply the antitone sum-integral comparison on [0,n], and
integrate to u+tailIntegral. Initial pull then supplies the one gap term.
This improves an intermediate lemma without changing the final theorem target.

Compiled correction: `ConcentrationCappedOccupancy` proves the globally
antitone capped tail, its integrability/exact integral, and
`sum_le_occupancy_bound_sharp`. `integral_fixedRadiusCount_le_sharp` derives
E[kappa]<=2/epsilon^2*(a+sqrt(pi*a)+1), removing the additive one.
The final source bound is unchanged. Next propagate this sharper intermediate
through the MOSS expectation consumer and prove actual selected-count transport
with its explicit initialization term. Full `73c0419` validation completed:
root, Tests (8909 jobs), ProofGraphExport, 400 Python tests (7 skipped,
193.963 seconds), check passed. Subsequent changes need a fresh full check.

Selected-count route (project-local, MLIB-FINSET-SUMS): search-memory and
list-lean-decls for sum_selected_pullCount found no existing exact identity.
Use Core.pullCount_succ and Finset.sum_range_succ, induction on the horizon,
to reindex arbitrary real weights of pre-pull counts over selected rounds.
No stochastic or regularity assumptions are needed, only decidable arm equality.
Import LeafLemmas and Mathlib finite real sums. This identity is a transport
leaf, not yet a proof that the MOSS policy satisfies the exceedance event.
The sharp MOSS expectation and gap-weighted bound now compile, respectively
without the additive one and with 15/sqrt(delta); old APIs remain wrappers.

Compiled transport: `PullCountReindex.sum_selected_pullCount` gives the exact
weighted reindexing identity. `pullCount_le_one_add_eventCount` and the thin
`MOSS.pullCount_le_one_add_indexExceedanceCount` retain the initial pull.
The selected-event premise is explicit, not a completed algorithm theorem.
Next derive this event from actual MOSS choices, count-consistent empirical
streams, and the optimal-arm optimism deficit; then integrate and assemble
the small/large-gap regret split. Chapter status remains partial.
