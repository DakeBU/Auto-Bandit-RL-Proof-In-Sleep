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
