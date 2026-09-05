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

Policy-event producer route: project-local MOSS stream bridge, using the
actual `MOSS.action` equality at each time (not an exceedance oracle), empirical
means equal to mean plus centered stream averages at the realized pull count.
First prove every positive prefix index is bounded below by minus the recursive
optimism deficit; normalize delta=k/n in radius by field algebra. Initialization
forces zero pre-pull counts for initial selections and positive best-arm counts
after k. Apply the existing argmax selection lemma and initialization-safe
count transport. Assumptions are n>=k>0 and pathwise policy consistency;
stochastic stream/history law identification remains a separate obligation.

The policy-equation count bound compiled. To discharge even this deterministic
equation premise, construct a recursive vector of arm counts, choose using
MOSS.action at that vector and the corresponding empirical stream averages,
and prove by induction that the vector equals Core.pullCount for the generated
trace. No change to probability contracts; this is a concrete algorithm producer.

Compiled `MOSSStream`: prefix deficit control, radius normalization, exact
stream-count state invariant, and `streamTrace_pullCount_le`. This last theorem
constructs the algorithm and needs no exceedance/policy-equation oracle. It
still has the pathwise large-gap condition gap>2Z. Next assemble the pathwise
regret split at max(8*sqrt(k/n),2Z), integrate the already proved occupancy
and deficit bounds, and identify this centered-table execution with the
common history law for arbitrary finite-arm unit-subgaussian rewards.
Full check at c8f4106 passed: root build, Tests (8912 jobs), ProofGraphExport,
400 Python tests in 209.945 seconds, 7 skipped. Newer commits need fresh checks.

Regret assembly route (project-local, MLIB-FINSET-SUMS): use existing
finset_sum_pullCount_eq_time and RealMeanRegretPullCount, retrieved with
search-memory/list-lean-decls sum_pullCount. Pointwise split each gap at
8*sqrt(delta) and 2Z. Small gaps cost at most (8*sqrt(delta)+2Z)*T_i;
the remaining arms use the concrete streamTrace count bound. Retain the
deterministic large-gap filter so integration uses the sharp expectation
bound only where gap>=8*sqrt(delta). All gaps nonnegative via best-arm premise.

Compiled: `MOSSRegret.streamTrace_realMeanRegret_le` proves the pathwise
decomposition for the actual recursive execution. `integrable_indexExceedanceCount`
supplies finite-indicator integrability without tail assumptions.
`integral_largeGapCountSum_le` bounds the filtered expectation by
sum gaps + k*15/sqrt(delta), using the sharp bound and only one initialization
gap per arm. Next prove measurable stream execution/integrable regret, then
combine with the deficit term and normalize delta=k/n to obtain constant 39.
The centered-table/history-law bridge and broader-class conclusion remain open.

Regularity route: project-local stream execution. Reuse measurable finite
argmax from ETCRealEmpiricalMean (same UCB.scoreArgmax definition), measurable
evaluation of a countable family of stream averages at a measurable Nat count,
and induct on streamCounts. Then reuse integrable_real_pullCount_of_measurable_action
and integrable_realMeanRegret_of_integrable_pullCount. Only strong measurability
of the centered coordinates and a finite measure are required, no independence
for these regularity results. This prevents relying on totalized Bochner
integrals before measurable execution has been certified.

Compiled: `MOSSStreamMeasurable` proves measurable recursive counts/actions
and integrable realMeanRegret under a finite measure. `MOSSExpectedRegret`
then proves `integral_streamTrace_regret_le`, exactly
E[realMeanRegret]<=39*sqrt(n*k)+sum gaps for the concrete centered-table MOSS
execution, under explicit per-arm independent, mean-zero, unit-subgaussian
coordinate contracts and n>=k>0. The bound uses no tail/count/regret oracle.
Next required bridge: construct centered streams from arbitrary arm reward
laws and identify this generated execution with MOSS.historyAlgorithm's
common history law. Do not infer broad-class/chapter completion from the
table theorem alone. Source wording, theorem exports and final gates still
need synchronized evidence once that bridge compiles.

Canonical law route: reuse UCB.armStreamMeasure (stationary product kernel),
armStreamMeasure_map_coord, iIndepFun_armStreamMeasure_coord_sub and
hasSubgaussianMGF_armStreamMeasure_coord_sub. Define centered coordinates as
table i arm - mean arm. MOSS uses i=1,2,...; coordinate zero is unused.
This harmless explicit one-based convention must match reward consumption
table(count+1,arm). No HasSubgaussianMGF.integral_eq_zero API was found;
derive zero means by integral_map and integral_sub with the explicit
arm-mean equation integral id = mean. Raw integrability follows by adding
the constant mean to the integrable centered reward.
The resulting theorem quantifies over arbitrary Markov reward kernels, but
history-law identification remains required. No Gaussian-only restriction.

Compiled `MOSSCanonicalReward.integral_canonicalReward_regret_le` (MOSS
namespace) consumes arbitrary Markov arm laws with their actual means and
unit-subgaussian centered MGFs, deriving all table independence/centering
contracts from the canonical product measure. `canonicalReward_action_eq_raw`
proves the action depends on raw empirical rewards and counts; unknown means
cancel after initialization, and initial choices ignore them.
Next identify finite histories using reward table(count+1,arm) and prove the
selected unused reward has the arm's law conditionally on history; then
transport to MOSS.historyAlgorithm and the main-prose near-minimax consumer.
Full check 81f500f passed: root, Tests (8915 jobs), ProofGraphExport, 400 Python
tests in 180.365 seconds, 7 skipped. Newer changes still need full validation.

Finite-history bridge route: define observed rewards by the existing
UCB.rewardFromArmStream applied to table shifted by one coordinate; form
History.finitePairHistoryOfTrace. Reuse exact sumRewards/pullCount history
identities from ETCRealHistoryScore and the UCB stream-prefix identity.
Then canonicalReward_action_eq_raw proves the next action is precisely
MOSS.historyAction. This is a pathwise identification, not yet equality of
the induced history measures; conditional unused-coordinate law remains next.

Compiled `MOSSCanonicalHistory`: canonical observed reward, finite history,
exact pull counts/raw empirical means, initial/next action identity with
MOSS.historyAction, measurable reward/history, recursive history extension,
and `canonicalHistory_eq_of_eq_consumed`. The last proves that changing any
unconsumed coordinates preserves the already observed history.
Next reuse the coordinate-without-coordinate independence from
UCBArmStreamConditionalReward and adapt its countable next-coordinate branch
argument to this MOSS history. Its UCB-specific history theorem cannot be
used directly. No conditional-law or history-measure equality is yet claimed.

Single-coordinate route: reuse UCB.armStreamWithoutCoordinate and
armStreamInsertCoordinate, but define MOSS next coordinate as (count+1,arm)
for its one-based table convention. From consumed-history invariance derive
history equality whenever count<target.index and complements agree. Prove
selection of target is invariant under inserting any replacement value,
in both directions, so the selection branch factors through the complement.
Then the history/action condition on that branch is a measurable function
of the complement, independent of the target reward under armStreamMeasure.

Compiled `MOSSUnusedCoordinate`: complement-history invariance, the two-way
next-coordinate insertion equivalence, actual/reconstructed condition equality
on a selected branch, measurable reconstruction, coordinate independence, and
`map_canonicalConditionWithout_coordinate` product joint law. A simplifier
timeout was repaired by congrArg on the history equality, without increasing
heartbeats or changing the proof route. Next restrict the product law to each
next-coordinate branch and sum the countable disjoint partition; this is still
needed before claiming the actual selected reward conditional law.

Branch restriction route: project-local adaptation of the compiled UCB proof,
with the MOSS count+1 coordinate map. Use Measure.restrict_map and map_congr
on the measurable branch, the insertion equivalence for reconstructed branch
preimages, and restrict_prod_eq_prod_univ for the product law. No new stochastic
assumption. Then sum the countable disjoint coordinate partition.

Compiled `MOSSRewardBranch.map_condition_reward_restrict_branch` and
`MOSSConditionalReward.map_condition_reward_eq_compProd`: the actual
successor condition/reward pair has the condition marginal followed by the
selected arm kernel. `canonicalReward_condDistrib` gives the corresponding
almost-everywhere conditional law, without a conditional-law premise.
This completes the successor unused-coordinate law; next prove the initial
joint law and inductively identify the canonical histories with the common
MOSS.historyAlgorithm law, then transport the constant39 expected regret.
Full e2479fb validation passed: root, Tests (8919 jobs), ProofGraphExport,
400 Python tests in 196.650 seconds, 7 skipped. Later changes need fresh check.

Common history-law route: use LowerBounds.canonicalBanditHistoryMeasure_zero
and _succ, and Thompson.IsHistoryAlgorithmEnvironmentSequence. Initial action
is arm zero, first reward table(1,zero) has its prescribed arm law. Deterministic
historyAction gives the action condDistrib via condDistrib_comp_self; combine
with the proved successor feedback conditional law using RewardKernel's split
pair producer. Then map singleton/successor measurable equivalences and induct
on inclusive time. This matches Chapter13's existing history functional.

Compiled `MOSSHistoryLaw.map_canonicalHistory_eq`: for every inclusive time,
the reward-table history pushforward equals LowerBounds.canonicalBanditHistoryMeasure
for the actual MOSS.historyAlgorithm and arbitrary stationary arm kernel.
The initial pair law, deterministic policy conditional law and full common
process contract are compiled producers, not premises. Next transport the
expected regret using this equality with the exact finite-history gap
functional, then discharge the broader-class near-minimax consequence and
perform the chapter evidence/review/export/site completion audit.
