# Actual collision-frequency concentration work

Source: Rosenski--Shamir--Szlak ICML2016 static Algorithm1, supplement A.1
Lemma3, with the separately reviewed all-player failure allocation in
MULTI-AGENT-PROOF-ROUTE.md. Owning scratch:
runs/extended-topics-20260920/MusicalChairsCollisionPrototype.lean.

Target: derive the ACTUAL iid exploration collision indicators' bounded mean,
time independence, centered sub-Gaussian proxy1/4 and frequency tail, specialize
to tolerance1/(10k), then union over players. Retain the second exploration
budget50k^2 log(4k/delta); no independence across players is assumed. Population
inverse-log rounding is a separate remaining theorem, not a supplied premise.

Retrieval: inspected Mathlib PMF integral_eq_sum, Measure.ext_of_singleton,
Measure.pi_singleton, measurePreserving_eval, integral_map, integral_indicator,
iIndepFun_pi and bounded-variable/sub-Gaussian finite-sum APIs. Reuse the actual
FinitePMF.iid exploration law and generic Mathlib concentration. Prove equality
of its induced measure to Measure.pi using singleton masses, rather than
introducing an unrelated Bernoulli law. Event variables are measurable on finite
discrete action spaces, bounded in[0,1] and integrable. Their mean is the actual
event measure. Only temporal independence is needed. Fixed finite horizon,
two-sided closed tail event; no stopping or anytime claim. Frequency requires
T>0. Intended endpoint is an actual all-player event with failure<=delta/2.

Semantic plan: independent source-blind reconstruction followed by source review
of the complete new chain and constants; standard-axiom audit and exact folded
reader. This remains scratch until accepted extraction/public-root integration
and shared gates. It adds a theorem edge towards population correctness;
it does not complete the multi-agent topic or the ten-topic Goal.

## Compiled endpoint and next analytic step

The actual finite iid PMF is now proved equal to its product measure. All
indicator marginal/mean/independence/centered-sum/frequency theorems compile.
The actual collision probability is recovered from the prior draw law, the
local feedback count is identified, and the player union gives the second
budget50k^2 log(4k/delta). Pullback to the same joint reward law and the union
with mean failure produce actual simultaneous local-statistics accuracy>=1-delta.
The exact natural ceiling/max explorationLength now supplies both budgets and
positive duration under0<delta<1. This does not prove population recovery.

Focused compilation exited0. The37 new scanned declarations (28 theorems) all
passed a separate #print axioms build using only propext, Classical.choice and
Quot.sound. Previous reward/exploration code is included unchanged as context.
Independent blind reconstruction completed; source-facing acceptance is recorded
separately in multi-agent-collision-review.json once complete. No public gates
are inferred from these scratch checks.

Compiler fixes were interface-level: measurable finite sets use
(Set.toFinite E).measurableSet; finite count simplification must avoid the
card/sum_const rewrite loop; positive multiplicative cancellation uses
mul_le_mul_iff_right₀; toReal conversions use simp only to preserve the natural
k-1 cast. No probability assumption, event, threshold or source constant changed.

Next inverse-log route stays at the reviewed gamma=2/5. Retrieved upstream
rpow_one_add_le_one_add_mul_self from Analysis.Convex.SpecificFunctions.Basic
(global namespace), Real.rpow_neg and Int.round_eq_iff. The positive fractional
power tangent bound plus reciprocal algebra gives both margins, so no informal
Taylor approximation is needed. The source comparison/rounding correctness and
actual local population estimator remain separate work, followed by ranking.

Independent source review accepted with explicit delta; all28 new proofs and three canaries inspected, blind reconstruction matched, exact reader fold and unchanged context verified. The receipt above binds hashes and the precise scratch-only acceptance scope.
The private next-step API experiment is
E:/ABRL/maintenance/extended-topics-20260920-multi-agent/population-inverse-api.lean.
Its base_gamma_upper and base_neg_gamma_lower compiled (one stylistic linter
warning only); these are not part of this checkpoint's semantic acceptance or
public declaration count and do not establish the estimator. Preserve their
primitive assumption k>1 when connecting to the source n<k domain.
