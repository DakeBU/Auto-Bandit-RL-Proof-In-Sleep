# HOO source obligation ledger for independent semantic review

Scope: repaired Bubeck et al. (2011) Algorithm1 / Theorem6 line frozen in 47474f9, Definition5 clarification c88f0c8. Mathematical source under review: fc1cbe65f2f3a9b14c01e5a9cd504611efca3753. Every row below records an implemented proof location, not independent acceptance. Review status: pending.

| Frozen obligation | Implemented chain / terminal declaration | Semantic checks still required from independent review |
| --- | --- | --- |
| 1. Actual measurable causal HOO with exact B/path/history | Algorithms.HOOTree, HOOHistory, HOOMeasurable, HOOTrajectory; action_causal, action_injective, trajectory_condDistrib | Correct initial two-child infinity rule, prefix-only information, no finite-fuel truncation, fixed representative and left tie, exact chronological indexing |
| 2. A1/A2 geometry, nonattained suprema, packing and limsup power bound | HOOGeometry, HOOModel, HOOOptimalBranch, HOOLevels, HOOPacking, HOODimension; nearOptimalNodes_power_bound | Preserve general asymmetric dissimilarity; no metric/compactness/attained maximizer; complete open balls contained in target; log-zero convention; finite coarse scales derived |
| 3. Actual adaptive conditional concentration | HOOConditionalMGF, HOOConcentration, HOOConfidence, HOOIndexConfidence | Selected regions are predictable; no within-region IID or guaranteed future visits; integral/MGF producer actually consumes the trajectory law |
| 4. Repaired source Lemmas14-17 | HOOPrefix, HOOPathComparison, HOOSelectionTail, HOOTailSum, HOOExpectedVisits; poor_region_expected_visits | U/B indexing, union over active optimal path, initial rounds and additive four, actual counts rather than oracle premises |
| 5. Actual three-way partition and regret contributions | HOOPartition; actual_regret_partition. HOORegretPartition; pathwise_regret_le, boundary_expected_visits. HOOExpectedRegret; expected_regret_dimension_sums | I prefix heredity, first bad child, disjoint cover; one-play from actual injectivity; bad gap from parent depth h while visit denominator uses child depth h+1; justified expectation/sum interchange |
| 6. Every exponent above actual dimension, one constant for all N>=1 | HOORegretAlgebra; regret_sums_le. HOODepthOptimization; exists_regret_depth, log_horizon_pos_le. HOORate; expected_pseudoRegret_rate | K/gamma independent of horizon; exact geometric constants; integer cutoff H>=1; N=1 included; no real cutoff, supplied O-bound or changed algorithm |
| 7. Expected cumulative=expected pseudo-regret under actual reward law | HOOActualRegret; integral_trajectory_reward, expected_actual_eq_pseudoRegret, expected_actualRegret_rate | First reward is genuine selected-arm reward; successor uses actual joint kernel; bounded reward and mean integrability; one infinite compatible policy/law across horizons |
| Nondegenerate final-rate witness | HOOCantorModel + HOOCantorRate; dimension_le_two, expected_actual_rate. Tests.HOORateCanary | Infinite binary arms, complete A1/A2, distinct means, every reward law non-Dirac, actual final rate without a dimension assumption; certificate <=2 is conservative, not exact dimension=2 |

The statement-level local gate and standard-axiom audit do not settle source fidelity. The review must inspect hypotheses, construction, proof-term dependencies and source repairs, not merely theorem names or this ledger. Accepted topics remain 0/10 pending review, shared mapping and ICLR program evidence. No reviewer verdict is fabricated here.


## Independent round trip checkpoint (2026-09-20)

The 32-file packet (28 production modules and four canaries) has now undergone
source-blind reconstruction, independent full-chain source comparison and
separate source-repair review. The kernel-model chain is accepted with explicit
initialization/index/logarithm/log-zero/fixed-choice deltas. Review found a real
extra assumption: the original terminal API requires a globally measurable
reward kernel. The [reward-family adapter](HOO-REWARD-FAMILY-ADAPTER.md) removes
that assumption in a separately compiled prototype; supplementary blind/source
reviews and hashes are recorded in `hoo-semantic-review.json`.

The earlier table remains a location/obligation map, not a fresh production gate.
The new adapter still needs production/public-root/canary integration. Recent
comparison-source disposition, site/shared registry mapping and ICLR evidence
remain mandatory; neither this checkpoint nor the old compiler gate completes
the Lipschitz topic.


## Production checkpoint (2026-09-20)

The reward-family adapter is now integrated in the public shared library and its new public-root canary passes. Original-chain, prototype, production port and mapping reviews are independently accepted with explicit deltas. Joint root9017, Tests9116,437Python tests7skips and generated-site checks passed at clean code785af09. Nine canonical reading references and an inline mathematical explanation are verified. Receipt: `runs/extended-topics-20260919/hoo-production-validation.json`. Earlier prototype-only/pending-production wording is historical; all-topic ICLR and topic completion remain pending.
