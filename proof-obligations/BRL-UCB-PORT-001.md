# Proof Obligations: BRL-UCB-PORT-001

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | pinned LML source, ABRL core | `LML-UCB-REGRET`, `TXT-LATTIMORE-SZEPESVARI-2020` | port the mathematical route locally while keeping actual LML symbols card-only across the toolchain mismatch | theorem-card status, toolchain alignment | project-local decision | upper | route recorded in task/conversion window | memory | compiled |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret`, `LeafLemmas`, `PullCountDecomposition`, `RegretDecomposition` | pull counts, segment counts, reward sums, gap surface, deterministic pull-count partition, deterministic regret-by-pull-count identity | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS`, `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `LOCAL-LEAF-REGRET-DECOMPOSITION`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | compiled dependency-light bookkeeping plus Mathlib Finset wrappers, finite-action count partition, and arm reindexing | finite arms, horizon, rational mean model | project-local compiled leaves | reviewer | `pullCount_le_time`, `pullCount_add_le`, `finset_sum_pullCount_eq_time`, `sumRewards_add_eq_of_forall_ne_between`, `pseudoRegret_add_eq_of_forall_gap_zero_between`, `pseudoRegret_eq_finset_sum_gap_mul_pullCount` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | compile the pinned-source Real empirical mean, realized pull-count width, finite-history index, and least-encoded selector | port route | `UCBRealHistoryIndex`, `ETCRealHistoryScore`, measurable sum/count APIs, Real log/sqrt | `LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX`, `MLIB-REAL-LOG-SQRT`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL` | define `sumRewards/pullCount` and `sqrt(2*c*log(n+1)/pullCount)`, align inclusive history at `n` with trace time `n+1`, reuse least-encoded argmax | positive K only for selector; canonical measurable Fin and timewise action/reward measurability for measurable endpoints; no count positivity or probability law | project-local over Mathlib and compiled local wrappers | lower Lean | `UCB.realIndexAction`; `UCB.realHistoryIndexAction_finitePairHistoryOfTrace`; `UCB.measurable_realIndexAction` | build | compiled |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards, `MeasureFoundation`, `MeasurableSums`, `MeasurableLocalQuantities`, `MeasurableRegret`, `MeasurablePullCount`, `MeasurablePullCountCast`, `ExpectationFoundation`, `ExpectationSums`, `ExpectationPullCount`, `ExpectationWeightedPullCount` | LML/Mathlib concentration route plus measurable action-event/indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities | `LOCAL-LEAF-MEASURE-FOUNDATION`, `LOCAL-LEAF-MEASURABLE-SUMS`, `LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES`, `LOCAL-LEAF-MEASURABLE-REGRET`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`, `LOCAL-LEAF-EXPECTATION-FOUNDATION`, `LOCAL-LEAF-EXPECTATION-SUMS`, `LOCAL-LEAF-EXPECTATION-PULLCOUNT`, `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION` | one-sided and union-bounded tail event control after event, pull-indicator, selected-reward indicator, finite-sum, `sumRewards`, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities are explicit | measurability, lower-integral event measures, lower-integral finite sums, lower-integral pull counts, lower-integral weighted pull counts, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported, with local measurable-event, indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count leaves compiled | lower retrieval | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward`, `measurable_finset_sum_indicator_reward`, `measurable_sumRewards`, `measurable_pseudoRegret`, `measurable_pullCount`, `measurable_natCast_pullCount`, `lintegral_actionTrace_eval_eq_indicator_one`, `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`, `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`, `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` plus TBD tail declarations | memory/build | obligation |
| `UCB-PEELING-LAW` | transport the adaptive `(pullCount,sumRewards)` event to a finite sum of fixed-sample arm-reward events | native index and a fixed-arm prefix source | `UCBFixedCountPeeling`, `ProbabilityUnionBound`, `IdentDistrib`, count/sum wrappers | `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW`, `LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX`, `LML-UCB-REGRET`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-FINSET-SUMS` | pathwise selected-reward prefix identity, finite count union, then complete-stream law transport by measurable fixed-prefix composition | measurable source/canonical spaces, measurable stream coordinates and event, decidable projected-count filter; no probability/MGF/independence premise | project-local source transport over Mathlib `IdentDistrib` and finite union | lower Lean | `UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource_identDistrib` | build | compiled |
| `UCB-ARM-STREAM-REWARD-SOURCE` | construct next-unused-coordinate rewards and the exact fixed-arm prefix source | `UCB-PEELING-LAW`, latent arm stream and arbitrary action trace | `UCBArmStreamSource`, count/sum successor lemmas, finite range sums, measurable Pi evaluation | `LOCAL-LEAF-UCB-ARM-STREAM-REWARD-SOURCE`, `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW`, `LML-UCB-REGRET`, `MLIB-FINSET-SUMS` | mirror LML reward indexing and prove the selected sum/pull-count prefix invariant by horizon induction | coordinate measurability only for a general source; no action measurability, law, stationarity, independence, MGF, filtration, or count positivity | project-local source construction; LML remains card-only | lower Lean | `UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum`; `UCB.canonicalFixedArmPrefixSource` | build | compiled |
| `UCB-ARM-STREAM-PROCESS-LAW` | construct the measurable recursive UCB action and canonical stationary/product arm-stream law | `UCB-ARM-STREAM-REWARD-SOURCE`, native UCB index action, stationary arm kernel | recursive action/history on stream space; measurable finite histories/random coordinate evaluation; infinite product arm laws | `LOCAL-LEAF-UCB-ARM-STREAM-REWARD-SOURCE`, `LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX`, `LML-UCB-REGRET`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-KERNEL` | define inclusive recursive histories, prove coordinate measurability by induction, identify the actual finite trace history, package next-unused rewards, and instantiate the double `infinitePi` law | `0<K`, canonical Pi spaces; Markov arm kernel only for product law; no MGF/filtration/count positivity | project-local process/law construction | lower Lean | `UCB.measurable_armStreamAction`; `UCB.armStreamHistory_eq_finitePairHistoryOfTrace`; `UCB.armStreamMeasure` | build | compiled |
| `UCB-ARM-STREAM-INDEX-TAIL` | prove source-faithful one-sided random-width UCB index tails with LML inverse-power envelope | process/product law, fixed-count peeling, independent fixed-prefix concentration | product coordinate map/independence, centered MGF sum tail, positive-count peeling, width algebra, Real/ENNReal rpow | `LOCAL-LEAF-UCB-ARM-STREAM-PROCESS-LAW`, `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-SUBGAUSSIAN`, `LML-UCB-REGRET` | prove each fixed-count deviation, peel adaptive counts, rewrite empirical-mean failures, collapse the log tail, and bound by `1/(n+1)^(c-1)` | `0<K`, Markov kernel, centered per-arm `HasSubgaussianMGF`, `0<=c`, nonzero proxy; outer measure only | Mathlib-backed concentration/product/rpow plus local adapters | lower Lean | `UCB.measure_realEmpiricalMean_add_realWidth_le_mean_rpow_bound`; `UCB.measure_mean_le_realEmpiricalMean_sub_realWidth_rpow_bound` | build | compiled |
| `UCB-ARM-STREAM-EXPECTED-PULLCOUNT` | integrate one positive-gap arm's recursive pull count under the product law | process measurability, one-sided index tails, generic selected-small/large count split | actual-width threshold algebra, selected-large union, finite ENNReal tail sum, lower integral | `LOCAL-LEAF-UCB-ARM-STREAM-PROCESS-LAW`, `LOCAL-LEAF-UCB-ARM-STREAM-INDEX-TAIL`, `LML-UCB-REGRET`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | prove initial positivity and `gap<=2*width`; derive ceiling threshold; union-bound two failure events; sum and integrate | `0<K`, `0<c`, nonzero proxy, positive queried-arm gap, Markov kernel, centered MGFs for best and queried arms | Mathlib-backed local expected-count endpoint | lower Lean | `UCB.lintegral_natCast_pullCount_armStreamAction_le_threshold_add_two_mul_constSum` | build | compiled |
| `UCB-FINAL` | canonical theorem with the exact `Bandits.UCB.regret_le` RHS | all above including expected pull count | Real Bochner expected-count conversion and deterministic gap-weighted regret decomposition | expected-count leaf, Real regret/pull-count leaf, `LML-UCB-REGRET`, `MLIB-MEASURE-INTEGRAL` | convert ENNReal count bound to Real expectation, sum arm gaps, split zero gaps, normalize inverse-gap term | `0<K`, `0<c`, nonzero common proxy, Markov Real arm kernel, centered MGF for every arm | project-local canonical final theorem; upstream symbols remain card-only | lower Lean | `UCB.integral_realKernelRegret_armStreamAction_le_lml_sum` | build | compiled |
| `UCB-EXTERNAL-ACTION-LAW-LML-REGRET` | transport the exact canonical RHS to any external action process with the same complete action-trace law | `UCB-FINAL`, measurable regret functional, Mathlib `IdentDistrib` | `measurable_pi_lambda`, finite-sum measurability, `IdentDistrib.comp`, `IdentDistrib.integral_eq` | `LOCAL-LEAF-UCB-ARM-STREAM-LML-REGRET`, `MLIB-MEASURE-INTEGRAL`, pinned `LML-UCB-REGRET` | prove full trace/regret measurability, compose the action-law witness with regret, transport the integral, invoke the canonical theorem | canonical UCB contracts plus complete action-trace `IdentDistrib`; no probability-measure, separate integrability, filtration, reward-process, or standard-Borel premise | project-local external law adapter; upstream symbols remain card-only | lower Lean | `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStreamAction` | build | compiled |
| `UCB-EXTERNAL-ARM-STREAM-SOURCE-LAW-LML-REGRET` | optionally construct the complete action law and exact regret from a latent arm stream with canonical complete law and a.e. recursive action generation | external action-law theorem, canonical stream/action measurability, Mathlib `IdentDistrib` | `IdentDistrib.comp/of_ae_eq/trans`, `AEMeasurable.congr`, `EventuallyEq.symm` | process-law leaf, external action-law leaf, `MLIB-PROBABILITY-INDEPENDENCE` | push the stream law through `armStreamAction`, replace generated action by the external action a.e., compose law identities, invoke exact regret | canonical contracts plus latent `ArmRewardStream` law and a.e. generated-action equality; no probability-measure, separate measurability, external reward trace, filtration, or standard-Borel premise | optional stronger project-local source-law adapter; not required by pinned LML | lower Lean | `UCB.identDistrib_action_armStreamAction_of_identDistrib_armStream`; `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStream` | build | compiled |
| `UCB-EXTERNAL-ACTION-REWARD-TRAJECTORY-LAW-LML-REGRET` | project a complete observable action/reward trajectory law to the canonical action law and exact regret sum | external action-law theorem, canonical arm-stream action/reward process, Mathlib `IdentDistrib` | measurable Pi projection by `Prod.fst`, `IdentDistrib.comp` | pinned `IsAlgEnvSeq.identDistrib_trajectory`, `ArrayModel.isAlgEnvSeq_arrayMeasure`, process-law and action-law leaves | compose pair-trajectory law with coordinatewise action projection, then invoke exact regret | canonical contracts plus complete observable pair-trajectory `IdentDistrib`; no latent stream, unused-arm independence, separate measurability, filtration, or standard-Borel premise | faithful pinned LML trajectory projection; upstream symbols remain card/source evidence | lower Lean | `UCB.identDistrib_action_of_identDistrib_actionRewardTrace`; `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_actionRewardTrace` | build | compiled |
| `UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET` | derive complete observable pair-trajectory law and exact UCB regret from a shared initial pair marginal and successor pair conditional kernels | finite-prefix trajectory uniqueness, projective-limit uniqueness, observable trajectory regret theorem | `Finset.sup`, measurable finite restrictions, `IsProjectiveLimit.unique`, `IdentDistrib`, `condDistrib`, `trajMeasure` | Mathlib `FiniteDimensionalLaws`/`Projective`, local prefix theorem, pinned `IsAlgEnvSeq.identDistrib_trajectory` and array model | lift every finite coordinate marginal from an `Iic` prefix; identify full laws as the same projective limit; instantiate pair coordinates and consume exact regret | finite source measures; measurable coordinates; nonempty standard-Borel pair target; probability `mu0`; Markov pair kernels; `[NeZero K]` elaboration bridge; canonical UCB contracts; no latent unused-arm law, filtration, conditional expectation, or pre-assumed trajectory law | generic uniqueness is a compiled Mathlib candidate; UCB wrapper is project-local | lower Lean | `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`; `RewardKernel.identDistrib_rewardTrace_of_common_condDistrib`; `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_common_actionReward_condDistrib` | build | compiled |
| `UCB-CANONICAL-ACTION-REWARD-CONDDISTRIB-LML-REGRET` | derive complete pair-trajectory law and exact regret directly from external initial/successor laws matching canonical arm-stream UCB | common-law uniqueness, canonical coordinate measurability, observable trajectory theorem | `Measure.isProbabilityMeasure_map`, built-in `condDistrib` Markov instance, `IdentDistrib` | Mathlib `CondDistrib`, local common-law leaf, pinned `IsAlgEnvSeq.identDistrib_trajectory`/array model | choose canonical time-zero pushforward and canonical regular conditional kernels internally; discharge canonical obligations by reflexivity; apply uniqueness and exact regret | finite external measure; measurable external coordinates; `[NeZero K]`, `0<K`; Markov arm kernel; initial pair-law equality; successor conditional-law equality; canonical sub-Gaussian contracts; no supplied `mu0`/kernel, latent arrays, filtration, conditional expectation, or full-law premise | project-local specialization over compiled generic uniqueness | lower Lean | `UCB.identDistrib_actionRewardTrace_of_condDistrib_eq_armStream`; `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_condDistrib_eq_armStream` | build | compiled |

Compiled bridge update: `EXP-PULLCOUNT-LE-TIME` is now available through
`LOCAL-LEAF-EXPECTATION-PULLCOUNT-BOUNDS` and declaration
`lintegral_natCast_pullCount_le_time`.  Use it as an `ENNReal` probability
pull-count budget bound for UCB expected-count scaffolding; it does not close
`EXP-REGRET-PULLCOUNT`, concentration, or the final UCB theorem.

Compiled weighted bridge update: `EXP-WEIGHTED-PULLCOUNT-LE-TIME` is now
available through `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT-BOUNDS` and
declaration
`lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.  Use it
as the `ENNReal` weighted probability budget bound before choosing a
`Fin K`/`Finset.univ`, scalar-conversion, or Bochner expected-regret route.

Compiled finite-arm bridge update: `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` is now
available through `LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-BOUNDS` and declaration
`lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.  Use it as
the finite-arm `Finset.univ` budget bound before the separate scalar conversion
for `FiniteBanditModel.gap : Fin K -> Rat`.

Compiled model-gap bridge update: `EXP-MODEL-GAP-OFREAL-BOUND` is now available
through `LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-MODEL-BOUNDS` and declaration
`lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time`.
Use it as an `ENNReal.ofReal` surrogate bound for `FiniteBanditModel.gap`; it
does not prove Rat-valued expected regret or gap faithfulness.

Compiled scalar bridge update: `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` is now
available through `LOCAL-LEAF-SCALAR-ENNREAL` and declaration
`ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg`.  Use it for exact scalar
conversion under explicit nonnegativity before any UCB Rat-valued expected
regret claim.

Compiled pointwise pseudo-regret bridge update:
`OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` is now available through
`LOCAL-LEAF-SCALAR-PSEUDOREGRET` and declaration
`ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`.
Use it as a scalar/model faithfulness bridge under explicit model-gap
nonnegativity; it does not prove expected regret, model-gap nonnegativity,
concentration, or the final UCB theorem.

Compiled lower-integral pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-OFREAL-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`.
Use it as an `ENNReal.ofReal` lower-integral bound under explicit model-gap
nonnegativity; it does not prove Rat-valued expected regret, Bochner expected
regret, model-gap nonnegativity, concentration, or the final UCB theorem.

Compiled Rat-contract pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-RAT-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`.
Use it when UCB scaffolding has a Rat-level gap nonnegativity contract; it does
not prove that contract from `FiniteBanditModel.bestArm`.

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.

## Native Real History Index Obligation

`UCB-NATIVE-REAL-HISTORY-INDEX` is discharged in
`BanditRLProof.Algorithms.UCBRealHistoryIndex`. The module defines the actual
source-shaped Real empirical mean and sample-path-dependent width
`sqrt(2*c*log(n+1)/pullCount)`, their sum, inclusive finite-pair-history
versions, and least-encoded score maximizers.

The proof reuses the compiled finite-history count/sum/mean wrappers, maps the
inclusive history at index `n` to trace horizon `n+1`, and proves exact score
and selector equality. Mathlib measurable division/sqrt plus local measurable
sum/count declarations prove every score coordinate and the selected action
measurable. The selector also exposes score maximality for every arm.

Regularity is `0 < K` for the selector and timewise measurable action/reward
coordinates for measurable endpoints. There is no probability measure,
reward law, MGF, independence, filtration, or count-positivity assumption.
Retrieval evidence is pinned LML `ucbWidth'`, `ucbWidth`, `empMean'`,
`empMean`, `nextArm`, `measurableArgmax`, and `Bandits.UCB.regret_le`, plus
Mathlib log/sqrt and local finite-sum/measurability cards.

Status is `leanCompiled` with focused and external canary builds. Failure
policy: do not reuse the older deterministic `proxy : Nat -> Arm -> NNReal`
surface as though it were this random width. The next source-faithful blocker
is now the recursive UCB action and stationary/product law on the compiled
arm-stream reward source; after that come one-sided fixed-count sub-Gaussian
tails, expected pull counts, and the final regret sum.

## Fixed-Count Peeling Law Obligation

`UCB-FIXED-COUNT-PEELING-LAW` discharges `UCB-PEELING-LAW` in
`BanditRLProof.Algorithms.UCBFixedCountPeeling`. The source structure records a
measurable latent `Nat -> Fin K -> Real` table and the exact pathwise identity
between `sumRewards` and the arm prefix of length `pullCount`. The first theorem
peels an adaptive `(pullCount,sumRewards)` event over the finite filtered range
`0,...,n`; the second transports every fixed-count term from one
`IdentDistrib` law for the complete stream.

The proof uses `pullCount_le_time`, `Finset.range/filter/sum`,
`ProbabilityUnionBound.measure_biUnion_finset_le`, measurable Pi evaluation,
`Finset.measurable_sum`, and `IdentDistrib.comp/measure_mem_eq`. Its contracts
are measurable source/canonical spaces, measurable stream coordinates,
measurable event `s`, and decidability of the projected count predicate. It
does not assume a probability measure, independence, an MGF, filtration, or a
positive count.

Retrieval evidence is pinned LML
`SumRewards.identDistrib_sum_range_snd` and
`prob_pullCount_prod_sumRewards_mem_le` at commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74`, plus the local Mathlib cards for
`IdentDistrib`, finite sums, measure, and finite union bounds. Status is
`leanCompiled` with focused and external canary builds. Failure policy: the
generic peeling/law theorem is closed, but it must not be presented as a UCB
tail theorem until `UCB-ARM-STREAM-PROCESS-LAW` constructs the recursive UCB
action and canonical stationary/product stream law, or proves a separately
recorded conditional-MGF substitute.

## Arm-Stream Reward Source Obligation

`UCB-ARM-STREAM-REWARD-SOURCE` compiles in
`BanditRLProof.Algorithms.UCBArmStreamSource`. The reward at time `t` is the
selected arm's latent coordinate indexed by its pull count before `t`. A
horizon induction using the local count/sum successor lemmas and
`Finset.sum_range_succ` proves exact equality between selected `sumRewards` and
the arm prefix of realized length `pullCount`.

The module packages this identity as `FixedArmPrefixSource`, supplies a direct
`IdentDistrib` peeling consumer, and specializes to the canonical
`ArmRewardStream K` sample space where coordinate measurability follows from
Pi evaluation. Its contracts do not include action measurability, probability,
stationarity, independence, MGF, filtration, or count positivity.

Retrieval evidence is pinned LML `ArrayProbSpace.reward_eq` and
`SumRewards.sumRewards_eq` at commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74`, plus the compiled peeling and
local recursion APIs. Status is `leanCompiled` with focused and three external
canary checks. Failure policy: the pathwise source is closed; the recursive
process/product law and one-sided inverse-power tails now compile separately.
Expected pulls and regret must be obtained from those downstream leaves, not
inferred from this source theorem.

## Arm-Stream Process And Product Law Obligation

`UCB-ARM-STREAM-PROCESS-LAW` is discharged in
`BanditRLProof.Algorithms.UCBArmStreamProcess`. The recursive inclusive history
uses round-robin initialization, the native Real history index thereafter, and
the next unused latent coordinate of the selected arm. Its main invariant is
exact equality with `History.finitePairHistoryOfTrace` for the extracted action
and reward traces. Finite-history induction and joint random-coordinate
evaluation prove measurable histories, actions, and rewards. The double
`Measure.infinitePi` construction is a probability measure with the stationary
arm laws and feeds the actual process directly to the fixed-count peeling
endpoint.

Regularity is `0 < K` plus a Markov arm kernel for the product law. No MGF,
filtration, or positive-count premise is hidden. Retrieval evidence is pinned
LML `hist`, `action`, `reward`, `nextArm`, `ucbAlgorithm`, and `streamMeasure`
at commit `19dc3ab132c2a7539f5944503d1114eac4c5bb74`. Status is `leanCompiled`
with external history, action-measurability, and coordinate-law canaries.
Failure policy: recursion, measurability, product law, and peeling are closed;
the ENNReal expected-count consumer now compiles downstream.

## Arm-Stream UCB Index Tail Obligation

`UCB-ARM-STREAM-INDEX-TAIL` is discharged in
`BanditRLProof.Algorithms.UCBArmStreamTail`. Product-coordinate map laws and
`iIndepFun_infinitePi_coord` transport each centered per-arm
`HasSubgaussianMGF` witness to independent fixed-prefix sums. The compiled
peeling source then bounds adaptive positive-count deviations. Algebraic
adapters identify the actual recursive empirical-mean/random-width failures,
collapse the finite count sum to `n * exp (-c * log (n+1))`, and finally prove
the LML-shaped ENNReal bound `1 / (n+1)^(c-1)` for both one-sided events.

Regularity is `0 < K`, a Markov arm kernel, a centered per-arm MGF witness,
`0 <= c`, and a nonzero variance proxy for the log simplification. These are
outer-measure bounds and do not assume recursive action measurability.
Retrieval evidence is pinned LML `prob_ucbIndex_le` and `prob_ucbIndex_ge`,
Mathlib product independence, fixed-sum sub-Gaussian concentration, and
Real/ENNReal rpow APIs. Status is `leanCompiled` with inverse-power external
canaries. Failure policy: the concentration leaf is closed and consumed by the
expected-count and exact canonical regret theorems downstream.

## Arm-Stream UCB Expected Pull-Count Obligation

`UCB-ARM-STREAM-EXPECTED-PULLCOUNT` is discharged in
`BanditRLProof.Algorithms.UCBArmStreamExpectedPullCount`. The endpoint is
`UCB.lintegral_natCast_pullCount_armStreamAction_le_threshold_add_two_mul_constSum`.
It proves initialization positivity, selected-score maximality, the actual
random-width threshold, selected-large inclusion in the two one-sided failure
events, the `2*constSum` finite tail sum, the ENNReal lower-integral bound,
integrability, and the exact LML-shaped Real expected-count bound.

Regularity is `0<K`, `0<c`, nonzero NNReal `sigma2`, positive queried-arm
kernel gap, a Markov Real kernel, and centered `HasSubgaussianMGF` witnesses for
the best and queried arms. Retrieval evidence is pinned LML
`pullCount_arm_le`, `pullCount_le_add_three`, `constSum`, and
`expectation_pullCount_le'`, plus the local process/tail/count-split leaves.
Status is `leanCompiled` with external ENNReal and Real exact-statement
canaries. Failure policy: the expected-count route is closed and consumed by
the final theorem.

## Canonical Arm-Stream UCB Regret Obligation

`UCB-FINAL` is discharged canonically by
`UCB.integral_realKernelRegret_armStreamAction_le_lml_sum`. It rewrites
expected Real-kernel regret as the finite gap-weighted sum of integrable pull
counts, applies the Real expected-count theorem to positive gaps, removes zero
gaps, and normalizes the threshold term. The RHS exactly matches pinned
`Bandits.UCB.regret_le`.

Regularity is `0<K`, `0<c`, nonzero common NNReal proxy, a Markov Real arm
kernel, and centered MGF witnesses for all arms. Status is `leanCompiled` with
an exact external canary. Failure policy: the canonical mathematical route is
closed. The downstream complete action-law transport is also compiled by
`UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStreamAction`.
It uses `IdentDistrib.comp` and `IdentDistrib.integral_eq`, with no separate
integrability or probability-measure premise. The remaining compatibility
obligation is now discharged faithfully from complete observable action/reward
trajectory `IdentDistrib` by
`UCB.identDistrib_action_of_identDistrib_actionRewardTrace`. This matches pinned
LML `IsAlgEnvSeq.identDistrib_trajectory`; the latent arm-stream constructor is
  only an optional stronger adapter. Generic trajectory-law uniqueness from a
  shared initial marginal and successor pair kernels now compiles through
  `RewardKernel.identDistrib_rewardTrace_of_common_condDistrib`, and the UCB
  consumer reaches the exact RHS. The canonical specialization now constructs
  the shared measure/kernel bundle internally. The remaining source obligation
  is no longer joint pair-law assembly: the split-law compatibility theorem
  now composes the initial action/feedback fields and successor
  action/feedback fields with `compProd`, constructs complete trajectory
  `IdentDistrib`, and reaches the exact RHS. The only remaining source
  obligation is proving those four split fields from an actual upstream
  sequence or literal compatible-toolchain import.

`UCB-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` now closes the local field
compatibility theorem itself. `UCB.RealStationaryUCBSequence` packages the
measurability and four split-law fields, has a canonical arm-stream witness,
implies complete observable trajectory `IdentDistrib`, and feeds
`UCB.regret_le_of_realStationaryUCBSequence`. The exact finite-sum theorem no
longer exposes a long list of field hypotheses. The remaining boundary is not
mathematical assembly: it is constructing this bundle from actual imported LML
symbols under a compatible toolchain or from a separately defined concrete
external sequence.
