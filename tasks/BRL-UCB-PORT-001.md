# Port the UCB regret proof route

Task id: `BRL-UCB-PORT-001`
Kind: `literaturePort`
Status: `activePort`
Harness: `hierarchical`

## Goal

Build a local ABRL route for the finite stochastic UCB regret theorem, starting
from theorem cards and ending in either a compiled local theorem, a documented
import route, or a precise blocked ledger.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.UCB.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.UCB`
- Local surface: `BanditRLProof/Algorithms/UCB.lean`
- Textbook/source cards: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`, `MLIB-PROBABILITY-INDEPENDENCE`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.UCB.obligationNames
-- future local theorem compatible with Bandits.UCB.regret_le
```

## Proof Obligations

- [x] Decide `card-only`, `port`, or `dependency` route: local port with pinned
  LML source evidence; direct LML import remains cross-toolchain work.
- [x] Map UCB index, width, empirical mean, and pull-count definitions through
  `UCB-NATIVE-REAL-HISTORY-INDEX`.
- [x] Record sub-Gaussian tail dependencies and the fixed-sample-count peeling
  law transport used by the pinned theorem.
- [x] Construct the next-unused-coordinate arm-stream reward source and prove
  its exact selected-reward prefix invariant.
- [x] Construct the recursive source-faithful UCB arm-stream process and its
  canonical stationary product measure/peeling law.
- [x] Prove the actual recursive-process one-sided random-width index tails in
  the LML inverse-power form.
- [ ] Record expected pull-count bound dependencies.
- [ ] Keep proof export clear that LML is theorem-card status until local closure.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-UCB-PORT-001.md`.  Generic order, algebra, positivity,
summability, and concentration infrastructure should be prepared as Mathlib
candidates.  UCB-specific wrappers should remain thin and should point to
those reusable leaves.  Do not change the proof route without a reviewer-visible
statement, hypothesis, or counterexample audit.

## Build Gate

```bash
python3 tools/bandit.py check
```

## Native Real History Index Leaf

- Leaf id: `UCB-NATIVE-REAL-HISTORY-INDEX`.
- Lean statements: `UCB.realEmpiricalMean`, `UCB.realWidth`, `UCB.realIndex`,
  `UCB.realHistoryWidth`, `UCB.realHistoryIndex`, `UCB.realIndexAction`,
  `UCB.realHistoryIndexAction`, their measurability/maximality theorems, and
  the four finite-pair-history/trace alignment theorems.
- Local APIs/imports: `BanditRLProof.Algorithms.UCB`, `ETCRealHistoryScore`,
  `ETCRealArgmaxTie`, `History.finitePairHistoryOfTrace`,
  `measurable_sumRewards`, `measurable_natCast_pullCount`, Mathlib
  `Real.log`, `Real.sqrt`, and measurable division.
- Proof route: define the actual path-dependent score from
  `sumRewards/pullCount + sqrt(2*c*log(n+1)/pullCount)`; use the inclusive
  history count/sum wrappers with the source's `n+2` convention; transport
  each score coordinate to trace time `n+1`; reuse the least-encoded finite
  argmax for maximality and measurability.
- Regularity contracts: `0 < K` for selector construction, canonical finite
  measurable space for `Fin K`, and timewise measurable action/reward
  coordinates for measurability. No measure, reward law, MGF, independence,
  filtration, count positivity, or tail theorem is assumed.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, `ucbWidth'`, `ucbWidth`,
  `empMean'`, `empMean`, `nextArm`, `measurableArgmax`, and
  `Bandits.UCB.regret_le`; local Mathlib cards `MLIB-REAL-LOG-SQRT`,
  `MLIB-FINSET-SUMS`, and `MLIB-MEASURE-INTEGRAL`.
- Status: `leanCompiled`; focused module and external alignment/measurability
  canaries pass.
- Failure policy: concrete empirical means, the random pull-count width,
  history/trace mapping, least-encoded maximization, and measurability are
  closed. Fixed-count peeling and next-unused arm-stream reward consumption
  now compile separately, as do the recursive process/product law and
  inverse-power one-sided tails. The next faithful blocker is recursive action
  measurability followed by expected pull-count assembly. Do not force this
  sample-dependent radius through the older
  deterministic `proxy : Nat -> Arm -> NNReal` interface.

## Fixed-Count Peeling And Stream-Law Leaf

- Leaf id: `UCB-FIXED-COUNT-PEELING-LAW` (`UCB-PEELING-LAW`).
- Lean statements: `UCB.ArmRewardStream`, `UCB.armPrefixSum`,
  `UCB.FixedArmPrefixSource`, its stream/prefix measurability theorems,
  `UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource`, and
  the `_identDistrib` law-transport endpoint.
- Local APIs/imports: `UCBFixedCountPeeling`, `UCBRealHistoryIndex`,
  `pullCount_le_time`, `ProbabilityUnionBound.measure_biUnion_finset_le`,
  `Finset.range`/`filter`/`sum`, `measurable_pi_apply`,
  `Finset.measurable_sum`, and Mathlib `ProbabilityTheory.IdentDistrib`.
- Proof route: record the pathwise identity saying selected rewards from an arm
  are the first `pullCount` values of its latent stream; cover the adaptive
  pair event by the finite union over `k <= n`; apply the outer-measure union
  bound; compose one complete-stream `IdentDistrib` law with each measurable
  fixed prefix sum and rewrite the event measures.
- Regularity contracts: measurable source and canonical spaces, measurable
  latent-stream coordinates, measurable `s : Set (Nat x Real)`, and a
  `DecidablePred` for the projected count filter. No probability-measure,
  independence, MGF, filtration, or positive-count premise is required.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`,
  `SumRewards.identDistrib_sum_range_snd`,
  `prob_pullCount_prod_sumRewards_mem_le`, and the two UCB index-tail uses;
  local cards `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-FINSET-SUMS`.
- Status: `leanCompiled`; focused module build and two external canaries pass.
- Failure policy: generic adaptive-count peeling and complete-stream law
  transport are closed, and the next-unused-coordinate leaf now constructs
  `FixedArmPrefixSource`. Do not claim source-faithful UCB tails until the
  recursive UCB action and its stationary/product stream law compile, or an
  explicitly recorded conditional-MGF substitute of equivalent strength.

## Arm-Stream Reward Source Leaf

- Leaf id: `UCB-ARM-STREAM-REWARD-SOURCE` (compiled part of
  `UCB-ARM-STREAM-SOURCE`).
- Lean statements: `UCB.rewardFromArmStream`,
  `UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum`,
  `UCB.fixedArmPrefixSourceOfArmStream`, the `_identDistrib` peeling consumer,
  `UCB.canonicalFixedArmPrefixSource`, and the canonical-stream peeling
  endpoint.
- Local APIs/imports: `UCBArmStreamSource`, `UCBFixedCountPeeling`,
  `sumRewards_succ_of_eq/ne`, `pullCount_succ_of_eq/ne`,
  `Finset.sum_range_succ`, and measurable Pi evaluations.
- Proof route: define reward at time `t` as the selected arm's latent coordinate
  indexed by its earlier pull count; induct on `n`, splitting on whether time
  `n` selects the fixed arm; package the exact prefix identity into the
  existing source and peeling interfaces.
- Regularity contracts: arbitrary action trace and arm stream pathwise;
  coordinate measurability only for the general source adapter. The canonical
  stream specialization discharges coordinate measurability automatically.
  No action measurability, probability measure, stationarity, independence,
  MGF, filtration, or positive-count premise is used.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`,
  `ArrayProbSpace.reward_eq`, `SumRewards.sumRewards_eq`, and local
  `LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW` plus count/sum recursion APIs.
- Status: `leanCompiled`; focused module build and three external canaries pass.
- Failure policy: next-unused reward indexing and the pathwise prefix-source
  obligation are closed. The remaining `UCB-ARM-STREAM-SOURCE` work is the
  recursive source-faithful UCB action and canonical stationary/product stream
  measure law. Do not infer those laws or any one-sided tail, expected-pull, or
  regret theorem from this pathwise leaf.

## Arm-Stream Process And Product Law Leaf

- Leaf id: `UCB-ARM-STREAM-PROCESS-LAW`.
- Lean statements: `UCB.armStreamHistory`, `UCB.armStreamAction`,
  `UCB.armStreamReward`, the exact actual-history and post-initialization index
  equalities, measurable recursive history/action/reward coordinates,
  `UCB.armStreamMeasure`, and the actual-process peeling theorem.
- Local APIs/imports: `UCBArmStreamProcess`, reward source, native Real history
  index, finite-pair history extension, `Measure.infinitePi`, and the compiled
  fixed-count peeling endpoint.
- Proof route: recurse over inclusive histories, select round-robin arms before
  the native history index, read the next unused arm coordinate, prove equality
  with the extracted finite trace, and instantiate the double product law.
- Regularity contracts: `0 < K`; a Markov arm kernel is needed only for the
  measure; no MGF, filtration, or count positivity.
- Retrieval evidence: pinned LML `hist`, `action`, `reward`, `nextArm`,
  `ucbAlgorithm`, and `streamMeasure` at commit `19dc3ab...`, plus the local
  native-index, reward-source, and peeling leaves.
- Status: `leanCompiled`; focused and external history/coordinate canaries pass.
- Failure policy: pathwise recursion, recursive measurability, product law, and
  outer peeling are closed; expected-pull integration compiles downstream.

## Arm-Stream UCB Index Tail Leaf

- Leaf id: `UCB-ARM-STREAM-INDEX-TAIL` (`UCB-TAILS`).
- Lean statements: product coordinate laws, independent centered MGF transport,
  fixed-prefix and adaptive positive-count deviation bounds, width-threshold
  algebra, logarithmic finite-sum collapse, and the two
  `measure_*_rpow_bound` endpoints.
- Local APIs/imports: `UCBArmStreamTail`, `IndependenceFoundation`,
  `ConcentrationSubGaussian`, the process/source/peeling modules, and Mathlib
  Real/ENNReal rpow APIs.
- Proof route: apply fixed-sum sub-Gaussian bounds to every positive count
  fiber, peel the adaptive event, identify actual empirical-mean/random-width
  failures, simplify to `n * exp(-c*log(n+1))`, then dominate it by
  `1/(n+1)^(c-1)`.
- Regularity contracts: `0 < K`, Markov kernel, centered per-arm
  `HasSubgaussianMGF`, `0 <= c`, and nonzero variance proxy. The theorem uses
  ENNReal outer measure and does not hide recursive action measurability.
- Retrieval evidence: pinned LML `prob_ucbIndex_le/ge` at commit
  `19dc3ab...`, product independence, fixed-sum sub-Gaussian tails, and rpow
  algebra.
- Status: `leanCompiled`; focused build and inverse-power external canaries pass.
- Failure policy: source-faithful concentration is closed and consumed by the
  expected-count leaf; do not claim Real expectation or final regret yet.

## Arm-Stream UCB Expected Pull-Count Leaf

- Leaf id: `UCB-ARM-STREAM-EXPECTED-PULLCOUNT` (`UCB-EXPECTED-PULLCOUNT`).
- Lean statements:
  `UCB.lintegral_natCast_pullCount_armStreamAction_le_threshold_add_two_mul_constSum`
  and
  `UCB.integral_real_pullCount_armStreamAction_le_realThreshold_add_two_add_two_mul_constSum`.
- Local APIs/imports: `UCBArmStreamExpectedPullCount`, recursive action
  measurability, one-sided rpow tails, selected-small/large count split,
  finite ENNReal sums, cast-pull-count integrability, Mathlib
  `ofReal_integral_eq_lintegral_ofReal`, and probability-measure integration.
- Proof route: prove initial positive counts and argmax score comparison; turn
  good confidence into `gap <= 2*width`; derive the ceiling count threshold;
  include selected-large in the lower/upper failure union; apply two tail
  bounds, sum `2*indexTail`, integrate the pointwise split, prove integrability
  from `pullCount<=n`, and convert the finite ENNReal bound to Real.
- Regularity contracts: `0<K`, `0<c`, nonzero NNReal proxy, positive queried
  arm gap, Markov Real arm kernel, and centered MGF witnesses for the best and
  queried arms; no filtration, conditional expectation, or standard-Borel
  premise.
- Retrieval evidence: pinned LML `pullCount_arm_le`, `pullCount_le_add_three`,
  `constSum`, and `expectation_pullCount_le'` at commit `19dc3ab...`, plus local
  process/tail/count-split leaves.
- Status: `leanCompiled`; focused build and exact ENNReal/Real canaries pass.
- Failure policy: ENNReal and Real expected pull counts are closed and consumed
  by the final canonical regret theorem.

## Canonical Arm-Stream LML-Shaped UCB Regret Theorem

- Leaf id: `UCB-ARM-STREAM-LML-REGRET` (`UCB-FINAL`).
- Lean statement:
  `UCB.integral_realKernelRegret_armStreamAction_le_lml_sum`.
- Local APIs/imports: `UCBArmStreamExpectedPullCount`,
  `integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount`, finite-arm gap
  nonnegativity, `Finset.sum_le_sum`, and field normalization.
- Proof route: establish integrability for every pull count, rewrite expected
  regret as the gap-weighted sum, remove zero-gap terms, apply the positive-gap
  Real count bound, and rewrite `gap*realPullThreshold` to the inverse-gap term.
- Regularity contracts: `0<K`, `0<c`, nonzero common NNReal proxy, Markov Real
  arm kernel, and centered `HasSubgaussianMGF` witnesses for every arm; the
  canonical double product law supplies stationarity/independence.
- Retrieval evidence: exact pinned `Bandits.UCB.regret_le` and
  `expectation_pullCount_le` at commit `19dc3ab...`, the local expected-count
  leaf, and the Real kernel regret decomposition.
- Status: `leanCompiled`; exact RHS external canary passes.
- Failure policy: the canonical mathematical theorem route is closed. Literal
  upstream `IsAlgEnvSeq` symbol import remains separate cross-toolchain work;
  the explicit external action-law transport is compiled in the next leaf.

## External Action-Law UCB Regret Transport

- Leaf id: `UCB-EXTERNAL-ACTION-LAW-LML-REGRET`
  (`UCB-ISALGENVSEQ-LAW-TRANSPORT`).
- Lean statements: `UCB.measurable_armStreamActionTrace`,
  `UCB.measurable_realKernelRegret_actionTrace`, and
  `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStreamAction`.
- Local APIs/imports: `UCBArmStreamExpectedPullCount`,
  `measurable_pi_lambda`, `measurable_pi_apply`, `measurable_of_finite`,
  `realKernelRegret_eq_finset_sum_gap`, `IdentDistrib.comp`, and
  `IdentDistrib.integral_eq`.
- Proof route: prove the full canonical action trace and finite-horizon regret
  functional measurable, compose the complete action-trace law identity with
  regret, transport the Bochner integral, and invoke the canonical theorem.
- Regularity contracts: the canonical UCB assumptions plus complete
  `IdentDistrib` of the external and canonical action traces. No probability
  measure on the external space, timewise action measurability, separate
  integrability, reward process, filtration, or standard-Borel premise is
  added; `IdentDistrib` carries a.e. measurability.
- Retrieval evidence: pinned `Bandits.UCB.regret_le` and `IsAlgEnvSeq` route at
  commit `19dc3ab...`, Mathlib `Probability.IdentDistrib`, the canonical UCB
  final leaf, and the Real regret finite-sum identity.
- Status: `leanCompiled`; measurable-function and exact theorem canaries pass.
- Failure policy: external transport from an explicit complete action-law
  identity is closed. The faithful upstream route constructs it from an
  observable pair-trajectory law below; do not reopen concentration.

## External Latent Arm-Stream Source UCB Regret

- Leaf id: `UCB-EXTERNAL-ARM-STREAM-SOURCE-LAW-LML-REGRET`
  (`UCB-ISALGENVSEQ-ARM-STREAM-LAW-TRANSPORT`).
- Lean statements:
  `UCB.identDistrib_action_armStreamAction_of_identDistrib_armStream` and
  `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStream`.
- Local APIs/imports: `measurable_armStreamActionTrace`,
  `IdentDistrib.comp`, `IdentDistrib.of_ae_eq`, `IdentDistrib.trans`,
  `AEMeasurable.congr`, `Filter.EventuallyEq.symm`, and the compiled external
  action-law exact-regret theorem.
- Proof route: push the complete latent stream law through the measurable
  recursive UCB action, derive external action a.e. measurability from a.e.
  generated-action equality, replace the generated action, compose law
  identities, and invoke the exact action-law transport theorem.
- Regularity contracts: canonical UCB assumptions, complete latent
  `ArmRewardStream` law equal to `armStreamMeasure`, and a.e. equality of the
  external action with the recursive generated action. No external probability
  measure, separate stream/action measurability, reward trace, filtration,
  conditional expectation, or standard-Borel premise is added.
- Retrieval evidence: Mathlib `Probability.IdentDistrib`, the local process-law
  and external action-law leaves, and the fixed-count complete-stream transport
  pattern.
- Status: `leanCompiled`; law-constructor and exact-regret canaries pass.
- Failure policy: latent-stream-to-action law transport is closed as an
  optional stronger adapter. It is not the pinned `IsAlgEnvSeq` route and must
  not be required or inferred from selected feedback alone.

## External Action-Reward Trajectory UCB Regret Transport

- Leaf id: `UCB-EXTERNAL-ACTION-REWARD-TRAJECTORY-LAW-LML-REGRET`
  (`UCB-ISALGENVSEQ-TRAJECTORY-PROJECTION`).
- Lean statements:
  `UCB.identDistrib_action_of_identDistrib_actionRewardTrace` and
  `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_actionRewardTrace`.
- Local APIs/imports: `measurable_pi_lambda`, `measurable_pi_apply`,
  `measurable_fst`, `IdentDistrib.comp`, the external action-law theorem, and
  the canonical `armStreamAction/armStreamReward` process.
- Proof route: project a complete action/reward pair-trajectory law through the
  measurable coordinatewise `Prod.fst` map, simplify composition, then invoke
  the exact action-law regret transport.
- Regularity contracts: canonical UCB assumptions plus complete observable
  pair-trajectory `IdentDistrib`. No external probability instance, separate
  action/reward measurability, latent arm stream, unobserved-arm independence,
  filtration, conditional expectation, or standard-Borel premise is added at
  this projection layer.
- Retrieval evidence: pinned LML `IsAlgEnvSeq.identDistrib_trajectory` and
  `ArrayModel.isAlgEnvSeq_arrayMeasure` at commit `19dc3ab...`, from
  `SequentialLearning/IonescuTulceaSpace.lean` and
  `Online/Bandit/ArrayProbSpace.lean`, plus the compiled external action-law
  theorem.
- Status: `leanCompiled`; generic projection and exact-regret canaries pass.
- Failure policy: faithful pair-trajectory-to-regret transport is closed. The
  downstream common-`condDistrib` uniqueness theorem now derives the required
  pair-trajectory law, and the canonical specialization constructs its common
  law bundle internally. Remaining work is external initial/successor pair-law
  identification; do not reconstruct unused arm arrays or claim direct LML
  import.

## Common Conditional-Law UCB Regret Transport

- Leaf id: `UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET`
  (`UCB-TRAJECTORY-LAW-UNIQUENESS`,
  `UCB-ISALGENVSEQ-TRAJECTORY-UNIQUENESS`).
- Lean statements:
  `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`,
  `RewardKernel.identDistrib_rewardTrace_of_common_condDistrib`, and
  `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_common_actionReward_condDistrib`.
- Local APIs/imports: the compiled finite-prefix uniqueness theorem,
  `Finset.sup`, measurable finite restrictions,
  `Mathlib.Probability.Process.FiniteDimensionalLaws`,
  `MeasureTheory.IsProjectiveLimit.unique`, `IdentDistrib`, and the compiled
  observable-trajectory regret theorem.
- Proof route: embed every finite coordinate set into `Finset.Iic (I.sup id)`;
  transport its law from the corresponding prefix; identify external and
  canonical full laws as projective limits of the same finite marginals; then
  instantiate the coordinate as `Fin K x Real` and invoke exact regret
  transport.
- Regularity contracts: finite source measures, coordinatewise measurable
  traces, nonempty standard-Borel coordinates, a probability initial marginal,
  Markov successor kernels, and canonical UCB sub-Gaussian assumptions. The UCB
  wrapper exposes `[NeZero K]` solely to register `Nonempty (Fin K x Real)`
  while elaborating `condDistrib`; `hK : 0 < K` remains the mathematical arm
  nonemptiness premise. No latent unused-arm law, reconstructed independence,
  filtration, conditional expectation, or separate full-trajectory law is
  assumed.
- Retrieval evidence: Mathlib `FiniteDimensionalLaws` and `Projective`, the
  local finite-prefix theorem, and pinned LML
  `IsAlgEnvSeq.identDistrib_trajectory`/
  `ArrayModel.isAlgEnvSeq_arrayMeasure` at commit `19dc3ab...`.
- Status: `leanCompiled`; generic full-law declarations and the external exact
  UCB canary compile. The full-law uniqueness theorem is a Mathlib candidate.
- Failure policy: trajectory uniqueness from a shared initial/successor law
  bundle is closed. The downstream canonical-`condDistrib` specialization now
  constructs the common initial measure and kernels internally. Marginal-only
  laws and unused-arm reconstruction remain invalid substitutes.

## Canonical Conditional-Law UCB Regret Transport

- Leaf id: `UCB-CANONICAL-ACTION-REWARD-CONDDISTRIB-LML-REGRET`
  (`UCB-ISALGENVSEQ-CANONICAL-CONDDISTRIB-SPECIALIZATION`).
- Lean statements:
  `UCB.identDistrib_actionRewardTrace_of_condDistrib_eq_armStream` and
  `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_condDistrib_eq_armStream`.
- Local APIs/imports: `Measure.isProbabilityMeasure_map`, the
  `IsMarkovKernel` instance for `condDistrib`, canonical action/reward
  coordinate measurability, common-`condDistrib` trajectory uniqueness, and the
  observable-trajectory exact-regret theorem.
- Proof route: define the canonical pair process internally; use its time-zero
  pushforward as `mu0` and its regular conditional distributions as the common
  kernel family; discharge canonical law fields by reflexivity; pass external
  initial/successor equality to trajectory uniqueness; consume the resulting
  complete `IdentDistrib` in exact regret transport.
- Regularity contracts: finite external measure, timewise measurable external
  action/reward, `[NeZero K]` and `0<K`, a Markov arm kernel, canonical UCB
  sub-Gaussian assumptions, equality of initial pair pushforwards, and a.e.
  equality of each successor pair `condDistrib` under the external prefix law.
  No caller-supplied `mu0`, pair kernel, canonical law proof, latent unused-arm
  law, filtration, conditional expectation, or full trajectory-law premise is
  required.
- Retrieval evidence: Mathlib `Probability.Kernel.CondDistrib`,
  `Measure.isProbabilityMeasure_map`, local common-law uniqueness, and pinned
  LML `IsAlgEnvSeq.identDistrib_trajectory`/
  `ArrayModel.isAlgEnvSeq_arrayMeasure` at commit `19dc3ab...`.
- Status: `leanCompiled`; trajectory-law and exact-regret external canaries
  compile.
- Failure policy: canonical law-bundle construction and trajectory uniqueness
  are closed. The next source obligation is deriving the external initial pair
  pushforward equality and successor `condDistrib` equality from actual
  upstream `IsAlgEnvSeq` environment/action fields, or importing its literal
  trajectory witness. Reward marginals alone are insufficient.

## IsAlgEnvSeq Split-Law UCB Regret Transport

- Leaf id: `UCB-ISALGENVSEQ-SPLIT-LAWS-LML-REGRET`.
- Lean statements:
  `RewardKernel.pair_map_eq_compProd_of_map_eq_of_condDistrib`,
  `RewardKernel.condDistrib_pair_ae_eq_compProd_of_split`,
  `UCB.identDistrib_actionRewardTrace_of_split_condDistrib_eq_armStream`, and
  `UCB.integral_realKernelRegret_externalAction_le_lml_sum_of_split_condDistrib_eq_armStream`.
- Local APIs/imports: Mathlib `condDistrib_ae_eq_iff_measure_eq_compProd`,
  `Kernel.compProd`, `Measure.compProd_assoc'`, `MeasurableEquiv.prodAssoc`,
  `Measure.isProbabilityMeasure_map`, finite pair-history measurability, and
  the compiled common-law trajectory uniqueness theorem.
- Proof route: combine the initial action marginal and feedback conditional
  law into the initial pair law; combine each successor action policy and
  feedback-given-history/action kernel into a pair kernel; choose the canonical
  split kernels internally; identify complete observable trajectories; apply
  exact regret transport.
- Regularity contracts: finite external measure, measurable action/reward
  coordinates, standard-Borel/nonempty generic action and feedback targets,
  Markov split kernels, and the existing canonical UCB positivity and centered
  MGF assumptions. No independence, filtration, unused-arm array, preassembled
  pair law, or trajectory-law premise is required.
- Retrieval evidence: pinned LML `IsAlgEnvSeq.hasLaw_step_zero`,
  `hasCondDistrib_action`, `hasCondDistrib_feedback`, `stepKernel`, and
  `identDistrib_trajectory` at `19dc3ab...`; Mathlib CondDistrib/CompProd;
  compiled local common-law and canonical-law leaves. LML remains card-only.
- Status: `leanCompiled`; module compilation and external declaration canaries
  pass.
- Failure policy: split-to-joint composition and exact regret transport are
  closed. Next prove the four split fields from a concrete upstream sequence
  or resolve literal cross-toolchain import. Do not reconstruct unused-arm
  arrays or weaken the fields to reward marginals.

## Native Real UCB LML Field Compatibility

- Leaf id: `UCB-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET`.
- Lean statements: `UCB.RealStationaryUCBSequence`,
  `UCB.realStationaryUCBSequence_armStream`,
  `UCB.identDistrib_actionRewardTrace_of_realStationaryUCBSequence`, and
  `UCB.regret_le_of_realStationaryUCBSequence`.
- Local APIs/imports: `UCBArmStreamExpectedPullCount`, Mathlib measure/kernel
  conditional distributions and `IdentDistrib`, finite pair histories, and the
  compiled split-law exact-regret route.
- Proof route: package the six exact local consequences of pinned
  `IsAlgEnvSeq`; construct the canonical witness by measurability/reflexivity;
  project the fields into split-to-joint composition and trajectory uniqueness;
  consume the exact canonical regret theorem.
- Regularity contracts: finite external measure, `[NeZero K]`, `0<K`, Markov
  Real arm kernel, timewise measurable action/reward inside the structure,
  positive `c`, nonzero `sigma2`, and centered per-arm MGF witnesses. No
  `StandardBorelSpace Omega`, independence, filtration, unused-arm array,
  caller-supplied pair kernels, or preassembled trajectory law is required.
- Retrieval evidence: pinned LML `IsAlgEnvSeq` split fields, `stepKernel`,
  `identDistrib_trajectory`, `ArrayModel.isAlgEnvSeq_arrayMeasure`, and
  `Bandits.UCB.regret_le` at `19dc3ab...`; compiled local split-law route.
- Status: `leanCompiled`; canonical witness, trajectory, and exact-regret
  canaries compile through the project root.
- Failure policy: local mathematical field compatibility is closed. Remaining
  work is actual LML symbol/toolchain import or one separately defined concrete
  external producer. Do not reopen concentration or reconstruct unused arms.
