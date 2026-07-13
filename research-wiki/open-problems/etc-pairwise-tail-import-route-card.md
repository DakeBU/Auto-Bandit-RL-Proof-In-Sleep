# ETC Pairwise Tail Import Route Card

Status: theorem-card-only / import-route card.

Progress update:

- `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is compiled locally in
  `BanditRLProof.Algorithms.ETCPairwiseTailContract`.
- `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is compiled locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- `TAIL-SUBGAUSS-SUM` is compiled locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is compiled locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `TAIL-COND-SUBGAUSS` is compiled locally in
  `BanditRLProof.ConcentrationSubGaussian`; conditional reward-law
  instantiation is still open.
- `TAIL-UNION-FINITE` is compiled locally in
  `BanditRLProof.ProbabilityUnionBound` as reusable explicit-`Finset` and
  `[Fintype]` finite-union outer-measure wrappers.  It is a probability
  assembly tool, not a pairwise-tail producer.
- `MEAS-HISTORY` is compiled locally in
  `BanditRLProof.HistoryFiltration` as finite action/reward history product
  objects, finite trace-restriction maps, and coordinate measurability over
  `Finset.Iic` prefixes.
- `FILTRATION-HISTORY` is compiled locally in
  `BanditRLProof.HistoryFiltration`.
- `ADAPTED-ACTION` is compiled locally in
  `BanditRLProof.HistoryFiltration` as a countable/discrete past-coordinate
  measurability canary, with a reward-coordinate companion theorem.
- `MEAS-POLICY` is compiled locally in
  `BanditRLProof.PolicyMeasurability` as a measurable policy/state composition
  surface with arbitrary-filtration and generated-history-filtration
  specializations.
- `POLICY-GENERATED-ACTION-TRACE-MEASURABILITY` is compiled locally in
  `BanditRLProof.PolicyMeasurability`; applying a measurable policy to a
  time-indexed measurable state process now gives an action trace with
  ambient, arbitrary-filtration, and generated-history-filtration coordinate
  measurability.  Kernel-law and trajectory-law construction remain out of
  scope.
- `KERNEL-REWARD` is compiled locally in `BanditRLProof.RewardKernel` as a
  Mathlib-backed reward-kernel contract surface, including selected-measure
  probability and event-probability measurability wrappers for measurable
  context/action and policy/state lookup.  Kernel-bind and trajectory-law
  construction remain out of scope.
- `POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION` is compiled locally in
  `BanditRLProof.RewardKernel`; a measurable policy plus a context/action
  Markov reward kernel now yields a context/state Markov reward kernel with
  measurable event probabilities.  Finite-horizon trajectory-law construction
  remains out of scope.
- `POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` is compiled locally in
  `BanditRLProof.RewardKernel`; time-indexed measurable policies plus
  measurable context/state extractors from `Finset.Iic` reward histories now
  yield Mathlib `partialTraj` finite-prefix reward-history kernels.
- `KERNEL-POLICY-BIND` is compiled locally in `BanditRLProof.RewardKernel`;
  deterministic policy action kernels product with selected reward kernels to
  produce one-step `(Action × Reward)` kernels, and Mathlib `partialTraj`
  assembles finite-prefix action/reward pair trajectory kernels.  The one-step
  and history-step action/reward kernels now expose selected-reward marginal
  wrappers, and `RewardKernel.CenteredRewardKernelLaw` transfers centered
  integrability, zero-integral, and sub-Gaussian MGF witnesses through
  policy/history step kernels.  `condExpKernel` reward-law identification,
  posterior kernels, infinite trajectory laws, and final adaptive theorems
  remain out of scope.
- `ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`; it packages per-arm
  filtrations, strong adaptedness, zeroth `HasSubgaussianMGF`, later
  `HasCondSubgaussianMGF`, and tail domination to produce
  `ETC.PairwiseEmpMeanTailContract`.
- `ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY` is compiled locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`; it instantiates the
  fixed-commit centered-diff `StronglyAdapted` field for
  `History.historyFiltrationSucc` under timewise reward-coordinate
  measurability.
- `ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS` is compiled locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`; it gives
  zero-variance unconditional and conditional MGF witnesses when
  `actionWithCommit` pulls neither the comparison arm nor the best arm.
- `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is compiled locally in
  `BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail`.
- `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` is compiled locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` is compiled locally in
  `BanditRLProof.Algorithms.ETCSumRewardsDiff`.
- `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` is compiled locally in
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` is compiled locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail`.
- `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` is compiled locally in
  `BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail`.
- `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` is compiled locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` is compiled locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`.
- `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` is compiled locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`.
- `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` is compiled locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE` is compiled locally across
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE` is compiled locally across
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE` is compiled locally across
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`; it proves
  reward-only past independence from reward-coordinate `iIndepFun`, including
  an infinitePi specialization.
- `ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE` is compiled locally across
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`; it adds the
  deterministic fixed `actionWithCommit` action-history inclusion and full
  `History.historyFiltrationSucc` independence, including an infinitePi
  specialization.
- `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` is compiled locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND` is compiled
  locally in `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND` is compiled locally
  in `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT` is compiled locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
  `ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE` are compiled locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND` is compiled locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` is compiled locally in
  `BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`.
- `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` is compiled locally in
  `BanditRLProof.Algorithms.ETCExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` is compiled locally
  in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER` is compiled locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` is compiled
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER` is compiled locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY` is compiled
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` is compiled locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- The remaining route-card work is a deliberately small conditional route,
  not to define the
  action-matched contract surface,
  remove the common empirical-mean denominator, instantiate the fixed-horizon
  `sumRewards` comparison, specialize the abstract sub-Gaussian producer,
  package the witness fields, choose the canonical exponential tail, consume
  the canonical wrong-commit probability bound, or transfer trace-level reward
  independence/sub-Gaussianity through the centered-diff transform, or derive
  the exact-mean zero-integral side condition.  The next bridge should avoid
  treating the compiled lower-integral surrogate as final expected regret.

Decision source:

- Local dual-agent review:
  `reports/local_dual_review_after_concrete_argmax_decision_2026-06-30.md`
- Boundary before route card:
  `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`

## Leaf

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

## Exact Lean-Facing Statement Shape

Do not add this as a local Lean declaration until the Mathlib import route and
reward regularity contracts are fixed.  The route must produce the exact
non-best pairwise-tail hypothesis consumed by the compiled concrete argmax
probability wrapper.

Concrete future producer shape:

```lean
theorem ETC.pairwise_tail_empMeanAtExploration_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hreward_tail :
      ETC.PairwiseEmpMeanTailContract
        mu spec model commitArm reward tail)
    (a : Fin K)
    (hne : a = model.bestArm -> False) :
    mu {omega : Omega |
      ETC.empMeanAtExploration spec commitArm (reward omega) a >=
        ETC.empMeanAtExploration spec commitArm (reward omega) model.bestArm}
      <= tail a
```

The contract type `ETC.PairwiseEmpMeanTailContract` has now been introduced as
the compiled `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` leaf, and the independent
sub-Gaussian abstract producer is compiled as
`ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS`.  The next proof batch must instantiate
the concrete reward-difference bridge needed by that producer; alternative
future routes remain:

- an independent sub-Gaussian finite-sum contract;
- an adapted conditionally sub-Gaussian contract;
- a bounded Hoeffding contract; or
- a project-local abstract assumption surface around a Mathlib theorem.

The target consumer after the producer exists is:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

For concrete ETC empirical means, instantiate:

```lean
empMean := fun omega : Omega =>
  fun a : Fin K => ETC.empMeanAtExploration spec commitArm (reward omega) a
```

## Local APIs And Imports

Local APIs already available:

- `ETC.empMeanAtExploration`
- `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`
- `ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`
- `ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`
- `ETC.measurable_empMeanAtExploration_coordinates`
- `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`
- `ETC.PairwiseEmpMeanTailContract`
- `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`
- `ETC.argmaxCommitOracle`
- `ETC.argmaxCommitOracle_choose_spec`
- `Concentration.subGaussian_sum_tail_of_iIndepFun`
- `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`
- `ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`
- `ETC.centeredPairwiseRewardDiff`
- `ETC.centeredPairwiseGapThreshold`
- `ETC.sumRewards_le_imp_centered_pairwise_sum_ge`
- `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`
- `ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`
- `ETC.CenteredDiffSubGaussianWitnesses`
- `ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses`
- `ETC.centeredDiffSubGaussianTail`
- `ETC.centeredDiffSubGaussianWitnesses_of_indep_subG`
- `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`

Mathlib cards to inspect before implementation:

- `MLIB-PROBABILITY-SUBGAUSSIAN`
  - `Mathlib.Probability.Moments.SubGaussian`
  - candidate declarations recorded locally:
    `measure_sum_ge_le_of_iIndepFun`,
    `HasSubgaussianMGF`,
    `measure_sum_ge_le_of_HasCondSubgaussianMGF`
- `MLIB-PROBABILITY-INDEPENDENCE`
- `MLIB-CONDITIONAL-EXPECTATION`

## Intended Proof Route

1. Use the compiled
   `ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`
   adapter to reduce the pairwise event
   `empMean a >= empMean bestArm` to a future pointwise implication from
   fixed-horizon `sumRewards bestArm <= sumRewards a` into a real finite-sum
   tail event.
2. The pointwise implication is now compiled by
   `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`,
   supported by `ETC.sumRewards_le_imp_centered_pairwise_sum_ge`.
3. The canonical independent sub-Gaussian route is now packaged as
   `ETC.centeredDiffSubGaussianTail`,
   `ETC.centeredDiffSubGaussianWitnesses_of_indep_subG`, and
   `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`.  The next
   proof/import must supply the concrete `iIndepFun` and
   `HasSubgaussianMGF` witness fields for `ETC.centeredPairwiseRewardDiff`.
4. Choose exactly one tail theorem route:
   the independent sub-Gaussian sum wrapper is now available as
   `Concentration.subGaussian_sum_tail_of_iIndepFun`, and its ENNReal-valued
   boundary wrapper is available as
   `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`; the generic
   conditional sub-Gaussian route is now available as
    `Concentration.condSubGaussian_sum_tail_of_stronglyAdapted` and
    `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`, and
    the centered-diff conditional witness consumer is now available as
   `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`.
   Its fixed-commit shifted-history `StronglyAdapted` field is now available as
   `ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc`.
   Its zero-summand MGF source is now available as
   `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss`.
   Its sampled-arm MGF transfer is now available as
   `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm`
   and
   `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm`.
   Its reward-level conditional witness contract is now available as
   `ETC.CenteredRewardCondSubGaussianWitnesses` and
   `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`.
   Its independence-based centered-reward conditional MGF source is now
   available as `ETC.hasCondSubgaussianMGF_of_indep_comap` and
   `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`.
   Its independence-based centered-reward conditional mean-zero source is now
   available as `ETC.centeredReward_condExp_eq_zero_of_indep`,
   `ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep`,
   `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`,
   and
   `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`.
   The bounded-source succ-indexed conditional mean-zero wrapper is now
   available as
   `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`.
   The martingale-difference witness surface is now available as
   `MartingaleDiff.SuccMartingaleDifference` and
   `MartingaleDiff.SuccMartingaleDifferencePrefix`, with a Mathlib partial-sum
   wrapper
   `MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference`
   and the fixed `actionWithCommit` bounded-source centered-reward instance
   `ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource`.
   Its reward-only past independence bridge is now available as
   `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward`; its
   fixed-action full-history bridge is now available as
   `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`.
   Its fixed-action bounded/source assembly is now available as
   `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource`,
   `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian`,
   and
   `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`.
   Its canonical-tail no-`htail` form is now available as
   `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail`,
   `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail`,
   and
   `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`.
   Its infinitePi specialization is now available as
   `ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail`,
   `ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail`,
   and
   `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian`.
   Its finite action/reward history product-measurability surface is now
   available as `History.FiniteHistory` plus the `History.finite*OfTrace`
   measurability theorems.  Its finite-prefix reward-history Mathlib
   `partialTraj` surface is now available as
   `RewardKernel.partialTrajectoryKernel`.  Its finite-prefix action/reward
   pair trajectory surface is now available as
   `RewardKernel.actionRewardPartialTrajectoryKernel`.  It still needs
   conditional reward-law transfer and, for arbitrary policies, the remaining
   full predictability pieces.
5. Use the compiled
   `ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`
   producer once the concrete centered-diff independence/sub-Gaussian
   witnesses are available.
6. Only after the imported tail route compiles, instantiate the concrete
   argmax probability wrapper through
   `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`.

Historical route detail:

- Prove that pointwise implication by instantiating the abstract real
   summands with centered exploration reward-differences for arm `a` and
   `model.bestArm`.

## Regularity Contracts

- `[MeasurableSpace Omega]`
- `mu : MeasureTheory.Measure Omega`
- `[MeasureTheory.IsProbabilityMeasure mu]`
- `hK : 0 < K`
- `spec : ETC.Spec K`
- `model : FiniteBanditModel K`
- `reward : Omega -> RewardTrace Rat`
- finite exploration denominator positivity
- measurable reward coordinates
- either independence/sub-Gaussian assumptions or adapted conditional
  sub-Gaussian assumptions
- no final ETC regret theorem in this route card

## Retrieval Evidence

Current local declaration lookup includes:

```text
BanditRLProof.ETC.empMeanAtExploration
BanditRLProof.ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
BanditRLProof.ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
BanditRLProof.ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
BanditRLProof.ETC.measurable_empMeanAtExploration_coordinates
BanditRLProof.ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
BanditRLProof.ETC.PairwiseEmpMeanTailContract
BanditRLProof.ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
BanditRLProof.Concentration.subGaussian_sum_tail_of_iIndepFun
BanditRLProof.Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
BanditRLProof.Concentration.condSubGaussian_sum_tail_of_stronglyAdapted
BanditRLProof.Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
BanditRLProof.History.historyFiltration
BanditRLProof.History.measurableSet_action_mem_historyFiltration
BanditRLProof.History.measurableSet_reward_mem_historyFiltration
BanditRLProof.ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds
BanditRLProof.ETC.centeredPairwiseRewardDiff
BanditRLProof.ETC.centeredPairwiseGapThreshold
BanditRLProof.ETC.sumRewards_le_imp_centered_pairwise_sum_ge
BanditRLProof.ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event
BanditRLProof.ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds
BanditRLProof.ETC.CenteredDiffSubGaussianWitnesses
BanditRLProof.ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses
BanditRLProof.ETC.centeredDiffSubGaussianTail
BanditRLProof.ETC.centeredDiffSubGaussianWitnesses_of_indep_subG
BanditRLProof.ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG
```

Mathlib retrieval cards record:

```text
MLIB-PROBABILITY-SUBGAUSSIAN
MLIB-PROBABILITY-INDEPENDENCE
MLIB-CONDITIONAL-EXPECTATION
```

Canonical bounded-arm implementation evidence now also includes:

```text
ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq
BanditRLProof.History.historyFiltrationSucc_eq_of_action_eq_on_prefix
BanditRLProof.ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt
BanditRLProof.ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_boundedArmLaws
BanditRLProof.ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_boundedArmLaws
BanditRLProof.ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws
```

The downstream canonical expectation endpoint is also compiled as
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal`.
The downstream external exploration-prefix consumer is compiled as
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq`.
The downstream external conditional-law consumer is also compiled as
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_condDistrib`.
Its generic prefix induction derives the pushforward identity from the zeroth
marginal and successor `condDistrib` laws through exploration. The remaining
project-local kernel adapter is now compiled as
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib`:
the law contract states only the stationary law of each scheduled exploration
arm. The remaining law portion is a concrete source or `IsAlgEnvSeq` bridge,
not another canonical pairwise or Bochner wrapper. The compiled full-history
consumer now matches the LML feedback conditioning variable and coarsens a
constant law to reward prefixes. The action-dependent adapter now uses selector
a.e. equality to turn raw action-selected kernels into those constant laws,
closing the dependency-light seed-shaped law route. Exact LML alignment separately requires a Real/common-
sub-Gaussian/per-arm route.

## Status

`compiled-local` for the canonical bounded finite-arm `trajMeasure` route and
for external laws satisfying the explicit exploration-prefix equality;
`theorem-card-only` for deriving that equality from a general environment and
for the exact LML theorem.

The concrete local implementation is
`ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT`, ending at
`ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws`.
It uses exploration-prefix action/filtration equality and the existing
conditional centered-diff consumer, and has compiled through:

```bash
python3 tools/bandit.py check
```

## Failure Policy

If extending beyond the canonical bounded arm-law trajectory, do not reuse its
prefix filtration equality without proving the target environment law. Split
the route into explicit law transport, measurability/integrability, and regret
assembly leaves. The common-denominator comparison
leaf is already compiled as `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM`; the next
tail import wrappers are already compiled as `TAIL-SUBGAUSS-SUM` and
`TAIL-SUBGAUSS-DIFF-SUM-IMPORT`, the abstract sub-Gaussian contract producer is
compiled as `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS`, the generic event-shape
adapter is compiled as `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT`, the
concrete centered-diff Finset bridge is compiled as
`ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`, the producer specialization is compiled
as `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF`, and the concrete witness target
is packaged as `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT`; the canonical
tail helper is compiled as `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL`, and
the canonical wrong-commit probability consumer is compiled as
`ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND`; the deterministic
independence transfer from trace-level reward-coordinate independence is
compiled as `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS`; the deterministic
sub-Gaussian transfer from per-time centered reward witnesses is compiled as
`ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS`; and the reward-coordinate-law
wrong-commit probability theorem is compiled as
`ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND`; the bounded reward
Hoeffding-lemma source is compiled as
`ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE`; the bounded-to-integrable
source is compiled as
`ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE`; and the bounded-reward
zero-integral source is compiled as
`ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE`; and the bounded-reward
wrong-commit probability theorem is compiled as
`ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND`; the action-matched
wrong-commit probability theorem is compiled as
`ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND`; and the
action-matched source contract is compiled as
`ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT`; the fixed product-coordinate source
and direct wrong-commit probability theorem are compiled as
`ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
`ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE`.
The next split should prove/import a source for one of:

- `ETC-FIXED-COMMIT-WRONG-COMMIT-TO-EXPECTED-REGRET`
- `ETC-ARGMAX-COMMIT-TRACE-REGRET-ASSEMBLY`
- `ETC-CENTERED-DIFF-SAMPLED-ARM-CONDITIONAL-MGF-SOURCE`

Do not pivot in the same batch to a full Hoeffding proof, filtration/history
implementation, conditional expectation development, UCB, Thompson sampling,
EXP3/Tsallis/OFUL/RL, or a final ETC theorem.

## Per-Arm Assembly Update

`ETC-PER-ARM-COMMIT-PROB-BOCHNER-ASSEMBLY` is now compiled. The expected suffix
cost is a finite sum of `gap a` times the probability of the concrete commit
fiber, so the route no longer needs a max-gap union assembly. The armwise event
inclusion and canonical ENNReal probability bound are now compiled as
`ETC-FINITE-ARM-BOUNDED-COMMIT-ARM-PAIRWISE-TAIL`. The current pairwise tail
contract remains the one-sided fixed-horizon source. Finite ENNReal-to-Real
conversion and termwise substitution now compile as
`ETC-FINITE-ARM-BOUNDED-CANONICAL-PER-ARM-BOCHNER-REGRET`; the best-arm term
vanishes and no arm union is taken. External exploration-prefix transport now
compiles as
`ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-PER-ARM-BOCHNER-REGRET`, requiring
only equality of the finite prefix pushforwards. Initial and successor
conditional laws now derive that identity in
`ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`. The
stationary scheduled-arm replacement now compiles as
`ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`;
the LML-shaped full action/reward-history constant-law coarsening now compiles
as `ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
Action-selected feedback kernels and a.e. scheduled actions now convert to
those constant laws in
`ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
The dependency-light bounded law chain is closed. Direct common-proxy arm MGFs
now also compile through the canonical pairwise empirical-mean tail contract,
without bounded support. Concrete commit-fiber bounds, finite Real tails, and
the canonical gap-weighted per-arm Bochner theorem now compile downstream.
External exploration-prefix equality, generic initial/successor conditional-
law transport, the scheduled exploration-arm endpoint, and the LML-shaped
full action/reward-history constant-law consumer and its action-dependent
selected-kernel adapter now compile as well. Dependency-light direct-MGF `Rat`
law transport is closed. The downstream native Real product theorem,
finite-prefix integral transport, scheduled initial/successor `condDistrib`
exact-regret endpoint, and upstream-shaped selected feedback-law adapter now
compile. The downstream least-encoded selector and action assembly also
compile, including source-shaped history-score mapping and a faithful local
bundle of the LML sequence fields. The remaining route is only a true
cross-toolchain import over the actual LML symbols; do not reopen this tail-
import route.
