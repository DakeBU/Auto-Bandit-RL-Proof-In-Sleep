# ABRL Project Overview And Next Plan

## Purpose

ABRL, short for Auto-Lean-in-Sleep: Bandit and RL Proofs, is a Lean 4 proof
library plus a plain-file multi-agent harness for formalizing bandit and
reinforcement-learning theory.

The intended pipeline is:

```text
literature theorem or new proof target
-> theorem card and assumption ledger
-> exact Lean-facing statement
-> small proof-DAG leaves
-> compiled Lean certificate
-> synchronized Markdown and LaTeX explanation
-> reusable memory for the next theorem
```

The main rule is that natural-language sketches, source cards, theorem cards,
and proof weapons are not completed proofs.  A result becomes certified local
memory only after the relevant Lean declarations compile through the repository
gate:

```bash
python3 tools/bandit.py check
```

That gate is intended to run:

```bash
lake build
lake build Tests
```

and then scan for placeholders such as `sorry`, `admit`, `axiom`, and
`postulate`.

## Current Local Reality

The current local checkout is an early proof-engineering skeleton, not a
complete textbook-scale bandit/RL theorem library.

Already present:

- a Lean package with Mathlib pinned through Lake;
- core finite-bandit vocabulary;
- recursive definitions for pull counts, reward sums, finite-arm mean models,
  gaps, and pseudo-regret;
- compiled best-arm dominance and model-gap nonnegativity invariants for the
  local finite-bandit model;
- a first set of compiled finite-bookkeeping leaves;
- Mathlib-backed `Finset.range` wrappers for pull counts, selected reward
  sums, and pseudo-regret;
- a deterministic regret decomposition into an arm-indexed sum of
  `gap * pullCount`;
- deterministic Rat/Nat count-bound-to-regret scaffolds;
- Bochner and ENNReal expectation/pull-count/regret bridge leaves;
- measure, finite-history, history-filtration finite-pair/comap alignment,
  policy-measurability,
  reward-kernel, finite-prefix `partialTraj`, and conditional-expectation
  bridge surfaces;
- independent and strongly adapted conditional sub-Gaussian tail wrappers;
- a deterministic finite-action EXP3 potential surface with exponential-weight
  updates, nonnegativity, one-step increment algebra, and finite-horizon
  telescoping;
- a deterministic full-information exponential-weights/Hedge theorem with a
  second-order comparator bound and the `[0,1]` endpoint
  `log |A| / eta + eta*T`;
- a generic finite-action FTRL one-step minimizer wrapper over an explicit
  feasible predicate or finite-simplex predicate;
- a finite-simplex Tsallis power-sum/entropy/negative-entropy regularizer
  surface with `Real.rpow` and denominator well-definedness facts;
- local exact/stationary final theorem routes for Explore-Then-Commit, UCB, and
  Thompson sampling, with literal upstream LML imports kept separate;
- task packets, proof obligations, conversion windows, research cards, and run
  logs.

Still missing or only carded:

- polished textbook-facing expectation APIs beyond the compiled bridge leaves;
- ambient trajectory-to-`condExpKernel` law identification, full adaptive
  policy predictability, posterior kernels, and full conditional-expectation
  contracts;
- Hoeffding/Chernoff and theorem-specific martingale tail instantiations
  beyond the compiled sub-Gaussian and Chebyshev/variance wrappers;
- optional-stopping/resource-feasibility/BwK routes beyond the compiled
  budget-exhaustion hitting-time wrapper;
- literal cross-toolchain imports of the upstream LML UCB/ETC/Thompson symbols
  and broader nonstationary/contextual adapters beyond the compiled local
  theorem routes;
- complete EXP3 bandit regret, Tsallis-INF/FTRL, OFUL/LinUCB, BwK, or
  finite-horizon RL theorem proofs;
- proof exports for closed textbook theorems.

The requested unfinished-work workflow is now available:

- `python3 tools/bandit.py unfinished` lists unfinished proof leaves and backlog
  rows.
- `docs/collaborator_unfinished_work_guide.md` explains the one-leaf workflow.
- `PULLCOUNT-LIST-RANGE`, `SUMREWARDS-LIST-RANGE`,
  `SUMREWARDS-LIST-FILTER`, and `PSEUDOREGRET-LIST-RANGE` are compiled local
  dependency-light bridges after the Lean gate passes.
- `PULLCOUNT-FINSET` is compiled locally as
  `pullCount_eq_finset_filter_card` in `BanditRLProof.MathlibWrappers`.
- `SUMREWARDS-FINSET` is compiled locally as
  `sumRewards_eq_finset_filter_sum` in `BanditRLProof.MathlibWrappers`.
- `PSEUDOREGRET-FINSET` is compiled locally as
  `pseudoRegret_eq_finset_sum` in `BanditRLProof.MathlibWrappers`.
- `ETC-EXPLOREARM-EQ-IFF-MOD` is compiled locally as
  `ETC.exploreArm_eq_iff_mod_eq_val` in `BanditRLProof.Algorithms.ETC`.
- `REGRET-PULLCOUNT` is compiled locally as
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount` in
  `BanditRLProof.RegretDecomposition`.
- `REGRET-COUNT-BOUND` is compiled locally as
  `pseudoRegret_le_finset_sum_gap_mul_count_bound` in
  `BanditRLProof.RegretCountBounds`.
- `REGRET-NAT-COUNT-BOUND` is compiled locally as
  `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound` in
  `BanditRLProof.RegretCountBounds`.
- `REGRET-UNIFORM-NAT-COUNT-BOUND` is compiled locally as
  `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound` in
  `BanditRLProof.RegretCountBounds`.
- `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_K_eq_one` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-ROUND-ROBIN-ADD-K-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_add_K_eq_add_one` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-ROUND-ROBIN-MUL-K-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_mul_K_eq` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_explorationPulls_mul_K_eq` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-EXPLORATION-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` is compiled
  locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` is compiled locally as
  `ETC.actionWithCommit_eq_exploreArm_of_lt` in
  `BanditRLProof.Algorithms.ETCTrace`.
- `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` is compiled locally as
  `ETC.actionWithCommit_eq_commitArm_of_ge` in
  `BanditRLProof.Algorithms.ETCTrace`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` is compiled locally as
  `ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le`
  in `BanditRLProof.Algorithms.ETCTrace`.
- `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `PULLCOUNT-SUM-TIME` is compiled locally as
  `finset_sum_pullCount_eq_time` in
  `BanditRLProof.PullCountDecomposition`.
- `MEAS-FIN-ACTION` is compiled locally as
  `measurableSet_actionTrace_eval_eq` in
  `BanditRLProof.MeasureFoundation`.
- `MEAS-PULL-INDICATOR` is compiled locally as
  `measurable_actionTrace_eval_eq_indicator_const` in
  `BanditRLProof.MeasureFoundation`.
- `MEAS-REWARD` is compiled locally as
  `measurable_actionTrace_eval_eq_indicator_reward` in
  `BanditRLProof.MeasureFoundation`.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource`,
  a source-projection wrapper exposing the packaged practical base
  raw-range/measurable-mean-range bounded source from a uniform-variance
  source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the explicit
  generated random-pair map source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  is compiled locally as
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`,
  a source-consumer wrapper lowering the packaged uniform-variance source
  through its generated random-pair map source into the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the weaker
  definitional generated actual-action reward-coordinate source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the explicit
  generated actual-action reward-map source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the definitional
  centered-source interface.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the bounded
  centered-source interface.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its bounded centered-source projection into the integrability-based
  centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`,
  a source-projection wrapper exposing the packaged practical base
  raw-range/measurable-mean-range bounded source from a selected-history
  variance source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  explicit generated random-pair map source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  generated full finite-pair `partialTraj` source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  is compiled locally as
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`,
  a source-consumer wrapper lowering the packaged selected-history-variance
  source through its generated random-pair map source into the canonical
  history-step next-pair law.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  weaker definitional generated actual-action reward-coordinate source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  explicit generated actual-action reward-map source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  bounded centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its bounded centered-source projection into the
  integrability-based centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  definitional centered-source interface.
- `MEAS-HISTORY` is compiled locally as finite action/reward history product
  objects, trace-restriction maps, and coordinate measurability over
  `Finset.Iic` prefixes in `BanditRLProof.HistoryFiltration`; it now also
  exposes pair-coordinate finite trace prefixes and measurable reward
  projection from finite `(Action, Reward)` pair histories, plus the
  measurable successor-extension map for appending one next pair.
- `MEAS-SELECTED-REWARD-FINITE-SUM` is compiled locally as
  `measurable_finset_sum_indicator_reward` in
  `BanditRLProof.MeasurableSums`.
- `MEAS-SUMREWARDS` is compiled locally as
  `measurable_sumRewards` in
  `BanditRLProof.MeasurableLocalQuantities`.
- `MEAS-REGRET` is compiled locally as
  `measurable_pseudoRegret` in
  `BanditRLProof.MeasurableRegret`.
- `MEAS-PULLCOUNT` is compiled locally as
  `measurable_pullCount` in
  `BanditRLProof.MeasurablePullCount`.
- `MEAS-PULLCOUNT-CAST` is compiled locally as
  `measurable_natCast_pullCount` in
  `BanditRLProof.MeasurablePullCountCast`.
- `INT-FINITE-SUM` is compiled locally as
  `IntegrabilitySums.integrable_finset_sum` and
  `IntegrabilitySums.integrable_univ_sum` in
  `BanditRLProof.IntegrabilitySums`.
- `EXP-FINITE-SUM` is compiled locally as
  `ExpectationBochnerSums.integral_finset_sum` and
  `ExpectationBochnerSums.integral_univ_sum` in
  `BanditRLProof.ExpectationBochnerSums`.
- `EXP-REGRET-PULLCOUNT` is compiled locally as
  `integrable_real_pseudoRegret_of_integrable_pullCount` and
  `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount` in
  `BanditRLProof.ExpectationRegretPullCount`; this is the Real-valued Bochner
  decomposition, not a Rat-valued expectation theorem or final algorithmic
  regret theorem.
- `EXP-INDICATOR-PULL` is compiled locally as
  `lintegral_actionTrace_eval_eq_indicator_one` in
  `BanditRLProof.ExpectationFoundation`.
- `EXP-FINSET-INDICATOR-PULL` is compiled locally as
  `lintegral_finset_sum_actionTrace_eval_eq_indicator_one` in
  `BanditRLProof.ExpectationSums`.
- `EXP-PULLCOUNT-LINTEGRAL` is compiled locally as
  `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq` in
  `BanditRLProof.ExpectationPullCount`.
- `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` is compiled locally as
  `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` in
  `BanditRLProof.ExpectationWeightedPullCount`.
- `EXP-PULLCOUNT-LE-TIME` is compiled locally as
  `lintegral_natCast_pullCount_le_time` in
  `BanditRLProof.ExpectationPullCountBounds`.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME` is compiled locally as
  `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` in
  `BanditRLProof.ExpectationWeightedPullCountBounds`.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` is compiled locally as
  `lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` in
  `BanditRLProof.ExpectationFiniteBanditBounds`.
- `EXP-MODEL-GAP-OFREAL-BOUND` is compiled locally as
  `lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time`
  in `BanditRLProof.ExpectationFiniteBanditModelBounds`.
- `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` is compiled locally as
  `ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg` in
  `BanditRLProof.ScalarENNReal`.
- `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` is compiled locally as
  `ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`
  in `BanditRLProof.ScalarPseudoRegret`.
- `EXP-OFREAL-PSEUDOREGRET-BOUND` is compiled locally as
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`
  in `BanditRLProof.ExpectationPseudoRegretOfRealBounds`.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` is compiled locally as
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`
  in `BanditRLProof.ExpectationPseudoRegretRatBounds`.
- `FINITE-BANDIT-GAP-BESTARM` is compiled locally as
  `FiniteBanditModel.gap_bestArm` in `BanditRLProof.Core`.
- `FINITE-BANDIT-BESTARM-DOMINATES` is compiled locally as
  `FiniteBanditModel.mean_le_bestArm_mean` in
  `BanditRLProof.FiniteBanditModelInvariants`.
- `FINITE-BANDIT-GAP-NONNEG` is compiled locally as
  `FiniteBanditModel.gap_nonneg` in
  `BanditRLProof.FiniteBanditModelInvariants`.
- `FINITE-BANDIT-MAXGAP`, `FINITE-BANDIT-GAP-LE-MAXGAP`, and
  `FINITE-BANDIT-MAXGAP-NONNEG` are compiled locally as
  `FiniteBanditModel.maxGap`, `FiniteBanditModel.gap_le_maxGap`, and
  `FiniteBanditModel.maxGap_nonneg` in
  `BanditRLProof.FiniteBanditModelInvariants`.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` is compiled locally as
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time`
  in `BanditRLProof.ExpectationPseudoRegretRatBounds`.

## Main Content Structure

### Lean Library

- `BanditRLProof/Core.lean`: core finite-bandit vocabulary.
  - `ActionTrace`
  - `RewardTrace`
  - `pullCount`
  - `sumRewards`
  - `FiniteBanditModel`
  - `bestArm`
  - `bestMean`
  - `gap`
  - `FiniteBanditModel.gap_bestArm`
  - `PolicySketch`
  - `CertificateStatus`

- `BanditRLProof/FiniteBanditModelInvariants.lean`: model-semantic
  invariants for the local finite-bandit selector.
  - `FiniteBanditModel.mean_le_bestArm_mean`
  - `FiniteBanditModel.gap_nonneg`
  - `FiniteBanditModel.maxGap`
  - `FiniteBanditModel.gap_le_maxGap`
  - `FiniteBanditModel.maxGap_nonneg`

- `BanditRLProof/Regret.lean`: regret-facing surfaces.
  - `pseudoRegret`
  - `RegretBoundCard`
  - `RegretObligation`

- `BanditRLProof/LeafLemmas.lean`: currently compiled dependency-light leaves.
  - pull-count update lemmas;
  - pull-count monotonicity and upper bounds;
  - zero/count segment lemmas;
  - reward-sum segment lemmas;
  - pseudo-regret zero and segment-stability lemmas.

- `BanditRLProof/MathlibWrappers.lean`: first Mathlib interop layer.
  - `pullCount_eq_finset_filter_card`;
  - `sumRewards_eq_finset_filter_sum`;
  - `pseudoRegret_eq_finset_sum`;
  - imports `Mathlib.Data.Finset.Card`;
  - imports `Mathlib.Algebra.BigOperators.Group.Finset.Basic` and
    `Mathlib.Algebra.Field.Rat` for `Finset.sum` over `Rat`;
  - uses `Finset.range_add_one`, `Finset.filter_insert`, and
    `Finset.sum_range_succ`.

- `BanditRLProof/RegretDecomposition.lean`: deterministic regret consumer
  leaves.
  - `pseudoRegret_eq_finset_sum_gap_mul_pullCount`;
  - imports `Mathlib.Data.Fintype.Basic` and `Mathlib.Data.Nat.Cast.Basic`;
  - uses `Finset.sum_fiberwise'`, `Finset.sum_const`, and `nsmul_eq_mul'`.

- `BanditRLProof/RegretCountBounds.lean`: deterministic count-bound-to-regret
  scaffolds.
  - `pseudoRegret_le_finset_sum_gap_mul_count_bound`;
  - `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`;
  - `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound`;
  - imports ordered finite-sum and ordered Rat APIs;
  - uses `pseudoRegret_eq_finset_sum_gap_mul_pullCount`,
    `FiniteBanditModel.gap_nonneg`, `Finset.sum_le_sum`, and
    `mul_le_mul_of_nonneg_left`.

- `BanditRLProof/PullCountDecomposition.lean`: deterministic finite-action
  count partition leaves.
  - `finset_sum_pullCount_eq_time`;
  - imports `Mathlib.Data.Fintype.Basic`;
  - uses `pullCount_eq_finset_filter_card` and
    `Finset.card_eq_sum_card_fiberwise`.

- `BanditRLProof/MeasureFoundation.lean`: first probability-facing
  measurability canaries.
  - `measurableSet_actionTrace_eval_eq`;
  - `measurable_actionTrace_eval_eq_indicator_const`;
  - `measurable_actionTrace_eval_eq_indicator_reward`;
  - imports `Mathlib.MeasureTheory.MeasurableSpace.Basic`;
  - uses `MeasurableSet.singleton`, measurable preimages,
    `measurable_const`, reward-evaluation measurability hypotheses, and
    `Measurable.indicator`.

- `BanditRLProof/MeasurableSums.lean`: finite-sum measurability bridge for
  selected-reward indicator contributions.
  - `measurable_finset_sum_indicator_reward`;
  - imports `Mathlib.MeasureTheory.Group.Arithmetic`;
  - uses `Finset.induction_on`, `Finset.sum_insert`, and `Measurable.add`.

- `BanditRLProof/MeasurableLocalQuantities.lean`: measurability bridge from
  selected-reward finite sums to local recursive quantities.
  - `measurable_sumRewards`;
  - imports `Mathlib.Algebra.BigOperators.Group.Finset.Indicator`;
  - uses `sumRewards_eq_finset_filter_sum`,
    `Finset.sum_indicator_eq_sum_filter`, and
    `measurable_finset_sum_indicator_reward`.

- `BanditRLProof/MeasurableRegret.lean`: pseudo-regret random-variable
  measurability bridge before expectation.
  - `measurable_pseudoRegret`;
  - imports `Mathlib.Data.Fintype.Basic` and
    `Mathlib.MeasureTheory.Group.Arithmetic`;
  - uses `measurable_of_finite`, `Measurable.comp`, finite-set induction, and
    `pseudoRegret_eq_finset_sum`.

- `BanditRLProof/MeasurablePullCount.lean`: pull-count random-variable
  measurability bridge before expected pull-count identities.
  - `measurable_pullCount`;
  - imports `Mathlib.MeasureTheory.Group.Arithmetic`;
  - uses `measurableSet_actionTrace_eval_eq`, `Measurable.ite`,
    `Measurable.add`, and `pullCount_succ`.

- `BanditRLProof/MeasurablePullCountCast.lean`: scalar-casted pull-count
  measurability bridge before expected pull-count identities.
  - `measurable_natCast_pullCount`;
  - imports `Mathlib.Data.Nat.Cast.Basic`;
  - uses scalar induction, `Measurable.ite`, `Measurable.add`, and
    `pullCount_succ`.

- `BanditRLProof/ExpectationFoundation.lean`: first lower-integral canary for
  action-event indicators.
  - `lintegral_actionTrace_eval_eq_indicator_one`;
  - imports `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`;
  - uses `MeasureTheory.lintegral_indicator_one` and
    `measurableSet_actionTrace_eval_eq`.

- `BanditRLProof/ExpectationSums.lean`: lower-integral finite-sum bridge for
  action-event indicators.
  - `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`;
  - imports `Mathlib.MeasureTheory.Integral.Lebesgue.Add`;
  - uses `MeasureTheory.lintegral_finset_sum`,
    `measurable_actionTrace_eval_eq_indicator_const`, and
    `lintegral_actionTrace_eval_eq_indicator_one`.

- `BanditRLProof/ExpectationPullCount.lean`: lower-integral pull-count identity.
  - `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`;
  - imports `Mathlib.Data.Nat.Cast.Basic`;
  - uses `pullCount_succ`, `Finset.sum_range_succ`, and
    `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`.

- `BanditRLProof/ExpectationRegretPullCount.lean`: Bochner/Real expected-regret
  decomposition into finite gap-weighted expected pull counts.
  - `integrable_real_pseudoRegret_of_integrable_pullCount`;
  - `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount`;
  - imports `Mathlib.MeasureTheory.Integral.Bochner.Basic`,
    `BanditRLProof.ExpectationBochnerSums`, and
    `BanditRLProof.RegretDecomposition`;
  - uses the deterministic `pseudoRegret_eq_finset_sum_gap_mul_pullCount`,
    `ExpectationBochnerSums.integral_univ_sum`, `Integrable.const_mul`, and
    `MeasureTheory.integral_const_mul`.

- `BanditRLProof/ConditionalExpectationReward.lean`: narrow
  `condExpKernel`-to-`condExp` zero bridge and explicit history-step
  integral/map-law consumers for centered reward variables.
  - `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero`;
  - `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq`;
  - `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq`;
  - `ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen`;
  - `ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet`;
  - `ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable`;
  - `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable`;
  - `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable`;
  - `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc`;
  - `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable`;
  - `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable`;
  - `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc`;
  - `ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen`;
  - `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc`;
  - `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk`;
  - `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`;
  - `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq`;
  - `Policy.generatedActionTraceSucc`;
  - `Policy.generatedActionTraceSucc_succ_eq`;
  - `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc`;
  - `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq`;
  - `ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq`;
  - `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq`;
  - `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - imports `Mathlib.Probability.Independence.Conditional` and
    `BanditRLProof.RewardKernel`;
  - uses `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel` and
    `MeasureTheory.ae_eq_of_ae_eq_trim`, plus
    `RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero`
    and Mathlib `integral_map`, `condExpKernel_ae_eq_trim_condExp`,
    `condExp_of_stronglyMeasurable`, `ae_all_iff`, and
    `mem_ae_iff_prob_eq_one`, plus `measurable_pi_lambda`,
    `History.measurable_reward_mem_historyFiltration_of_lt`,
    `History.measurable_action_mem_historyFiltration_of_lt`, and
    `Measure.map_congr` plus
    `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply`
    and `RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply`;
    it consumes but does not construct the trajectory-law conditional-kernel
    identification.

- `BanditRLProof/Algorithms/ETC.lean`: Explore-Then-Commit interface and
  obligation names.

- `BanditRLProof/Algorithms/ETCTrace.lean`: fixed-commit ETC phase-switching
  trace boundary for exploration and commit phases.

- `BanditRLProof/Algorithms/ETCTraceCountLemmas.lean`: deterministic
  pull-count transfer facts for the fixed-commit ETC trace.

- `BanditRLProof/Algorithms/UCB.lean`: UCB interface, index-state surface, and
  obligation names.

- `BanditRLProof/Algorithms/Thompson.lean`: Thompson sampling and Bayesian
  regret obligation names, a posterior-action identity ledger, and a compiled
  Mathlib `condDistrib` transport theorem for the probability-matching route.

- `BanditRLProof/Algorithms/ThompsonCanonicalSampler.lean`: canonical
  prior-likelihood-posterior one-step sampler, marginal transports, and a
  premise-free Thompson probability-matching theorem.

- `BanditRLProof/Algorithms/ThompsonReferencePolicy.lean`: fixed-reference
  posterior policy, `compProd` action sampler, posterior-preservation transport,
  and finite action/reward-prefix probability matching from posterior
  invariance.

- `BanditRLProof/Algorithms/ThompsonAlgorithmDensity.lean`: common-history
  density law source, base-density/`compProd` commutation, posterior invariance,
  and generic plus finite-prefix reference-policy probability matching from
  marginal/joint change-of-algorithm laws.

- `BanditRLProof/Algorithms/ThompsonBayesRegretDecomposition.lean`:
  measurable history/action score interface, conditional-law score-expectation
  transport, initial best-action marginal identification, and the exact
  finite-horizon Bayesian mean-regret decomposition on the actual recursive
  uniform-reference Thompson trajectory.

- `BanditRLProof/Algorithms/ThompsonClippedUCBScore.lean`: the pinned LML
  zero-pull/clipped empirical-mean score on finite pair histories, measurable
  `[l,u]` bounds, history-to-trace transport, automatic score/mean
  integrability, and the concrete actual-trajectory Bayesian-regret
  decomposition.

- `BanditRLProof/Algorithms/ThompsonStationaryReward.lean`: measurable
  stationary reward-kernel sampling into an independent latent arm stream,
  arbitrary-action adaptive-count sub-Gaussian tails, and deterministic
  next-unused feedback for the Thompson trajectory transport route.

- `BanditRLProof/Literature.lean`: LML theorem-card registry.

- `BanditRLProof/Automation.lean`: harness/task/gate types.

- `BanditRLProof/OpenProblems.lean`: open problem registry.

### Workflow And Memory

- `tasks/`: task packets such as `BRL-UCB-PORT-001`,
  `BRL-ETC-PORT-001`, `BRL-TS-BAYES-001`, and
  `BRL-OP-RL-BELLMAN-001`.
- `proof-obligations/`: task-local leaf ledgers.
- `conversion-windows/`: mappings between paper/theorem-card prose and local
  Lean surfaces.
- `proof-blueprints/`: generated snapshots that combine task context,
  obligations, retrieval cards, and local declarations.
- `research-wiki/`: theorem cards, paper cards, Mathlib routes, proof
  techniques, scenario taxonomy, and open problems.
- `runs/`: prompt decks, run logs, handoff notes, and trial summaries.
- `tools/bandit.py`: plain-file CLI for task creation, memory refresh,
  blueprint refresh, retrieval, declaration search, proof export, run-cycle
  prompt generation, and checks.

## Why Not Start With A Broad Theorem

Broad goals such as "prove UCB regret", "formalize Tsallis-INF", or "build the
RL Bellman theory" currently depend on many missing layers at once:

- finite-sum bridges;
- probability and measure theory imports;
- measurability and integrability contracts;
- concentration inequalities;
- algorithm-specific algebra;
- final regret decomposition.

Starting there would likely produce more planning prose instead of a compiled
Lean result.  The repository's own design says lower work should target exactly
one small unfinished leaf at a time.

## Recommended Next Step

The deterministic dependency-light baseline is now closed:

```text
PULLCOUNT-LIST-RANGE       compiled-local
SUMREWARDS-LIST-RANGE      compiled-local
SUMREWARDS-LIST-FILTER     compiled-local
PSEUDOREGRET-LIST-RANGE    compiled-local
ETC-EXPLOREARM-ADD-K       compiled-local
ETC-EXPLOREARM-EQ-IFF-MOD  compiled-local
PULLCOUNT-FINSET           compiled-local
SUMREWARDS-FINSET          compiled-local
PSEUDOREGRET-FINSET        compiled-local
REGRET-PULLCOUNT           compiled-local
REGRET-COUNT-BOUND         compiled-local
REGRET-NAT-COUNT-BOUND     compiled-local
REGRET-UNIFORM-NAT-COUNT-BOUND compiled-local
ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT compiled-local
ETC-ROUND-ROBIN-ADD-K-COUNT compiled-local
ETC-ROUND-ROBIN-MUL-K-COUNT compiled-local
ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT compiled-local
ETC-EXPLORATION-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE compiled-local
ETC-ACTION-WITH-COMMIT-COMMIT-PHASE compiled-local
ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET compiled-local
ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET compiled-local
ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET compiled-local
ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND compiled-local
ETC-WRONG-COMMIT-PROBABILITY-DESIGN theorem-card-only
ETC-MEAS-COMMITARM-NE-BESTARM compiled-local
ETC-MEAS-EMPMEAN-GE-EMPMEAN compiled-local
ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM compiled-local
ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT compiled-local
ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET compiled-local
ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM compiled-local
ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS compiled-local
ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL compiled-local
ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL compiled-local
ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL compiled-local
ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET compiled-local
ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF compiled-local
ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT compiled-local
ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL compiled-local
ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND compiled-local
ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS compiled-local
ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS compiled-local
ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND compiled-local
ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE compiled-local
ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND compiled-local
ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND compiled-local
ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND compiled-local
ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT compiled-local
ETC-BOUNDED-REWARD-INFINITEPI-SOURCE compiled-local
ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE compiled-local
ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND compiled-local
ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE compiled-local
ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER compiled-local
ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER compiled-local
ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER compiled-local
PULLCOUNT-SUM-TIME         compiled-local
MEAS-FIN-ACTION            compiled-local
MEAS-PULL-INDICATOR        compiled-local
MEAS-REWARD                compiled-local
MEAS-HISTORY               compiled-local
MEAS-SELECTED-REWARD-FINITE-SUM compiled-local
MEAS-SUMREWARDS            compiled-local
MEAS-REGRET                compiled-local
MEAS-PULLCOUNT             compiled-local
MEAS-PULLCOUNT-CAST        compiled-local
EXP-INDICATOR-PULL         compiled-local
EXP-FINSET-INDICATOR-PULL  compiled-local
EXP-PULLCOUNT-LINTEGRAL    compiled-local
EXP-WEIGHTED-PULLCOUNT-LINTEGRAL compiled-local
EXP-PULLCOUNT-LE-TIME      compiled-local
EXP-WEIGHTED-PULLCOUNT-LE-TIME compiled-local
EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN compiled-local
EXP-MODEL-GAP-OFREAL-BOUND compiled-local
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS compiled-local
OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS compiled-local
EXP-OFREAL-PSEUDOREGRET-BOUND compiled-local
EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG compiled-local
FINITE-BANDIT-GAP-BESTARM compiled-local
FINITE-BANDIT-BESTARM-DOMINATES compiled-local
FINITE-BANDIT-GAP-NONNEG compiled-local
FINITE-BANDIT-MAXGAP compiled-local
FINITE-BANDIT-GAP-LE-MAXGAP compiled-local
FINITE-BANDIT-MAXGAP-NONNEG compiled-local
EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP compiled-local
```

The first deliberate Mathlib-backed wrappers, deterministic regret consumer,
deterministic count partition leaf, and measurable action-event/indicator
canaries are now closed:

```text
Leaf: PULLCOUNT-FINSET
Goal: connect recursive `pullCount` to a filtered `Finset.range` cardinality.
Status: compiled-local.

Leaf: PSEUDOREGRET-FINSET
Goal: connect recursive `pseudoRegret` to a `Finset.range` sum of selected gaps.
Status: compiled-local.

Leaf: SUMREWARDS-FINSET
Goal: connect recursive `sumRewards` to a filtered `Finset.range` sum.
Status: compiled-local.

Leaf: REGRET-PULLCOUNT
Goal: reindex pseudo-regret as an arm sum of `gap * pullCount`.
Status: compiled-local.

Leaf: REGRET-COUNT-BOUND
Goal: convert per-arm pull-count bounds into a gap-weighted pseudo-regret
upper bound.
Status: compiled-local.

Leaf: REGRET-NAT-COUNT-BOUND
Goal: convert Nat-valued per-arm pull-count bounds into the gap-weighted
pseudo-regret upper bound after casting budgets to Rat.
Status: compiled-local.

Leaf: REGRET-UNIFORM-NAT-COUNT-BOUND
Goal: convert a uniform Nat-valued pull-count bound into
`pseudoRegret <= (sum gaps) * B`.
Status: compiled-local.

Leaf: ETC-EXPLOREARM-EQ-IFF-MOD
Goal: characterize `ETC.exploreArm spec t = a` by the modular equality
`t % K = a.val`.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT
Goal: prove each arm is pulled exactly once in the first round-robin ETC
exploration cycle.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-ADD-K-COUNT
Goal: prove each full-cycle extension of the ETC round-robin exploration
prefix adds exactly one pull of each arm.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-MUL-K-COUNT
Goal: prove `m` full ETC round-robin exploration cycles pull each arm exactly
`m` times.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT
Goal: specialize the multiple-cycle theorem to the configured ETC exploration
horizon `spec.explorationPulls * K`.
Status: compiled-local.

Leaf: ETC-EXPLORATION-REGRET-BOUND
Goal: bound the pure round-robin ETC exploration prefix pseudo-regret by
`(sum gaps) * spec.explorationPulls`.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND
Goal: bound the fixed-commit ETC trace pseudo-regret at the configured
exploration horizon by `(sum gaps) * spec.explorationPulls`.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE
Goal: define a fixed-commit ETC phase-switching trace and prove it agrees with
`ETC.exploreArm` throughout the configured exploration prefix.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-COMMIT-PHASE
Goal: prove the fixed-commit ETC phase-switching trace equals the supplied
commit arm after the configured exploration horizon.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE
Goal: prove the fixed-commit ETC phase-switching trace equals the selected
best arm after the configured exploration horizon when the supplied commit arm
is that selected best arm.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT
Goal: transfer pull counts from `ETC.actionWithCommit` to `ETC.exploreArm` on
any prefix contained in the configured exploration horizon.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT
Goal: specialize the fixed-commit ETC trace pull-count transfer to the
configured exploration horizon.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT
Goal: prove the one-step post-commit pull-count recurrence for the fixed-commit
ETC trace.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT
Goal: prove the closed-form post-exploration suffix pull count for the
fixed-commit ETC trace.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT
Goal: prove that every non-commit arm keeps its exploration-horizon pull count
after the fixed-commit ETC trace enters the commit phase.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT
Goal: prove that the commit arm has exploration-horizon count plus every
post-exploration suffix pull.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET
Goal: prove that, when the fixed commit arm is the selected best arm, the
post-exploration suffix adds no pseudo-regret.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND
Goal: prove that, when the fixed commit arm is the selected best arm, any
post-exploration suffix horizon satisfies the exploration-horizon regret
budget.
Status: compiled-local.

Leaf: PULLCOUNT-SUM-TIME
Goal: prove finite-action pull counts sum to the time horizon.
Status: compiled-local.

Leaf: MEAS-FIN-ACTION
Goal: prove measurable action evaluations yield measurable equality events.
Status: compiled-local.

Leaf: MEAS-PULL-INDICATOR
Goal: prove measurable action-equality events yield measurable constant-valued
pull indicators.
Status: compiled-local.

Leaf: MEAS-REWARD
Goal: prove selected-reward action indicators are measurable without choosing an
expectation or scalar algebra route.
Status: compiled-local.

Leaf: MEAS-SELECTED-REWARD-FINITE-SUM
Goal: prove finite sums of selected-reward indicator contributions are
measurable without choosing an expectation route.
Status: compiled-local.

Leaf: MEAS-SUMREWARDS
Goal: prove local recursive selected-reward accumulators are measurable by
connecting `sumRewards` to the selected-reward finite-sum bridge.
Status: compiled-local.

Leaf: MEAS-REGRET
Goal: prove local pseudo-regret is a measurable random variable before choosing
an expectation or probability-measure route.
Status: compiled-local.

Leaf: MEAS-PULLCOUNT
Goal: prove local recursive pull counts are measurable before choosing an
expected pull-count or scalar-cast route.
Status: compiled-local.

Leaf: MEAS-PULLCOUNT-CAST
Goal: prove scalar-casted local pull counts are measurable before choosing an
expected pull-count route.
Status: compiled-local.

Leaf: EXP-INDICATOR-PULL
Goal: prove the `ENNReal` lower integral of an action-equality pull-event
indicator equals the measure of that event.
Status: compiled-local.

Leaf: EXP-FINSET-INDICATOR-PULL
Goal: prove the `ENNReal` lower integral of a finite sum of action-equality
pull-event indicators equals the finite sum of event measures.
Status: compiled-local.

Leaf: EXP-PULLCOUNT-LINTEGRAL
Goal: prove the `ENNReal` lower integral of scalar-casted recursive
`pullCount` equals the finite sum of action-event measures.
Status: compiled-local.

Leaf: EXP-WEIGHTED-PULLCOUNT-LINTEGRAL
Goal: prove the `ENNReal` lower integral of a finite weighted sum
`gap a * pullCount a n` equals the corresponding weighted finite sum of
action-event measures.
Status: compiled-local.

Leaf: EXP-PULLCOUNT-LE-TIME
Goal: under a probability measure, prove the `ENNReal` lower integral of a
scalar-casted recursive pull count is bounded by the horizon.
Status: compiled-local.

Leaf: EXP-WEIGHTED-PULLCOUNT-LE-TIME
Goal: under a probability measure, prove the `ENNReal` lower integral of a
finite weighted pull-count sum is bounded by the weighted horizon budget.
Status: compiled-local.

Leaf: EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN
Goal: specialize the weighted probability budget bound to
`(Finset.univ : Finset (Fin K))`.
Status: compiled-local.

Leaf: EXP-MODEL-GAP-OFREAL-BOUND
Goal: instantiate the finite-arm weighted budget bound with
`ENNReal.ofReal (((model.gap a : Rat) : Real))`.
Status: compiled-local.

Leaf: OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
Goal: under explicit nonnegativity of real weights, prove `ENNReal.ofReal`
commutes with finite weighted Nat-count sums.
Status: compiled-local.

Leaf: OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
Goal: under explicit nonnegativity of model gaps, prove pointwise Rat-valued
`pseudoRegret` has the same `ENNReal.ofReal` image as the finite-arm weighted
pull-count expression.
Status: compiled-local.

Leaf: EXP-OFREAL-PSEUDOREGRET-BOUND
Goal: under explicit gap nonnegativity, bound the lower integral of
`ENNReal.ofReal` pseudo-regret by the model-gap horizon budget.
Status: compiled-local.

Leaf: EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG
Goal: expose the same lower-integral pseudo-regret bound with the natural
Rat-level gap nonnegativity contract.
Status: compiled-local.

Leaf: EXP-REGRET-PULLCOUNT
Goal: prove the Real-valued Bochner expected pseudo-regret identity
`E[pseudoRegret] = sum_a gap a * E[pullCount a]` under explicit per-arm
Real-cast pull-count integrability.
Status: compiled-local.

Leaf: FINITE-BANDIT-GAP-BESTARM
Goal: expose the definitional fact that the selected best arm has zero local
model gap.
Status: compiled-local.

Leaf: FINITE-BANDIT-BESTARM-DOMINATES
Goal: prove every arm mean is at most the mean of the local model's selected
`bestArm`, as a prerequisite for deriving model-gap nonnegativity.
Status: compiled-local.

Leaf: FINITE-BANDIT-GAP-NONNEG
Goal: prove every local `FiniteBanditModel.gap` value is Rat-nonnegative from
best-arm dominance and the local `gap` definition.
Status: compiled-local.

Leaf: FINITE-BANDIT-MAXGAP
Goal: expose the maximum local arm gap over the finite arm set as a deterministic
model constant.
Status: compiled-local.

Leaf: FINITE-BANDIT-GAP-LE-MAXGAP
Goal: prove every local `FiniteBanditModel.gap` value is bounded by
`FiniteBanditModel.maxGap`.
Status: compiled-local.

Leaf: FINITE-BANDIT-MAXGAP-NONNEG
Goal: prove the finite maximum gap is Rat-nonnegative.
Status: compiled-local.

Leaf: EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP
Goal: remove the explicit `hgap` argument from the `ENNReal.ofReal`
lower-integral pseudo-regret bound by using `FiniteBanditModel.gap_nonneg`.
Status: compiled-local.
```

Closed statement:

```lean
theorem pullCount_eq_finset_filter_card
    {Action : Type u} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (t : Nat) :
    pullCount action a t =
      ((Finset.range t).filter fun s => action s = a).card := by
  -- induction on t
  -- use Finset.range_add_one and Finset.filter_insert
  -- split on action t = a
```

These support:

- ETC round-robin counts;
- UCB pull-count bounds;
- final algorithm regret theorems.

## Suggested Immediate Plan

1. Keep the local gate passing:

   ```bash
   python3 tools/bandit.py check
   ```

2. When route judgment is needed, run two local reviewer agents and record a
   combined local review artifact before choosing probability foundations or an
   algorithm-specific leaf.

3. Do not enter probability/concentration until measurable and integrable
   contracts are written as exact leaves.

4. After every compiled leaf, update:
   - `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
   - `docs/completion_gap_audit.md`;
   - relevant proof-obligation ledgers;
   - retrieval indexes through `python3 tools/bandit.py reference-index`.

5. Periodically run the local two-agent review workflow after a meaningful
   batch, for example after a route-card or compiled leaf changes the
   probability/concentration frontier.

Current ETC boundary:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` is compiled locally, and
  it implements the Extended Pro recommendation to choose Candidate B from
  `reports/extended_pro_after_commitarm_suffix_count_candidate_prompt_2026-06-29.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_commitarm_suffix_count_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` is compiled locally, and
  it implements the second Extended Pro recommendation to choose Candidate C
  from
  `reports/extended_pro_after_suffix_budget_regret_candidate_prompt_2026-06-30.md`.
- The second recorded reviewer response is
  `reports/extended_pro_after_suffix_budget_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` is compiled locally, and it
  implements the third Extended Pro recommendation from
  `reports/extended_pro_after_coarse_suffix_regret_candidate_prompt_2026-06-30.md`.
- The third recorded reviewer response is
  `reports/extended_pro_after_coarse_suffix_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` is compiled locally, and
  it implements the fourth Extended Pro recommendation from
  `reports/extended_pro_after_phase_split_regret_candidate_prompt_2026-06-30.md`.
- The fourth recorded reviewer response is
  `reports/extended_pro_after_phase_split_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` is compiled locally, and it
  implements the Extended Pro recommendation from
  `reports/extended_pro_after_gap_bestarm_candidate_prompt_2026-06-30.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_gap_bestarm_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` is compiled locally, and
  it implements the Extended Pro recommendation from
  `reports/extended_pro_after_bestarm_suffix_no_regret_candidate_prompt_2026-06-30.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_bestarm_suffix_no_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` is compiled locally, and it
  implements the Extended Pro recommendation from
  `reports/extended_pro_after_bestarm_suffix_regret_bound_candidate_prompt_2026-06-30.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_bestarm_suffix_regret_bound_response_2026-06-30.md`.
- Do not prove the generic constant-arm suffix lemma, simplify the
  suffix-budget RHS, add empirical means/commit argmax, or move into
  probability, concentration, filtration, conditional expectation, or final ETC
  theorem facts before another reviewer/Extended Pro decision.

## Question For Extended Pro

Please review this plan as a Lean/formal-methods proof-engineering strategy.

Context:

- This repository aims to formalize bandit/RL theory in Lean 4.
- Current local code has compiled dependency-light finite-prefix bridges for
  pull counts, reward sums, filtered reward sums, and pseudo-regret.
- `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and `PSEUDOREGRET-FINSET` now
  compile as Mathlib-backed wrappers.
- `REGRET-PULLCOUNT` now compiles as a deterministic consumer leaf.
- `PULLCOUNT-SUM-TIME` now compiles as a deterministic finite-action count
  partition leaf.
- `MEAS-FIN-ACTION` now compiles as the first probability/measure canary.
- `MEAS-PULL-INDICATOR` now compiles as the second probability/measure canary.
- `MEAS-REWARD` now compiles as the selected-reward indicator measurability
  canary.
- `MEAS-SELECTED-REWARD-FINITE-SUM` now compiles as a selected-reward finite-sum
  measurability bridge.
- `MEAS-SUMREWARDS` now compiles as a local recursive reward-sum measurability
  bridge.
- `MEAS-REGRET` now compiles as a local pseudo-regret random-variable
  measurability bridge.
- `MEAS-PULLCOUNT` now compiles as a local pull-count random-variable
  measurability bridge.
- `MEAS-PULLCOUNT-CAST` now compiles as a scalar-casted pull-count
  measurability bridge.
- `COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO` now compiles as a narrow
  `condExpKernel`-to-ordinary-`condExp` zero bridge for arbitrary real
  variables and succ-indexed centered rewards; the broad `COND-EXPECT-REWARD`
  row remains open until the trajectory-law conditional-kernel identification
  and adaptive-policy assembly are supplied.
- `COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER` now compiles under
  explicit trim-a.e. law/integral-equality hypotheses, using the history-step
  centered-reward zero integral to feed the existing `condExpKernel` bridge;
  the broad `COND-EXPECT-REWARD` route remains open because the equality
  hypotheses are not yet constructed from `partialTraj`.
- `COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER` now compiles
  under explicit reward-coordinate pushforward equality and frozen-past
  a.e. hypotheses, reducing that structural law-identification interface to
  the existing integral consumer through Mathlib `integral_map`; the broad
  route remains open until those hypotheses are proved from the trajectory law.
- `COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED` now compiles as a deterministic
  bridge from a finite-history frozen-past hypothesis to the centered-target
  a.e. equality required by the map-law consumer; the broad route remains open
  until the history frozen-past theorem and `condExpKernel` trajectory-law
  identification are proved.
- `COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL` now compiles as the
  conditional-kernel frozen-past route: conditioning-measurable events have
  0/1 real mass under the conditional kernel, countable-valued
  conditioning-measurable variables are frozen under that kernel, and finite
  reward histories measurable at `F i` are frozen under
  `condExpKernel mu (F i)`.  The route is now fed by the concrete
  finite-history measurability hookup below; trajectory reward-law
  identification remains open.
- `COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP` now compiles as the
  concrete finite reward-history measurability hookup: coordinate
  measurability at `F i` yields frozen finite histories, and the generated
  `History.historyFiltrationSucc` specialization supplies those coordinates
  from the local history filtration.  The broad route still needs the
  `partialTraj`/history-to-`condExpKernel` reward-law identification and
  final adaptive theorem assembly.
- `COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP` now compiles as the
  finite action/reward pair-history frozen-past hookup under
  `[Countable Action]`: coordinate measurability at `F i` freezes the whole
  `History.finitePairHistoryOfTrace`, and the generated
  `History.historyFiltrationSucc` specialization supplies both action and
  reward coordinate measurability.  This supports the future pair-law
  identification; it does not prove the `partialTraj`/`condExpKernel` law.
- `COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP` now compiles as the
  successor-extension bridge for pair traces: `History.extendPairHistorySucc`
  appends one `(Action, Reward)` pair to a finite pair prefix, the actual
  `i + 1` trace prefix decomposes through it, and under generated
  `History.historyFiltrationSucc`/`condExpKernel` the random extended trace is
  a.e. the frozen old prefix extended by the random next pair.  This is still
  structural support, not the full joint `partialTraj`/`condExpKernel` law.
- `COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP` now compiles as the
  succ-indexed map-law consumer with the frozen-past side condition discharged
  from finite-history coordinate measurability, plus a generated
  `History.historyFiltrationSucc` specialization.  The broad route still
  needs the reward-coordinate pushforward identity from `condExpKernel` to
  `RewardKernel.historyStepKernelFamily`, i.e. the trajectory reward-law
  identification.
- `COND-EXPECT-REWARD-PAIR-MAP-CONSUMER` now compiles as the pair-law route
  into the map-law consumer: a `condExpKernel` next-step `(Action × Reward)`
  pushforward identity into `RewardKernel.actionRewardHistoryStepKernelFamily`
  marginalizes through `Prod.snd` into the reward-coordinate map law.  The
  remaining hard step is proving that pair-law identity from the finite-prefix
  `partialTraj` trajectory law.
- `COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP` now compiles as the
  generated `History.historyFiltrationSucc` specialization of the pair-law
  consumer: timewise action/reward measurability supplies the next coordinate
  measurability, and local history-filtration coordinate APIs supply reward
  prefix measurability.  The remaining hard step is still the actual
  `partialTraj`/history-to-`condExpKernel` action/reward pair-law identity.
- `COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP` now compiles
  as the concrete trace-pair and reward-projection specialization of that
  generated-history pair-law consumer: the pair history is
  `fun j => (action omega j, reward omega j)`, and the pair-context/state
  wrappers project the reward prefix before calling the original
  reward-history context/state.  The remaining hard step is still the actual
  generated-history `condExpKernel` pair-law identity.
- `COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP` now compiles as the
  local projection-measurability hookup: `History.pairHistoryRewardProjection`
  is measurable, so projected pair-context/state measurability follows from
  the original reward-history context/state measurability.  The remaining hard
  step is still the actual generated-history `condExpKernel` pair-law
  identity.
- `COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP` now compiles as the
  named finite pair-trace specialization: `History.finitePairHistoryOfTrace`
  is the `Finset.Iic`-indexed pair-coordinate prefix used in the remaining
  pair-law equality, aligning the conditional-expectation consumer with
  `RewardKernel.actionRewardPartialTrajectoryKernel`.  The remaining hard step
  is still the actual generated-history `condExpKernel` pair-law identity.
- `COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER` now compiles as
  the partialTraj finite-pair-trace consumer: an explicit generated-history
  `condExpKernel` law for the extended pair trace projects through
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply` into
  a reusable next-pair map-law adapter, then into the centered-reward consumer.
  The actual `partialTraj`/history-to-`condExpKernel` law remains open.
- `COND-EXPECT-REWARD-TRAJMEASURE-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP` now
  compiles as the project-notation canonical wrapper: the Mathlib
  `trajMeasure` full-prefix `condExpKernel` law is restated with
  `History.finitePairHistoryOfTrace` for the old and successor pair prefixes.
  This aligns the canonical source theorem with the theorem-card shape, while
  still not transporting the law to an arbitrary generated
  `Omega`/`History.historyFiltrationSucc` process.
- `COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT`
  now compiles as the explicit source-contract for that remaining law shape:
  `GeneratedActionPartialTrajectoryPairLawSource` stores the full finite-pair
  `partialTraj`/`condExpKernel` equality over
  `generatedActionFromRewardHistory`, and
  `generatedActionRandomPairDefinitionalMapSource_of_partialTrajectoryPairLawSource`
  feeds it into the existing definitional generated random-pair map source.
  This names the exact input expected from future disintegration work without
  proving the theorem-card law.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION` now
  compiles as the source-projection theorem for that same law: a
  `GeneratedActionPartialTrajectoryPairLawSource` exposes its full finite-pair
  `partialTraj`/`condExpKernel` field as a named theorem matching the
  theorem-card law shape, and it now also projects to the weaker
  `GeneratedActionDefinitionalActualRewardMapSource`,
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource`, and explicit
  `GeneratedActionActualRewardMapSource` interfaces.  This lets downstream
  selected-reward, mean-zero, and conditional-MGF routes share the same
  packaged partialTraj source without unpacking its fields manually, while
  still leaving the actual disintegration/trajectory-law proof open.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-EXTEND-MAP`
  now compiles as a source constructor from the narrower frozen-prefix
  extension-map law.  Future trajectory-law work can prove the extension-map
  `partialTraj`/`condExpKernel` equality, then this wrapper builds the full
  `GeneratedActionPartialTrajectoryPairLawSource` through the existing
  extension-to-full-trace adapter.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-HISTORYSTEP-PAIR-LAW`
  now compiles as the next upstream source constructor: a generated next-pair
  `condExpKernel` law identified with
  `RewardKernel.actionRewardHistoryStepKernelFamily` builds the same
  `GeneratedActionPartialTrajectoryPairLawSource` via the next-pair-to-extension
  and extension-to-full-source adapters.  This makes the remaining law target
  closer to the canonical `trajMeasure` next-pair route.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SPLIT-NEXTPAIR-LAW`
  now compiles as the split-law source constructor: the generated action
  conditional a.e. law plus the policy-selected reward-coordinate
  `condExpKernel` map law build the same
  `GeneratedActionPartialTrajectoryPairLawSource` through the split next-pair
  law builder and existing source adapters.  This narrows the next proof target
  to the two split laws while keeping the theorem-card law open.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW`
  now compiles as the selected-reward source constructor and theorem wrapper:
  for
  `generatedActionFromRewardHistory`, the generated-trace action-freezing API
  supplies the action side automatically, so the policy-selected
  reward-coordinate `condExpKernel` map law alone builds the same
  `GeneratedActionPartialTrajectoryPairLawSource` and directly exposes the
  full finite-pair `partialTraj`/`condExpKernel` law.  The remaining upstream
  proof target is still the selected reward-coordinate law under the generated
  history filtration.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE`
  now compiles as a source-conversion wrapper: an existing
  `GeneratedActionRandomPairDefinitionalMapSource` projects to the
  policy-selected reward-coordinate law and then builds
  `GeneratedActionPartialTrajectoryPairLawSource`.  This connects the older
  definitional random-pair source surface to the newer partialTraj source
  route without changing the theorem-card status.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  now compiles as the practical source-conversion wrapper for that same
  source contract: `GeneratedActionPartialTrajectoryPairLawSource`, measurable
  mean, centered reward-kernel law, raw reward range bounds, and deterministic
  mean range bounds build
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  This lets downstream raw-range/mean-range consumers use the named source
  directly, while still leaving the theorem-card pair-law proof open.
  The finite-pair comap selected-reward law can now enter at this base source
  layer too, with either the generated-history trim filter or the direct
  comap-trim filter, constructing the full finite-pair source internally before
  packaging the raw-range/measurable-mean-range source.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-MEAN-ZERO`
  now compiles as the matching source-level mean-zero consumer: the same
  generated `partialTraj` pair-law source plus raw/mean range regularity
  directly yields ordinary succ-indexed conditional mean-zero for the centered
  generated reward.  It removes manual `hcontext`/`hstate`/full-law threading
  for this route, while still consuming rather than proving the underlying
  `partialTraj`/`condExpKernel` law.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE`
  now compiles as the global-variance companion: the same generated
  `partialTraj` pair-law source plus a pointwise bound
  `varianceProxy context action <= varianceCeiling` builds the packaged
  uniform-variance practical source.  It prepares the conditional-MGF route
  without proving the underlying `partialTraj`/`condExpKernel` law.
  The finite-pair comap selected-reward law can now enter at this source layer
  as well, constructing the full finite-pair source internally before packaging
  the uniform-variance practical source, with either the generated-history
  trim filter or the direct comap-trim filter accepted as the law surface; the
  selected-reward law and global ceiling remain explicit caller obligations.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-COND-MGF`
  now compiles as the source-level uniform MGF consumer: the same generated
  `partialTraj` pair-law source plus raw/mean range regularity and a global
  variance ceiling directly yields the succ-indexed
  `ProbabilityTheory.HasCondSubgaussianMGF` witness.  It removes the need for
  downstream callers to manually pass `hcontext`, `hstate`, and the full
  finite-pair partialTraj law, while still leaving the theorem-card law open.
  The finite-pair comap selected-reward law can now be consumed directly into
  the same witness by first constructing the generated selected-reward source
  and full finite-pair `partialTraj` source; this still assumes the selected
  reward law rather than proving transport from canonical `trajMeasure`.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF`
  now compiles as the coarser-proxy source-level uniform MGF consumer: the same
  generated `partialTraj` pair-law source plus raw/mean range regularity, a
  global variance ceiling, and `varianceCeiling <= c` directly yields the
  succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy `c`.
  It is still a consumer of the supplied full finite-pair law, not a proof of
  that law or of the proxy domination.
  The finite-pair comap selected-reward law can now enter this coarser-proxy
  route directly as well, by constructing the full finite-pair source
  internally; `varianceCeiling <= c` remains an explicit caller obligation.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-SOURCE`
  now compiles as the selected-history companion: the same generated
  `partialTraj` pair-law source plus
  `varianceProxy (context i history) ((policy i).action (state i history)) <=
  varianceCeiling i` builds the packaged history-variance practical source.
  This is still a source conversion, not a proof of the trajectory-law card.
  The finite-pair comap selected-reward law can now enter at this source layer
  too, constructing the full finite-pair source internally before packaging the
  selected-history-variance practical source, with either the generated-history
  trim filter or the direct comap-trim filter accepted as the law surface;
  selected-history ceilings remain explicit caller obligations.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-COND-MGF`
  now compiles as the selected-history source-level MGF consumer: the same
  generated `partialTraj` pair-law source plus raw/mean range regularity and
  selected-history variance ceilings directly yields the succ-indexed
  `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy
  `varianceCeiling i`.  It removes the same manual `hcontext`/`hstate`/law
  threading for the history-variance route while still consuming the packaged
  source law.
  The finite-pair comap selected-reward law now has the same direct entry into
  this selected-history-variance witness by constructing the full finite-pair
  source internally, with either the generated-history trim filter or the
  direct comap-trim filter accepted as the law surface; selected-history
  ceilings and the selected-reward law are still assumed inputs.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF`
  now compiles as the coarser-proxy selected-history source-level MGF
  consumer: the same generated `partialTraj` pair-law source plus raw/mean
  range regularity, selected-history variance ceilings, and
  `varianceCeiling i <= c` directly yields the succ-indexed
  `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy `c`.  It still
  consumes the supplied full finite-pair law and the proxy domination.
  The finite-pair comap selected-reward law can now enter this coarser-proxy
  selected-history route directly by constructing the full finite-pair source
  internally, with either the generated-history trim filter or the direct
  comap-trim filter accepted as the law surface; `varianceCeiling i <= c`
  remains an explicit caller obligation.
- `COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP` now compiles as
  the reward-coordinate adapter for that same full finite-pair-trace law:
  after projecting the `partialTraj` law to the next `(Action, Reward)` pair,
  it maps through `Prod.snd`, uses
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`, and rewrites
  the policy-selected action to the actual successor action under either an
  explicit action equality or `Policy.generatedActionTraceSucc`.  It still
  assumes the full finite-pair trace `condExpKernel`/`partialTraj` law.
- `COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER` now compiles as the
  extension-map partialTraj consumer: `Measure.map_congr` turns the generated
  successor decomposition into a pushforward equality, and a reusable adapter
  lifts any extension-map `partialTraj` law back to the full `i + 1` finite
  pair-trace law.  The centered consumer can still assume the narrower
  frozen-prefix extension-map law; the actual `partialTraj`/history-to-
  `condExpKernel` law remains open.
- `COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP` now compiles as the
  reward-coordinate adapter for that narrower extension-map law: it lifts the
  frozen-prefix extension-map law to the full finite-pair trace law, reuses the
  finite-pair-trace reward-map projection, and has a generated-action wrapper
  that supplies the successor action equality from `Policy.generatedActionTraceSucc`.
  The extension-map `condExpKernel`/`partialTraj` law remains assumed.
- `COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP` now compiles as the
  direct next-pair reward-coordinate adapter: an explicit
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair map law is
  projected through `Prod.snd` and
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`, then the
  policy action is rewritten to the actual successor action.  The
  finite-pair-history specialization aligns pair histories with reward-history
  context/state, and the generated-action wrapper removes the explicit
  successor equality when `Policy.generatedActionTraceSucc` is available.  The
  next-pair `condExpKernel` law itself remains assumed.
- `COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP`
  now compiles as the selected-reward canonical `trajMeasure` law in project
  finite-pair-history notation: it rewrites the `Preorder.frestrictLe n`
  conditioning prefix to `History.finitePairHistoryOfTrace` and returns
  `RewardKernel.selectedMeasure` at that prefix.  This is only the canonical
  Mathlib trajectory source; the ambient `Omega`/`History.historyFiltrationSucc`
  transport step remains open.
- `COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-REWARDHISTORY-CONDEXPKERNEL-MAP`
  now compiles as the reward-history projection of that canonical law, and
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT`
  now packages the corresponding generated ambient selected-reward law as an
  explicit source that converts into `GeneratedActionPartialTrajectoryPairLawSource`.
  The source still consumes the ambient reward-law field; it does not prove the
  trajectory-to-`condExpKernel` transport.
- `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW`
  now compiles as the source constructor from the Mathlib-facing finite-prefix
  comap conditioning shape into
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource`.  It uses
  `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace` and now
  accepts both the existing generated-history trim filter and a direct
  comap-trim filter at the selected-source, partialTraj-source, and theorem
  wrapper layers, so future selected-reward transport can target the comap
  sigma-algebra and directly enter the generated-history source route.  The
  same comap law now also constructs the full
  `GeneratedActionPartialTrajectoryPairLawSource` directly and exposes the
  theorem-card-shaped full finite-pair `partialTraj`/`condExpKernel` law
  without requiring callers to manually build and project the source.  It still
  consumes the selected-reward law.
- `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW`
  now compiles as the source-projection theorem for that contract: a
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource` directly exposes
  the theorem-card-shaped full `finitePairHistoryOfTrace` partialTraj law over
  `generatedActionFromRewardHistory`.  This narrows the Lean-facing surface for
  downstream consumers but still assumes the selected-reward law field.
- `COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE`
  now compiles as the upstream source conversion from the definitional
  actual-action reward-coordinate source to that selected-reward
  finite-pair-history source.  The proof only unfolds
  `generatedActionFromRewardHistory` and projects pair histories to reward
  histories; it still assumes the actual-action reward-coordinate law.
- `COND-EXPECT-REWARD-PRACTICAL-RAW-RANGE-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE`
  now compiles as the practical source conversion route: the definitional
  raw-range/measurable-mean-range generated random next-pair package, plus its
  uniform-variance and selected-history-variance wrappers, projects directly
  to `GeneratedActionSelectedRewardFinitePairHistoryLawSource` through the
  full finite-pair `partialTraj` source projection.  This lets the selected
  source mean-zero and conditional-MGF consumers start from the practical
  package surface; it still assumes the packaged random next-pair law.
- `COND-EXPECT-REWARD-PRACTICAL-SOURCE-VIA-SELECTED-FINITEPAIRHISTORY-COND-MGF`
  now compiles as the route-specific theorem surface for that composition:
  the practical base source reaches ordinary conditional mean-zero, and the
  practical uniform-variance/history-variance wrappers reach succ-indexed
  `HasCondSubgaussianMGF` witnesses, by first constructing the selected
  finite-pair-history source and then applying the selected-source consumers.
  This records the selected finite-pair-history route end-to-end while still
  consuming the packaged random next-pair law and variance/proxy contracts.
- `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO`
  now compiles as the direct mean-zero consumer for that source contract:
  once the generated selected-reward finite-pair-history law is supplied, the
  existing full finite-pair source route plus raw/mean range regularity yields
  ordinary succ-indexed conditional mean-zero.  The finite-pair comap
  selected-reward law can now be consumed directly into the same mean-zero
  surface with either the generated-history trim filter or the direct
  comap-trim filter, after the local comap-to-source adapter constructs the
  source internally.
  The same selected-reward finite-pair-history source now also has direct
  conditional-MGF consumers: with raw/mean range regularity it feeds
  succ-indexed `HasCondSubgaussianMGF` witnesses under either a global
  variance ceiling, a coarser global proxy, selected-history variance
  ceilings, or a coarser selected-history proxy.  These wrappers reuse the
  packaged full finite-pair `partialTraj` source route and still consume the
  selected-reward law plus variance/proxy contracts.
  The uniform-variance conditional MGF consumer now accepts the same direct
  comap-trim law surface, provided raw/mean range regularity and a global
  variance ceiling are supplied.
  Its coarser-proxy companion now accepts the same direct comap-trim law
  surface when a deterministic domination proof `varianceCeiling <= c` is
  supplied.
  The selected-history-variance conditional MGF consumer now accepts the same
  direct comap-trim law surface under the time-indexed selected-history
  variance ceiling contract.
- `POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP` now compiles as the RewardKernel
  side of that route: the one-step action/reward `partialTraj` measure equals
  `Measure.map (History.extendPairHistorySucc history)` of
  `RewardKernel.actionRewardHistoryStepKernelFamily`.  This removes one
  Mathlib decomposition gap but still does not prove the generated-history
  `condExpKernel` law.
- `COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP` now compiles as the
  law builder from an explicit conditional next-pair pushforward identity into
  the extension-map `partialTraj` identity.  It connects the pair-map law shape
  to the extension-map law shape, but the next-pair `condExpKernel` identity is
  still the open mathematical step.
- `COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP` now also
  exposes generated-action reward-coordinate, actual-action pair-product, and
  fully random next-pair law shapes as full finite-pair-trace `partialTraj` law
  adapters before applying the centered conditional mean-zero consumers.  The
  generatedActionFromRewardHistory actual-action reward-coordinate surface now
  also has a source constructor and theorem wrapper that expose the same full
  finite-pair `partialTraj` law without passing an explicit action trace or
  generated-trace equality.  The pair/reward law source and ambient
  trajectory-to-`condExpKernel` identification remain open.
- `COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER` now compiles as the next
  decomposition: the full next-pair `condExpKernel` law follows from a
  conditional action a.e. equality to the policy-selected action plus a
  reward-coordinate selected-measure law.  This isolates the remaining
  predictability/action-freezing and reward-law sources.
- `COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW` now compiles as a
  canonical pair-law adapter:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`
  rewrites a generated-action random next-pair source law stated with
  `Measure.map (Prod.mk actualAction) selectedMeasure` into the standard
  `RewardKernel.actionRewardHistoryStepKernelFamily` form over
  `History.finitePairHistoryOfTrace`.  It keeps the random next-pair law as an
  explicit hypothesis but removes manual `Prod.mk`/selected-measure rewriting
  from downstream consumers.
- `COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP` now compiles as the action
  side of that split: a countable next action measurable at `F i`, plus
  trim-a.e. equality to the policy-selected action, yields the conditional
  action a.e. equality consumed by the split-law builder.  Policy
  predictability and the reward-coordinate law remain open.
- `COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP` now compiles as
  the generated-history version of that action side: visible finite pair
  histories, measurable `pairState`, and pointwise policy-generation equality
  produce the conditional action a.e. equality.  The reward-coordinate law is
  still separate.
- `COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE` now compiles as a
  shifted generated-trace source for that pointwise policy-generation equality:
  `action (i+1)` is definitionally selected by `policy i` from the finite
  pair-history state when the action trace equals `Policy.generatedActionTraceSucc`.
- `COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP` now
  compiles as the generated-action plus actual/random-pair reward-law route:
  an actual-action pair-product law marginalizes through `Prod.snd` to the
  actual-action reward-coordinate law, and a fully random next-pair law first
  freezes the action coordinate via `Measure.map_congr`.  The resulting law is
  rewritten to the policy-selected action, fed to the split-law builder, pushed
  through the extension-map `partialTraj` bridge, exposed as reusable
  full-trace law adapters, and consumed for succ-indexed conditional mean-zero
  under integrability.  The generatedActionFromRewardHistory actual-action
  reward-coordinate law is now also exposed directly as
  `GeneratedActionPartialTrajectoryPairLawSource` and as the theorem-card-shaped
  full finite-pair `partialTraj` law, with no explicit action trace/equality
  argument at the call site.  The pair/reward-law source and ambient
  trajectory-to-`condExpKernel` identification remain open.
- `COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT` now
  compiles in `BanditRLProof.ConditionalRewardLawSource` as the narrower
  reward-coordinate source package: `GeneratedActionActualRewardMapSource`
  stores the shifted generated-action equality plus only the actual next-action
  reward-coordinate `condExpKernel` map law.  Its consumers reuse the existing
  actual reward-map route to expose the full finite-pair-trace `partialTraj`
  law and succ-indexed conditional mean-zero.  This reduces the future law
  construction target below the full random next-pair law, but still assumes
  the reward-coordinate law, integrability, and ambient `condExpKernel`
  trajectory identification.
- `COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the actual reward-coordinate source-level canonical pair-law
  consumer: `GeneratedActionActualRewardMapSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `History.finitePairHistoryOfTrace`, with reward-history `context/state`
  lifted through `History.pairHistoryRewardProjection`.  This exposes the
  canonical pair-law surface from the weaker actual reward-coordinate source,
  but still assumes that source law and the ambient trajectory-to-`condExpKernel`
  identification.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`
  now compiles as the definitional generated-action version of that narrower
  source: `GeneratedActionDefinitionalActualRewardMapSource` fixes the action
  trace to `generatedActionFromRewardHistory`, derives `haction` from
  measurable reward-history state extractors and timewise reward measurability,
  converts to `GeneratedActionActualRewardMapSource`, and reuses its
  finite-pair-trace `partialTraj` and conditional mean-zero consumers.  The
  actual reward-coordinate law, integrability, and ambient `condExpKernel`
  trajectory identification remain open.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the definitional actual reward-coordinate source-level
  canonical pair-law consumer: `GeneratedActionDefinitionalActualRewardMapSource`
  yields `RewardKernel.actionRewardHistoryStepKernelFamily` over
  `generatedActionFromRewardHistory`, deriving action measurability from the
  source's reward-history state measurability and reusing the explicit
  actual-source pair-law wrapper.  This keeps the source surface free of
  explicit `action`/`haction`, but still assumes the definitional
  reward-coordinate law and the ambient trajectory-to-`condExpKernel`
  identification.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW`
  now has a standalone card and canary for the definitional actual
  reward-coordinate source-level full finite-pair-trace `partialTraj`
  consumer:
  `actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`
  yields the `RewardKernel.actionRewardPartialTrajectoryKernel` law over
  `generatedActionFromRewardHistory`.  The theorem was already compiled as
  part of the source contract; the new leaf makes the full-trace law reusable
  independently from the canonical history-step pair-law consumer.  It still
  assumes the definitional reward-coordinate source law and the ambient
  trajectory-to-`condExpKernel` identification.
- `COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT` now compiles in
  `BanditRLProof.ConditionalRewardLawSource` as a reusable source package:
  `GeneratedActionRandomPairMapSource` stores the shifted generated-action
  equality plus each step's random next-pair `condExpKernel` map law, and the
  consumers expose both the full finite-pair-trace `partialTraj` law and
  succ-indexed conditional mean-zero.  This packages the remaining law
  assumption; it does not construct the pair/reward law source, prove
  integrability, or identify the ambient trajectory law with `condExpKernel`.
- `COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as a source-level canonical pair-law consumer:
  `GeneratedActionRandomPairMapSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `History.finitePairHistoryOfTrace`, with reward-history `context/state`
  lifted through `History.pairHistoryRewardProjection`.  This removes repeated
  unpacking of the source fields before downstream pair-law consumers while
  still leaving the random-pair source law and ambient `condExpKernel`
  trajectory identification explicit.
- `COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE` now
  compiles as a source-conversion layer: a generated random next-pair source
  can be weakened into `GeneratedActionActualRewardMapSource` by freezing the
  generated action coordinate under `condExpKernel` and marginalizing through
  `Prod.snd`.  The definitional variant converts
  `GeneratedActionRandomPairDefinitionalMapSource` into
  `GeneratedActionDefinitionalActualRewardMapSource` using the source's
  state-measurability field.  This does not construct the random-pair law.
- `COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the centered source map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairCenteredSource` exposes the
  source's packaged `GeneratedActionRandomPairMapSource` directly.  This is a
  named interface wrapper; it does not construct the random next-pair law or
  the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the centered-source projection layer:
  `generatedActionActualRewardMapSource_of_randomPairCenteredSource` weakens
  `GeneratedActionRandomPairCenteredSource` into
  `GeneratedActionActualRewardMapSource` by reusing the centered source's
  packaged random-pair map source and state-measurability field.  The centered
  kernel law and integrability fields remain assumptions carried by the
  stronger source.
- `COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the bounded-centered source map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  Its a.e. measurability and interval-bound evidence remain available for
  integrability consumers but are not needed by this weaker map-source
  interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the bounded-centered projection layer:
  `generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource`
  weakens `GeneratedActionRandomPairBoundedCenteredSource` into
  `GeneratedActionActualRewardMapSource` by reusing the bounded source's
  packaged random-pair map source and state-measurability field.  Its a.e.
  measurability and interval-bound evidence remain assumptions for
  integrability consumers but are not needed by this weaker interface.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT` now compiles
  as the narrower generated-action source layer:
  `GeneratedActionRandomPairDefinitionalMapSource` defines the action trace as
  `generatedActionFromRewardHistory`, derives timewise action measurability
  from measurable reward-history state extractors plus timewise reward
  measurability, converts to `GeneratedActionRandomPairMapSource`, and reuses
  the full finite-pair-trace and conditional mean-zero consumers.  The random
  next-pair law, integrability, and ambient `condExpKernel` trajectory
  identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the definitional source-level canonical pair-law consumer:
  `GeneratedActionRandomPairDefinitionalMapSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `generatedActionFromRewardHistory`, avoiding explicit `action`/`haction`
  parameters before the canonical pair-law surface.  The definitional random
  next-pair law and ambient `condExpKernel` trajectory identification remain
  open assumptions.
- `COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT` now also compiles in
  `BanditRLProof.ConditionalRewardLawSource`: `GeneratedActionRandomPairCenteredSource`
  packages context/state measurability, the centered reward-kernel law, the
  generated random-pair source, and per-step ambient centered-reward
  integrability.  Its consumers expose the full finite-pair-trace `partialTraj`
  law and succ-indexed conditional mean-zero without a separate `h_integrable`
  argument.  The law source and integrability fields are still assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the centered-source canonical pair-law consumer:
  `GeneratedActionRandomPairCenteredSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by projecting its packaged
  random-pair map source plus context/state measurability.  This keeps the
  centered law and integrability fields available for later consumers while
  still leaving random-pair law construction and ambient `condExpKernel`
  trajectory identification open.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT` now
  compiles as the definitional generated-action centered source:
  `GeneratedActionRandomPairDefinitionalCenteredSource` removes explicit
  `action` and `haction` inputs from the centered source layer by reusing
  `generatedActionFromRewardHistory` plus
  `GeneratedActionRandomPairDefinitionalMapSource`.  Its conversion
  `generatedActionRandomPairCenteredSource_of_definitionalCenteredSource`
  enters the existing centered-source route, and its consumers expose the full
  finite-pair-trace `partialTraj` law plus succ-indexed conditional mean-zero.
  The definitional random-pair law and centered integrability fields are still
  assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the definitional centered-source canonical pair-law consumer:
  `GeneratedActionRandomPairDefinitionalCenteredSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `generatedActionFromRewardHistory`, again without explicit `action`/`haction`
  parameters.  It remains a source consumer, not a construction of the
  random-pair law.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-INTEGRABILITY`
  now compiles as a named integrability projection:
  `centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource`
  exposes the definitional centered source's packaged per-step ambient
  centered-reward integrability without requiring downstream callers to unpack
  the structure field directly.  This is a projection of an assumed field, not
  a boundedness-derived integrability proof.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the direct random-pair map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource`
  weakens `GeneratedActionRandomPairDefinitionalCenteredSource` into
  `GeneratedActionRandomPairMapSource` over `generatedActionFromRewardHistory`
  by projecting the packaged definitional map source.  The centered
  reward-kernel law and integrability fields are intentionally unused by this
  weaker map-source interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as a source-conversion leaf:
  `generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource`
  weakens `GeneratedActionRandomPairDefinitionalCenteredSource` into
  `GeneratedActionDefinitionalActualRewardMapSource` by projecting the
  packaged definitional random-pair map source.  The centered reward-kernel law
  and integrability fields remain available for stronger centered-source
  consumers but are intentionally unused by this weaker reward-coordinate
  interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the explicit generated-action counterpart:
  `generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource`
  weakens `GeneratedActionRandomPairDefinitionalCenteredSource` into
  `GeneratedActionActualRewardMapSource` whose action trace is
  `generatedActionFromRewardHistory`.  It first reuses the definitional
  actual-map projection and then the existing definitional-to-explicit actual
  reward-map conversion.
- `COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT` now compiles
  in the same module as the bounded/a.e.-measurable variant:
  `GeneratedActionRandomPairBoundedCenteredSource` replaces the direct
  centered-integrability field with per-step `AEMeasurable` evidence and a.e.
  interval bounds, derives integrability via Mathlib `Integrable.of_mem_Icc`,
  converts to `GeneratedActionRandomPairCenteredSource`, and exposes the same
  finite-pair-trace and conditional mean-zero consumers.  The random pair law,
  a.e. bound evidence, and ambient `condExpKernel` trajectory identification
  remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the bounded-centered-source canonical pair-law consumer:
  `GeneratedActionRandomPairBoundedCenteredSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering through
  `generatedActionRandomPairCenteredSource_of_boundedCenteredSource` and the
  centered-source pair-law route.  It preserves the bounded/a.e. regularity
  path while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT` now also
  compiles in `BanditRLProof.ConditionalRewardLawSource`:
  `GeneratedActionRandomPairRawMeanBoundedSource` replaces direct centered
  a.e. measurability and centered interval bounds with separate raw-reward and
  selected-mean a.e. measurability plus interval bounds.  It derives centered
  a.e. measurability via `AEMeasurable.sub`, derives centered bounds by
  interval subtraction, converts to `GeneratedActionRandomPairBoundedCenteredSource`,
  and exposes integrability plus the same finite-pair-trace and conditional
  mean-zero consumers.  The random pair law, raw/mean bound evidence, and
  ambient `condExpKernel` trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw/mean bounded canonical pair-law consumer:
  `GeneratedActionRandomPairRawMeanBoundedSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering through
  `generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource` and
  the bounded-centered pair-law route.  It keeps the raw-reward/selected-mean
  regularity path aligned with the canonical next-pair law while still leaving
  the random next-pair law and ambient `condExpKernel` trajectory
  identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw/mean bounded map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw/mean bounded projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource`
  weakens `GeneratedActionRandomPairRawMeanBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its raw reward and
  selected mean a.e. measurability/bound fields remain assumptions for the
  centered-bound and integrability consumers but are not needed by this weaker
  interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT` now
  compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawBoundMeanBoundedSource` removes the explicit
  raw-reward `AEMeasurable` field by deriving Rat-to-Real raw-reward
  a.e. measurability from the existing timewise reward trace measurability
  `hreward`.  It then converts to `GeneratedActionRandomPairRawMeanBoundedSource`
  and reuses the raw/mean bounded consumers.  Raw reward bounds, selected mean
  a.e. measurability/bounds, the random pair law, and ambient `condExpKernel`
  trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-bound/mean-bounded canonical pair-law consumer:
  `GeneratedActionRandomPairRawBoundMeanBoundedSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering through
  `generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`
  and then the raw/mean bounded pair-law route.  This keeps the
  reward-measurability-from-`hreward` source layer aligned with the canonical
  next-pair law while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw-bound/mean-bounded map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-bound/mean-bounded projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource`
  weakens `GeneratedActionRandomPairRawBoundMeanBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its raw reward bounds
  and selected mean a.e. measurability/bound fields remain assumptions for
  centered-bound and integrability consumers but are not needed by this weaker
  interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT`
  now compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` removes the
  selected-mean `AEMeasurable` field by deriving Rat-to-Real selected-mean
  a.e. measurability from a measurable mean surface composed with finite
  reward histories, context/state extractors, and the measurable policy action.
  It then converts to `GeneratedActionRandomPairRawBoundMeanBoundedSource` and
  reuses its consumers.  Raw reward bounds, selected mean bounds, the random
  pair law, and ambient `condExpKernel` trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-bound/measurable-mean canonical pair-law consumer:
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` directly
  exposes `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering
  through
  `generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`
  and then the raw-bound/mean-bounded pair-law route.  This keeps the
  measurable selected-mean source layer aligned with the canonical next-pair
  law while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`
  weakens `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its measurable mean
  surface, raw reward bounds, and selected mean bound fields remain assumptions
  for centered-bound and integrability consumers but are not needed by this
  weaker interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
  now compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource` removes
  the selected-mean a.e. bound field by deriving the generated selected-mean
  interval bound from a deterministic pointwise range bound on the mean
  surface.  It then converts to
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` and reuses
  its consumers.  Raw reward bounds, mean measurability, deterministic mean
  range bounds, the random pair law, and ambient `condExpKernel` trajectory
  identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean-range map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-bound/measurable-mean-range canonical pair-law
  consumer: `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`
  directly exposes `RewardKernel.actionRewardHistoryStepKernelFamily` by
  lowering through
  `generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`
  and then the raw-bound/measurable-mean pair-law route.  This keeps the
  deterministic selected-mean range-bound layer aligned with the canonical
  next-pair law while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean-range projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its measurable mean
  surface, raw reward bounds, and deterministic mean range bounds remain
  assumptions for centered-bound and integrability consumers but are not
  needed by this weaker interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
  now compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` removes
  the raw reward a.e. bound field by deriving the generated raw reward
  interval bound from a deterministic pointwise range bound on the reward
  trace.  It then converts to
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource` and
  reuses its consumers.  Mean measurability, deterministic raw reward and
  mean range bounds, the random pair law, and ambient `condExpKernel`
  trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-range/measurable-mean-range canonical pair-law
  consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`
  lowers through
  `generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`
  and reuses the raw-bound/measurable-mean-range history-step pair-law route.
  This exposes the canonical `RewardKernel.actionRewardHistoryStepKernelFamily`
  next-pair law directly from the deterministic raw reward and mean range
  source layer while still assuming the random next-pair law source and
  ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-range/measurable-mean-range projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its deterministic raw
  reward and mean range fields remain assumptions for centered-bound and
  integrability consumers but are not needed by this weaker interface.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
  now compiles as the practical definitional generated-action version of that
  top source layer:
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  removes explicit `action` trace and `haction` inputs by using
  `generatedActionFromRewardHistory` plus
  `GeneratedActionRandomPairDefinitionalMapSource`.  It converts to
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` and
  reuses the existing integrability, full finite-pair-trace `partialTraj`
  law, and conditional mean-zero consumers.  The definitional random-pair law,
  mean measurability, deterministic raw reward and mean range bounds, and
  ambient `condExpKernel` trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the practical definitional canonical pair-law consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  lowers through
  `generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  and reuses the explicit raw-range history-step pair-law route.  This exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` directly over
  `generatedActionFromRewardHistory` while preserving the implicit action
  surface of the practical top source.  It still assumes the definitional
  random next-pair law and ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as a named map-source projection:
  `generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  directly into the explicit `GeneratedActionRandomPairMapSource` whose action
  trace is `generatedActionFromRewardHistory`.  This keeps the lower map-law
  route available without first building the full explicit raw-range source.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  now compiles as the matching partialTraj-source projection:
  `generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens the same practical definitional raw-range source directly into
  `GeneratedActionPartialTrajectoryPairLawSource` by projecting the packaged
  definitional random-pair map source and context measurability.  This is a
  source-surface conversion only; it still assumes the packaged random next-pair
  law and does not prove the ambient `partialTraj`/`condExpKernel` trajectory
  identification.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY`
  now compiles as the top definitional regularity layer:
  `centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  and
  `centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  expose centered successor reward a.e. measurability and the deterministic
  centered interval bound directly from the practical definitional source.
  The proof route lowers through the existing explicit raw-range source
  conversion and reuses the raw-range regularity consumers.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  now compiles as the practical bounded-centered source projection:
  `generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  directly into `GeneratedActionRandomPairBoundedCenteredSource` over
  `generatedActionFromRewardHistory`.  It packages the existing generated
  random-pair map-source projection with the centered successor reward
  a.e. measurability and interval-bound evidence, so later bounded-source
  integrability and tail routes can consume one named source contract.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE`
  now compiles as the direct centered-source projection:
  `generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  lowers the same practical definitional source through the bounded-centered
  wrapper and into `GeneratedActionRandomPairCenteredSource` over
  `generatedActionFromRewardHistory`.  This exposes the existing
  integrability-based centered-source consumers from the top practical source
  contract without repeating the bounded-integrability construction at each
  call site.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the definitional centered-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  packages the same practical definitional source directly into
  `GeneratedActionRandomPairDefinitionalCenteredSource`.  It preserves the
  generated action trace as an implicit `generatedActionFromRewardHistory`
  surface while reusing the bounded-derived integrability theorem, so the newer
  definitional centered-source consumers can be reached without first exposing
  an explicit action trace.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the selected-history variance-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the definitional
  centered-source projection above.  This gives downstream centered-source
  consumers a direct interface from the selected-history variance source while
  keeping the random next-pair law and variance ceilings as source assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the selected-history variance random-pair map projection:
  `generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated random-pair map-source projection.  This gives full next-pair law
  and partialTraj consumers a direct interface from the selected-history
  variance source while keeping the random next-pair law and time-indexed
  variance ceilings as source assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  now compiles as the selected-history variance full finite-pair
  `partialTraj` source projection:
  `generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the raw-range-to-
  `partialTraj` source conversion.  This gives full finite-pair consumers a
  direct interface from the selected-history variance source while keeping the
  random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the selected-history variance history-step pair-law
  consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`
  first exposes the generated random-pair map source and then reuses the
  source-level canonical history-step consumer.  This gives history-step
  consumers a direct interface from the selected-history variance source while
  keeping the random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the selected-history variance definitional actual
  reward-map projection:
  `generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the existing
  definitional actual reward-coordinate projection.  This gives definitional
  reward-coordinate consumers a direct interface from the selected-history
  variance source while keeping the random next-pair law and time-indexed
  variance ceilings as source assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the selected-history variance actual-reward-map projection:
  `generatedActionActualRewardMapSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated actual reward-map projection.  This gives reward-coordinate law
  consumers a direct interface from the selected-history variance source while
  keeping the random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  now compiles as the selected-history variance bounded-source projection:
  `generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the bounded-centered
  projection.  This preserves deterministic centered reward bounds for
  bounded-integrability and tail consumers while keeping the selected-history
  variance ceiling as part of the source package.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  now compiles as the selected-history variance centered-source projection:
  `generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`
  first lowers the history-variance wrapper to the bounded centered-source
  projection and then reuses the existing integrability-based centered-source
  conversion.  This gives downstream mean-zero and centered-source consumers a
  direct interface from the selected-history variance source while keeping the
  random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the uniform variance random-pair map projection:
  `generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated random-pair map-source projection.  This gives full next-pair law
  and partialTraj consumers a direct interface from the uniform variance
  source while keeping the random next-pair law and global variance ceiling as
  source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  now compiles as the uniform variance partialTraj-source projection:
  `generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the base source to
  `GeneratedActionPartialTrajectoryPairLawSource` conversion.  This gives full
  finite-pair `partialTraj` source consumers a direct interface from the
  uniform variance source while keeping the random next-pair law and global
  variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the uniform variance canonical pair-law consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`
  first exposes the generated random-pair map source and then reuses the
  generic random-pair-source history-step consumer.  This gives history-step
  law consumers a direct interface from the uniform variance source while
  keeping the random next-pair law and global variance ceiling as source
  assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the uniform variance definitional actual reward-map
  projection:
  `generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the existing
  definitional actual reward-coordinate projection.  This gives definitional
  reward-coordinate consumers a direct interface from the uniform variance
  source while keeping the random next-pair law and global variance ceiling as
  source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the uniform variance actual-reward-map projection:
  `generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated actual reward-map projection.  This gives reward-coordinate law
  consumers a direct interface from the uniform variance source while keeping
  the random next-pair law and global variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the uniform variance-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the same definitional
  centered-source projection.  This gives downstream centered-source consumers
  a direct interface from the uniform variance source while keeping the random
  next-pair law and global variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  now compiles as the uniform variance bounded-source projection:
  `generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the bounded-centered
  projection.  This preserves deterministic centered reward bounds for
  bounded-integrability and tail consumers while keeping the global variance
  ceiling as part of the source package.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  now compiles as the uniform variance centered-source projection:
  `generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`
  first lowers the uniform-variance wrapper to the bounded centered-source
  projection and then reuses the existing integrability-based centered-source
  conversion.  This gives downstream mean-zero and centered-source consumers a
  direct interface from the uniform variance source while keeping the random
  next-pair law and global variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the definitional raw-range projection layer:
  `generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  into `GeneratedActionDefinitionalActualRewardMapSource` by reusing the
  source's packaged definitional random-pair map source.  Its deterministic
  raw reward and mean range fields remain assumptions for centered-bound and
  integrability consumers but are not needed by this weaker interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the explicit generated-action projection layer:
  `generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  into `GeneratedActionActualRewardMapSource` whose action trace is
  `generatedActionFromRewardHistory`.  It first reuses the definitional
  actual-map projection and then the existing definitional-to-explicit actual
  reward-map conversion; the raw reward and mean range fields remain available
  for stronger centered-bound/integrability consumers.
- `POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP` now compiles as the Mathlib-backed
  `partialTraj` one-step next-coordinate marginal wrapper: the reward-history
  and action/reward pair trajectory kernels from `n` to `n + 1` push forward
  along coordinate `n + 1` to their configured history-step kernels.  This
  supplies the trajectory-kernel side of the future `condExpKernel` pair-law
  identification, not the conditional-kernel identity itself.
- `EXP-INDICATOR-PULL` now compiles as an `ENNReal` lower-integral
  action-event indicator canary.
- `EXP-FINSET-INDICATOR-PULL` now compiles as an `ENNReal` lower-integral
  finite-sum bridge for action-event indicators.
- `EXP-PULLCOUNT-LINTEGRAL` now compiles as an `ENNReal` lower-integral
  identity for scalar-casted recursive pull counts.
- `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` now compiles as an `ENNReal`
  lower-integral weighted pull-count bridge.
- `EXP-PULLCOUNT-LE-TIME` now compiles as an `ENNReal` probability-measure
  pull-count budget bound.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME` now compiles as an `ENNReal`
  probability-measure weighted pull-count budget bound.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` now compiles as a `Fin K`/`Finset.univ`
  specialization of the weighted probability budget bound.
- `EXP-MODEL-GAP-OFREAL-BOUND` now compiles as an `ENNReal.ofReal` surrogate
  bound for `FiniteBanditModel.gap : Fin K -> Rat`.
- `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` now compiles as a scalar
  `ENNReal.ofReal` faithfulness lemma under explicit nonnegativity.
- `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` now compiles as a pointwise
  scalar/model pseudo-regret faithfulness bridge under explicit model-gap
  nonnegativity.
- `EXP-OFREAL-PSEUDOREGRET-BOUND` now compiles as an `ENNReal.ofReal`
  lower-integral pseudo-regret bound under explicit model-gap nonnegativity.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` now compiles as a
  Rat-level nonnegativity contract adapter for that lower-integral bound.
- `EXP-REGRET-PULLCOUNT` now compiles as a Real-valued Bochner expected-regret
  decomposition into finite gap-weighted expected pull counts under explicit
  per-arm pull-count integrability.
- `FINITE-BANDIT-GAP-BESTARM` now compiles as
  `FiniteBanditModel.gap_bestArm`, proving the selected best arm has zero
  local gap.
- `FINITE-BANDIT-BESTARM-DOMINATES` now compiles as
  `FiniteBanditModel.mean_le_bestArm_mean`, proving every arm mean is at most
  the selected best-arm mean.
- `FINITE-BANDIT-GAP-NONNEG` now compiles as
  `FiniteBanditModel.gap_nonneg`, proving the model-derived Rat-level gap
  nonnegativity contract.
- `FINITE-BANDIT-MAXGAP`, `FINITE-BANDIT-GAP-LE-MAXGAP`, and
  `FINITE-BANDIT-MAXGAP-NONNEG` now compile as the finite max-gap model
  invariant layer.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` now compiles as a no-explicit-`hgap`
  `ENNReal.ofReal` lower-integral pseudo-regret bound.
- Probability, measure theory, concentration inequalities, and full regret
  theorem routes are mostly theorem cards or retrieval cards.
- `python3 tools/bandit.py unfinished` is now the local unfinished-work entry
  point.
- The local `python3 tools/bandit.py check` gate passes.

Plan to evaluate:

1. Treat the dependency-light finite-prefix baseline as closed.
2. Treat `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and
   `PSEUDOREGRET-FINSET` as closed Mathlib wrapper canaries.
3. Treat `REGRET-PULLCOUNT` as the first closed deterministic consumer leaf.
4. Treat `PULLCOUNT-SUM-TIME` as the first closed deterministic count
   partition leaf.
5. Treat `MEAS-FIN-ACTION` as the first closed probability/measure canary.
6. Treat `MEAS-PULL-INDICATOR` as the second closed probability/measure
   canary.
7. Treat `MEAS-REWARD` as the selected-reward indicator measurability canary.
8. Treat `MEAS-SELECTED-REWARD-FINITE-SUM` as the selected-reward finite-sum
   measurability bridge.
9. Treat `MEAS-SUMREWARDS` as the local recursive reward-sum measurability
   bridge.
10. Treat `MEAS-REGRET` as the local pseudo-regret random-variable
    measurability bridge.
11. Treat `MEAS-PULLCOUNT` as the local pull-count random-variable
    measurability bridge.
12. Treat `MEAS-PULLCOUNT-CAST` as the scalar-casted pull-count measurability
    bridge.
13. Treat `EXP-INDICATOR-PULL` as the first lower-integral
    indicator/event-measure canary.
14. Treat `EXP-FINSET-INDICATOR-PULL` as the lower-integral finite-sum bridge
    for action-event indicators.
15. Treat `EXP-PULLCOUNT-LINTEGRAL` as the lower-integral pull-count identity.
16. Treat `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` as the lower-integral weighted
    pull-count bridge.
17. Treat `EXP-PULLCOUNT-LE-TIME` as the probability-measure pull-count
    budget bound.
18. Treat `EXP-WEIGHTED-PULLCOUNT-LE-TIME` as the probability-measure weighted
    pull-count budget bound.
19. Treat `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` as the `Fin K`/`Finset.univ`
    specialization.
20. Treat `EXP-MODEL-GAP-OFREAL-BOUND` as the `ENNReal.ofReal` surrogate
    model-gap bound.
21. Treat `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` as the scalar
    `ENNReal.ofReal` faithfulness leaf under explicit nonnegativity.
22. Treat `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` as the pointwise
    scalar/model bridge under explicit gap nonnegativity.
23. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND` as the `ENNReal.ofReal`
    lower-integral pseudo-regret bound under explicit gap nonnegativity.
24. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` as the Rat-level
    gap nonnegativity contract adapter for that lower-integral bound.
25. Treat `FINITE-BANDIT-GAP-BESTARM` as the canonical zero-gap fact for the
    selected best arm.
26. Treat `FINITE-BANDIT-GAP-NONNEG` as the model-invariant source for the
    explicit gap-nonnegativity contract used by the lower-integral bound.
27. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` as the no-explicit-`hgap`
    `ENNReal.ofReal` lower-integral pseudo-regret bound.
28. Treat `REGRET-COUNT-BOUND` as the deterministic scaffold converting
    per-arm pull-count bounds into a pseudo-regret bound.
29. Treat `REGRET-NAT-COUNT-BOUND` as the deterministic adapter for
    Nat-valued count bounds produced by future algorithm lemmas.
30. Treat `REGRET-UNIFORM-NAT-COUNT-BOUND` as the deterministic adapter for
    uniform Nat-valued count bounds.
31. Treat `ETC-EXPLOREARM-EQ-IFF-MOD` as the compiled modular selector helper
    for future ETC count theorems.
32. Treat `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` as the first compiled ETC
    round-robin count scaffold.
33. Treat `ETC-ROUND-ROBIN-ADD-K-COUNT` as the compiled full-cycle extension
    recurrence for ETC pull counts.
34. Treat `ETC-ROUND-ROBIN-MUL-K-COUNT` as the compiled multiple-full-cycle
    ETC count theorem.
35. Treat `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` as the configured
    exploration-horizon count adapter.
36. Treat `ETC-EXPLORATION-REGRET-BOUND` as the deterministic exploration-only
    ETC pseudo-regret scaffold.
37. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` as the fixed-commit ETC
    trace boundary on the exploration prefix.
38. Treat `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` as the fixed-commit ETC trace
    boundary after the exploration horizon.
39. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the fixed-commit
    ETC trace boundary after the exploration horizon when the commit arm is
    the selected best arm.
40. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` as the
    exploration-prefix pull-count transfer for the fixed-commit ETC trace.
41. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` as the configured
    exploration-horizon pull count for the fixed-commit ETC trace.
42. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` as the
    deterministic fixed-commit ETC trace regret scaffold at the exploration
    horizon.
43. Treat `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` as the one-step
    post-commit pull-count recurrence for the fixed-commit ETC trace.
44. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` as the closed-form
    post-exploration suffix pull count for the fixed-commit ETC trace.
45. Treat `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` as the
    non-commit-arm post-exploration pull-count stability corollary.
46. Treat `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` as the commit-arm
    post-exploration pull-count corollary.
47. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` as the compiled
    count-budget pseudo-regret scaffold for the fixed-commit ETC trace.
48. Treat `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` as the compiled
    coarse uniform post-exploration suffix regret bound.
49. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` as the compiled
    post-horizon phase-split pseudo-regret equality.
50. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` as the compiled
    phase-split exploration-plus-suffix-gap regret bound.
51. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` and
    `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` as the compiled
    optimal-commit deterministic suffix facts.
52. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the compiled
    trace fact that a best-arm commit stays on the selected best arm after the
    exploration horizon.
53. Treat `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as a theorem-card-only /
    missing-leaf design, not a local Lean proof.
54. Treat `ETC-MEAS-COMMITARM-NE-BESTARM` as the first compiled
    wrong-commit event measurability leaf.
55. Treat `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT` as the compiled pure
    set-inclusion event-reduction leaf.
56. Treat `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET` as the
    compiled arbitrary-measure monotonicity wrapper for the wrong-commit event
    reduction.
57. Treat `ETC-MEAS-EMPMEAN-GE-EMPMEAN` as the compiled pairwise
    empirical-mean comparison-event measurability canary.
58. Treat `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM` as the compiled
    finite existential wrong-mean event measurability wrapper.
59. Treat `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` as the
    compiled finite-union probability upper-bound wrapper.
60. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` as the compiled
    final elementary event-probability assembly wrapper.
61. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL` as the compiled
    abstract non-best pairwise-tail consumer wrapper.
62. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL` as the compiled
    if-zeroed nonbest pairwise-tail consumer wrapper.
63. Treat `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled filtered-sum pairwise-tail consumer wrapper.
64. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the compiled
    deterministic Nat denominator-positivity leaf for fixed-commit ETC
    exploration counts.
65. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the
    compiled Rat denominator-positivity adapter for fixed-commit ETC
    exploration counts.
66. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` as the
    compiled Rat nonzero-denominator adapter for fixed-commit ETC exploration
    counts.
67. Treat `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` as the compiled
    deterministic fixed-commit exploration-horizon empirical-mean definition
    and denominator rewrite.
68. Treat `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled numerator-measurability bridge for fixed-commit ETC empirical
    means under stochastic reward traces.
69. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
    as the compiled full empirical-mean measurability wrapper under an
    explicit Rat division-by-constant measurability contract.
70. Treat `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` as the compiled
    Rat division-by-constant measurability wrapper under
    `[MeasurableSingletonClass Rat]`.
71. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled no-`hdiv_const` empirical-mean measurability theorem consuming
    the Rat wrapper.
72. Treat `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` as the compiled
    coordinate-shaped empirical-mean measurability wrapper selected by
    Extended Pro.
73. Treat `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` as the compiled deterministic
    abstract commit-oracle argmax consumer for the wrong-commit event
    reduction.
74. Treat `ETC-COMMIT-ORACLE-PROB-WRAPPER` as the compiled
    oracle-specialized abstract pairwise-tail probability consumer selected by
    Extended Pro.
75. Treat `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` as the compiled
    oracle-specialized filtered-sum pairwise-tail probability consumer selected
    by Extended Pro.
76. Treat `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` as the compiled
    oracle-specialized if-zeroed nonbest pairwise-tail probability consumer
    selected by Extended Pro.
77. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` as the compiled
    oracle-selected wrong-event measurability wrapper under direct composed
    choice measurability, selected by Extended Pro.
78. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` as the compiled
    Mathlib-backed countable score-vector oracle-choice measurability bridge
    selected by Extended Pro as an immediately compilable candidate.
79. Treat `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` as the compiled Mathlib
    Pi-space coordinate-to-vector empirical-mean measurability bridge selected
    by Extended Pro.
80. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-choice measurability
    composition wrapper selected by Extended Pro.
81. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-wrong-event measurability
    composition wrapper selected by Extended Pro.
82. Treat `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled concrete argmax-oracle filtered-sum pairwise-tail consumer wrapper.
    `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now compiled locally, packaging the
    fixed-commit ETC empirical-mean pairwise-tail assumption and its concrete
    argmax consumer.  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is also compiled
    locally, removing the common positive empirical-mean denominator and
    reducing pairwise empirical-mean comparison to fixed-horizon reward-sum
    comparison.  `TAIL-HOEFFDING-BOUNDED` is now compiled locally as the
    generic bounded-centered Hoeffding MGF source with interval variance
    proxy.  `TAIL-SUBGAUSS-SUM` is now compiled locally as a Mathlib
    import wrapper for independent sub-Gaussian finite-sum tails, and
    `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is compiled locally as its ENNReal-valued
    event-probability boundary wrapper.  `TAIL-COND-SUBGAUSS` is also compiled
    locally as a Mathlib-backed strongly adapted conditional sub-Gaussian
    finite-prefix wrapper and ENNReal boundary adapter.  The ETC pairwise tail contract itself
    is now producible from explicit abstract sub-Gaussian witnesses through
    `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS`.  The generic empirical-mean
    comparison event-shape adapter is now compiled as
    `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT`.  The concrete
    centered reward-difference bridge is now compiled as
    `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`, and the concrete centered-diff
    sub-Gaussian producer specialization is compiled as
    `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF`.  The exact witness package
    consumed by that producer is now compiled as
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT`.  The canonical
    exponential tail helper is now compiled as
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL`.  The canonical
    wrong-commit probability bound consuming that tail is now compiled as
    `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND`.  The deterministic
    reward-coordinate independence and centered reward sub-Gaussian transfers,
    plus the reward-coordinate-law wrong-commit bound, are now compiled as
    `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS`,
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS`, and
    `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND`.  The ETC-shaped
    bounded-reward Hoeffding source now reuses the generic `Concentration`
    wrapper, and the corresponding strong all-arm bounded-reward
    wrong-commit bound is compiled as
    `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
    `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND`.  The action-matched
    reward-sub-Gaussian and bounded-reward wrong-commit wrappers are now
    compiled as
    `ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND` and
    `ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND`.  The exact
    action-matched source contract package is now compiled as
    `ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT`.  The fixed product-coordinate
    source and its direct wrong-commit probability bound are now compiled as
    `ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
    `ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE`.
    The same fixed-product wrong-commit bound now also has a standalone
    `Measure.real` bridge from the finite `ENNReal` tail budget under
    `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND`.
    The pointwise wrong-commit regret assembly bridge is now compiled as
    `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE`.
    The abstract lower-integral wrong-commit regret assembly is now compiled
    as `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY`.
    The concrete finite-argmax/infinitePi lower-integral regret assembly is now
    compiled as `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY`.
    The fixed product-coordinate bad-gap lower-integral endpoint now also has
    a named `ETC.fixedProductArgmaxAction` wrapper and named `ENNReal.ofReal`
    RHS budget under `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER`.
    The conservative sum-gap suffix adapter for that assembly is now compiled
    as `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY`.
    The fixed product-coordinate conservative sum-gap lower-integral endpoint
    now also has a named `ETC.fixedProductArgmaxAction` wrapper and named
    `ENNReal.ofReal` RHS budget under
    `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER`.
    The sharper max-gap suffix adapter is now compiled as
    `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY`.
    The polished fixed product-coordinate max-gap wrapper is now compiled as
    `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER`.
    The Bochner/Real finite-argmax/infinitePi expected-regret assembly now also
    exposes the bad-gap endpoint through the named `ETC.fixedProductArgmaxAction`
    API, aligned with the existing sum-gap and max-gap Real wrappers, under
    `ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY`.
    `ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET` now removes the
    public `baseCommitArm` artifact from the fixed-product max-gap Real endpoint:
    bounds and means are stated directly at `ETC.exploreArm`, while the existing
    wrapper is reused with `model.bestArm` only as an internal seed.  This closes
    the canonical fixed-product theorem surface, not the adaptive/LML ETC
    theorem; the next required transport is an action-dependent environment law
    aligned with the random post-exploration commit trace.
    `ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` is now compiled as the first
    direct support leaf for that transport: it proves fixed-commit exploration
    scores depend only on reward coordinates below the exploration horizon. The
    next narrow route remains construction and alignment of a history-derived
    commit policy, not an expected-regret theorem.
    `ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` now provides the exact
    generated-state score reconstruction needed by that next route: a history
    through time `t` determines the exploration argmax scores when the
    exploration horizon is at most `t + 1`. The remaining narrow task is an
    action equality for a measurable finite-history ETC policy.
    `ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` now compiles that policy
    and function-level action equality. The next narrow task is no longer a
    deterministic ETC wrapper: it is an action-dependent reward-law source for
    the generated trace, to be consumed by the already compiled conditional
    expectation and conditional-MGF surfaces.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` now supplies the
    full generated finite-pair law for the canonical Markov-kernel trajectory.
    The next narrow task is measure/kernel transport and finite-bandit
    regularity identification, not another generated-policy construction.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` now also
    reaches the conditional-MGF layer for rewards centered at `model.mean`.
    `ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` now constructs the raw
    context-independent Markov reward kernel from per-arm probability laws and
    proves selected-measure equality.
    `ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` now also constructs the
    centered model-mean law from common bounded arm laws and feeds it through
    the canonical trajectory conditional-MGF theorem.
    `ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL` now adds the true time-zero
    term and proves the complete selected centered-reward finite-sum tail.
    `ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now constructs the required
    fixed-exploration masked pairwise process through the existing witness
    package and proves the actual empirical-mean wrong-commit finite-union bound
    under canonical `trajMeasure`.
    `ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` now also compiles the
    Real probability conversion, measurable commit/wrong event, integrability,
    and generated-action Bochner expected-regret endpoint.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET` now factors the
    integrand through the `m*K` exploration rewards and transports the bound to
    any external reward law with the same finite-prefix pushforward.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET` now derives
    that pushforward identity from the initial reward marginal and successor
    `condDistrib` laws only through exploration, then transports the integral
    back to the original sample space.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET`
    now rewrites those hypotheses directly as stationary laws of the scheduled
    exploration arms, with no caller-visible context/state/policy kernel or
    trajectory measure. The next narrow law work is a concrete environment or
    LML `IsAlgEnvSeq` bridge to these conditional laws.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
    now accepts constant scheduled-arm laws with the exact LML feedback
    conditioning-variable shape and projects them to reward prefixes. The next
    seed-specific action-dependent kernel plus a.e. action transport is now
    compiled by the action-dependent full-history endpoint. The law route is
    complete without an LML dependency; a direct `IsAlgEnvSeq` wrapper is
    optional. The exact LML route next needs Real
    rewards/models, arbitrary common-sub-Gaussian laws, argmax tie semantics,
    and per-arm gap-weighted expected pull-count bounds; the local max-gap union
    theorem must not be presented as the exact `Bandits.ETC.regret_le` port.
83. Do not start final adaptive ETC/UCB theorem work from the compiled
    lower-integral surrogate.  The current narrow option is a deliberately
    split derivation of conditional witness fields from a concrete reward law:
    the shifted-history `StronglyAdapted` field, zero-summand MGF source,
    sampled-arm MGF transfer, reward-level conditional witness contract,
    independence-based conditional MGF and mean-zero wrappers, reward-only past
    independence bridge, full fixed-action history independence bridge,
    exact-mean zero-integral source, and bounded-source conditional mean-zero
    wrapper are now compiled; bounded rewards now also imply raw reward
    integrability locally, and fixed deterministic `actionWithCommit`
    centered rewards now instantiate a finite-prefix martingale-difference
    witness, while global succ-indexed martingale-difference witnesses now
    produce a Mathlib partial-sum `Martingale`.  CondExpKernel reward-law
    identification and final adaptive assembly remain beyond the fixed-action
    boundary.

Current review conclusion:

- Extended Pro judged the deterministic fixed-commit ETC layer saturated enough
  for now.
- The current required route-review mechanism is local two-agent review, not
  ChatGPT Extended Pro.
- The latest local two-agent review selected
  `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`; that leaf now
  compiles locally in `BanditRLProof.Algorithms.ETCArgmaxOracle`.
- `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now compiled locally.
- `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- `IID-REWARD-FAMILY` now compiles locally in
  `BanditRLProof.IndependenceFoundation` as generic infinite-product
  coordinate-transform independence plus a reward-trace specialization.
- `TAIL-HOEFFDING-BOUNDED` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian` as
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`.
- `TAIL-SUBGAUSS-SUM` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `TAIL-COND-SUBGAUSS` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `MEAS-HISTORY` now compiles locally in
  `BanditRLProof.HistoryFiltration` as finite action/reward history product
  objects over `Finset.Iic` prefixes, with measurable trace restrictions and
  measurable coordinate projections, including pair-coordinate trace prefixes
  and reward projection from finite `(Action, Reward)` pair histories.  It now
  also names the measurable successor-extension map for pair histories.
- `FILTRATION-HISTORY` now compiles locally in
  `BanditRLProof.HistoryFiltration`.
- `HISTORY-FILTRATION-FINITEPAIR-COMAP` now compiles locally in
  `BanditRLProof.HistoryFiltration`: finite pair histories are measurable at
  later generated-history filtration levels, and
  `History.historyFiltration ... (n + 1)` is exactly the comap of
  `History.finitePairHistoryOfTrace ... n`; the shifted
  `History.historyFiltrationSucc ... n` form is also named.  This is the
  sigma-algebra bridge between the local generated-history filtration and
  Mathlib finite-prefix conditioning surfaces; it does not prove reward-law or
  trajectory-law transport.
- `ADAPTED-ACTION` now compiles locally in
  `BanditRLProof.HistoryFiltration` as a countable/discrete past-coordinate
  measurability canary, with a reward-coordinate companion theorem.
- `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` now compiles locally in
  `BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail`.
- `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` now compiles locally in
  `BanditRLProof.Algorithms.ETCSumRewardsDiff`.
- `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` now compiles locally in
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` now compiles locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`, using
  `History.historyFiltrationSucc` from `BanditRLProof.HistoryFiltration`.
- `ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT` now compiles locally
  in `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE` now compiles locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `MART-DIFF-REWARD` now compiles locally in
  `BanditRLProof.MartingaleDifference`, including centered reward process
  builders from adaptedness, integrability, and succ-indexed conditional
  mean-zero contracts, plus the abstract Mathlib partial-sum `Martingale`
  wrapper, and
  `ETC-CENTERED-REWARD-MART-DIFF-BOUNDED-SOURCE` now compiles locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `TAIL-UNION-FINITE` now compiles locally in
  `BanditRLProof.ProbabilityUnionBound` as reusable explicit-`Finset` and
  `[Fintype]` finite-union outer-measure wrappers, including a nonempty-Finset
  equal-share `delta/card` normalizer; this is a probability assembly leaf, not
  a concentration theorem.
- `TAIL-SUMMABILITY-UCB` now compiles locally in
  `BanditRLProof.UCBSummability` as an abstract finite-arm finite-horizon
  bad-event summability wrapper consuming per-arm/per-time ENNReal tail bounds;
  UCB log/sqrt side conditions and the final regret theorem remain separate.
- `EXP3-POTENTIAL` now compiles locally in `BanditRLProof.Exp3Potential` as
  a deterministic finite-action exponential-weights potential surface with
  update unfolding, nonnegativity, one-step increment algebra, and
  finite-horizon telescoping.
- `EXP3-HEDGE-DETERMINISTIC-REGRET` now compiles locally in
  `BanditRLProof.Exp3HedgeRegret`: positive cumulative-loss weights are
  normalized on a nonempty finite arm set, the quadratic exponential bound and
  one-step log-potential inequality are proved, and telescoping yields a
  second-order comparator theorem for arbitrary nonnegative losses under
  `eta > 0`, plus `log |A| / eta + eta*T` for `[0,1]` losses.
- `EXP3-IMPORTANCE-WEIGHTED-MOMENTS` now compiles locally in
  `BanditRLProof.Exp3ImportanceWeighted`: the sampled-coordinate estimator has
  exact finite-sum armwise cancellation and mixed-loss identities, while its
  probability-weighted mixed square is exactly `sum_a loss(a)^2` and at most `|A|` for
  losses in `[0,1]`. These are deterministic weighted-sum identities.
- `EXP3-CONDITIONAL-MOMENT-TRANSPORT` now compiles locally in
  `BanditRLProof.Exp3ConditionalMoments`: an explicit normalized finite Dirac
  action law and an actual history-conditional `condDistrib` equality yield
  armwise unbiasedness plus exact mixed-loss and mixed-square Bochner-integral
  identities.
- `EXP3-GENERATED-ACTION-PROCESS` now compiles locally in
  `BanditRLProof.Exp3ActionProcess`: measurable history-indexed finite
  probability vectors generate a Markov kernel and canonical `compProd`
  history/action measure; the sampled action's `condDistrib` is a.e. that
  policy, and canonical armwise/mixed first- and second-moment wrappers consume
  the previous transport without external law premises.
- `EXP3-SCORE-REGULARITY` now compiles locally in
  `BanditRLProof.Exp3ScoreRegularity`: measurable supported `[0,1]` losses and a
  uniform positive probability floor imply measurable armwise/mixed first- and
  second-moment scores, pointwise reciprocal-floor bounds, and generated-law
  integrability. Its canonical consumers remove manual `hprob`, `hscore`, and
  `hIntegrable` premises from all three one-round moment identities.
- `EXP3-EXPLORATION-MIXED-RECURSIVE-TRAJECTORY` now compiles locally in
  `BanditRLProof.Exp3RecursiveTrajectory`: any measurable cumulative score on
  inclusive finite action/loss histories generates normalized exploration-mixed
  probabilities with floor `gamma / |A|`, a stochastic history algorithm, a
  complete adaptive trajectory kernel, and the exact successor-action
  conditional law given each finite prefix.
- `EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY` now compiles locally in
  `BanditRLProof.Exp3SampledHistoryScore`: the score starts from the initial
  action law and recursively adds each observed chosen-action Real loss divided
  by the exact preceding exploration-mixed probability. Its coordinate
  measurability, concrete probability floor, stochastic history algorithm,
  complete trajectory kernel, and exact successor-action conditional law all
  compile without arbitrary `score/hscore` inputs.
- `EXP3-PREDICTABLE-ADVERSARY` now compiles locally in
  `BanditRLProof.Exp3PredictableAdversary`: jointly measurable initial and
  history-dependent successor loss vectors are fixed before the current
  action, bounded in `[0,1]`, and realized as chosen-coordinate Dirac feedback.
  A prior-mixture transport preserves the concrete sampled EXP3 policy after
  conditioning on `(Env, prefix)`, closing the action-reactive-adversary gap.
- `EXP3-PREDICTABLE-OBSERVED-MOMENTS` and
  `EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS` now compile locally in
  `BanditRLProof.Exp3PredictableMoments`: initial and successor generated
  rewards equal their selected predictable losses almost surely, every actual
  time has the observed armwise first and mixed-square second moment identity
  on the common trajectory law, and both identities sum over
  `Finset.range horizon` with explicit integrability. The next theorem boundary
  is the sampled-history-score/Hedge-potential coupling, followed by
  exploration-bias control and `eta`/`gamma` optimization. This is not final
  EXP3 regret.
- `FTRL-ONE-STEP` now compiles locally in `BanditRLProof.FTRLOneStep` as
  a deterministic finite-action regularized-objective minimizer wrapper
  yielding the one-step linear-loss inequality under `0 < eta`; convexity,
  minimizer existence, Tsallis regularizer facts, stability/penalty, and regret
  remain separate.
- `TSALLIS-REGULARIZER` now compiles locally in
  `BanditRLProof.TsallisRegularizer` as a finite-simplex `Real.rpow`
  power-sum, entropy, and negative-entropy regularizer surface with nonzero
  denominator and nonnegative power-sum facts; convexity, stability/penalty,
  self-bounding, learning-rate, and regret remain separate.
- `ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `INT-REWARD-BOUNDED` /
  `ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` now compiles locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail`.
- `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` now compiles locally in
  `BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail`.
- `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` now compiles locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` and
  `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` now compile locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`.
- `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
  `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` now compile locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND` and
  `ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND` now compile locally
  in `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT` now compiles locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
  `ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE` now compile locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE` now compiles
  locally in `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` now compiles locally in
  `BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`.
- `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` now compiles locally in
  `BanditRLProof.Algorithms.ETCExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` now compiles locally
  in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` now compiles
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY` now compiles
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `MEAS-POLICY` now compiles locally in
  `BanditRLProof.PolicyMeasurability` as a measurable policy/state composition
  surface with arbitrary-filtration and generated-history-filtration
  specializations.
- `POLICY-GENERATED-ACTION-TRACE-MEASURABILITY` now compiles locally in
  `BanditRLProof.PolicyMeasurability` as policy-generated action-trace
  coordinate measurability from a time-indexed measurable state process.
- `KERNEL-REWARD` now compiles locally in `BanditRLProof.RewardKernel` as a
  Mathlib-backed reward-kernel contract surface: arm/context-indexed Markov
  reward laws, selected-measure probability, event-probability measurability,
  and policy/state selected-measure wrappers are available.
- `POSTERIOR-KERNEL` now compiles locally in
  `BanditRLProof.PosteriorKernel` as a Mathlib-backed posterior-kernel contract
  surface: histories index probability measures over environments, measurable
  and countable-history selector constructors are available, and a
  prior/likelihood/posterior surface is named. The canonical subroute now also
  wraps Mathlib `posterior likelihood prior` and proves it equals
  `condDistrib env history` whenever the source environment/history pair law is
  `prior ⊗ₘ likelihood`; arbitrary posterior surfaces, actual trajectory laws,
  Thompson sampling, and Bayesian regret remain separate.
- `TS-POSTERIOR-ACTION-IDENTITY-LEDGER` now compiles locally in
  `BanditRLProof.Algorithms.Thompson`: a posterior kernel, Thompson action
  kernel, measurable environment-to-best-action map, and event-level
  probability-matching equality are packaged as a source contract, with
  event-level and singleton action-probability consumers.  This still consumes
  the posterior action law; it does not prove Bayes' rule, construct the
  posterior sampler, import LML, or prove Bayesian regret.
- `TS-POSTERIOR-BEST-ACTION-MEASURABILITY` now compiles locally in
  `BanditRLProof.Algorithms.Thompson`: for countable singleton-measurable
  environment spaces, any `bestAction : Env -> Action` is measurable by
  Mathlib `measurable_of_countable`, and the posterior-action identity ledger
  can be built without a separate best-action measurability proof.  This
  discharges the finite/countable best-action regularity side condition, but
  the posterior action-law identity itself remains assumed.
- `TS-POSTERIOR-ACTION-CONDDISTRIB` now compiles locally in
  `BanditRLProof.Algorithms.Thompson`: the Thompson action conditional law is
  identified with `posterior.kernel.map bestAction`, the supplied posterior
  kernel/environment `condDistrib` equality is mapped through `bestAction`, and
  Mathlib `condDistrib_comp` yields the conditional law of the random best
  action. This generic local counterpart of pinned LML
  `Bandits.TS.hasCondDistrib_action` still accepts the posterior equality as a
  premise; downstream canonical pair-law and algorithm-density leaves now
  produce it. Concrete recursive density-law construction, global trace
  coupling, regret decomposition, and concentration remain open.
- `TS-CANONICAL-POSTERIOR-PAIR-LAW` now compiles locally across
  `BanditRLProof.PosteriorKernel` and `BanditRLProof.Algorithms.Thompson`:
  Mathlib's canonical posterior compProd identity and conditional-distribution
  uniqueness produce the environment posterior from an exact pair pushforward;
  the generic Thompson theorem then needs only the next-action law
  `condDistrib nextAction history = canonicalPosterior.map bestAction`.
  Canonical `Env × History` product sources discharge the pair law directly.
  The canonical sampler leaf below discharges the remaining action law.
- `TS-CANONICAL-SAMPLER-PROB-MATCH` now compiles locally in
  `BanditRLProof.Algorithms.ThompsonCanonicalSampler`: the mapped canonical
  posterior is lifted to the environment/history pair and composed with the
  canonical joint law. `Measure.fst_compProd` and a finite-measure
  history/action marginal transport construct both generic law premises, so
  the one-step theorem has no pair-law or action-law hypothesis. The downstream
  reference-policy and algorithm-density leaves connect this one-step logic to
  process-facing history laws.
- `TS-REFERENCE-POSTERIOR-POLICY-SAMPLER` now compiles locally in
  `BanditRLProof.Algorithms.ThompsonReferencePolicy`: following the pinned LML
  non-circular policy design, a fixed reference-process posterior is mapped
  through `bestAction`; the actual next action is sampled with `compProd` after
  a history `Kernel.comap`. The module proves the history/action law, the action
  `condDistrib`, preservation of every measurable base marginal, and
  preservation of the environment posterior after adjoining the action. Its
  finite action/reward-prefix endpoint therefore needs only
  reference-versus-actual posterior invariance. The downstream
  algorithm-density leaf now produces that invariance from matching marginal
  and joint density laws.
- `TS-ALGORITHM-DENSITY-POSTERIOR-INVARIANCE` now compiles locally in
  `BanditRLProof.Algorithms.ThompsonAlgorithmDensity`: an
  `AlgorithmDensityPosteriorSource` records that the actual history marginal
  and actual history/environment joint law are the corresponding reference
  laws weighted by one measurable history density. The generic
  `compProd_withDensity_left` lemma commutes that density through the reference
  posterior composition product; `condDistrib` uniqueness proves posterior
  invariance, and generic plus finite-pair endpoints immediately close
  reference-policy probability matching without posterior or action-law
  assumptions.
- `TS-CONDITIONAL-HISTORY-DENSITY-SOURCE` now compiles in the same module:
  equal actual/reference environment marginals and one a.e. conditional-history
  kernel density law construct both `AlgorithmDensityPosteriorSource`
  pushforward equalities using `condDistrib_comp_map`, `compProd`,
  `withDensity`, and coordinate swap. Generic and finite-pair consumers close
  probability matching directly. The recursive finite-history process theorem,
  its environment-indexed `condDistrib id` transport, and the four-family
  conditional split-source constructor now compile downstream. The canonical
  trajectory leaf now builds each fixed-environment pair `trajMeasure`, proves
  its combined and split process laws, identifies the full conditional sample
  law of `prior compProd trajectoryKernel`, and closes finite-prefix probability
  matching for supplied Markov trajectory-kernel families with canonical
  pointwise values. `ThompsonMeasurableTrajectory` now constructs those
  environment-indexed Markov kernels directly from jointly measurable feedback
  data using Mathlib `Kernel.traj`. The fixed-environment support theorem and
  projected prefix/next composition-product identity now prove the shifted pair
  `condDistrib` law; projective-limit uniqueness gives pointwise canonical
  equality, and the endpoint closes finite-prefix probability matching with no
  supplied kernel or process-law premise. `ThompsonRecursiveSampler` now also
  couples those policies into one non-circular uniform-reference Thompson
  `HistoryAlgorithm`, transports the fixed-environment action law through the
  prior, discharges finite-action AC by uniform full support, and proves
  probability matching for the same trajectory's successor action.
  `ThompsonBayesRegretDecomposition` transports that probability matching
  through arbitrary measurable history/action scores, and
  `ThompsonClippedUCBScore` now instantiates the exact pinned clipped score,
  proves its finite-history/trace identity and range regularity, and closes all
  decomposition integrability contracts. `ThompsonStationaryReward` now maps
  stationary environment/action reward kernels to independent latent arm
  streams, proves arbitrary-action adaptive-count upper/lower tails, and
  exposes the table through measurable next-unused deterministic feedback.
  The deterministic-support route now compiles as well: every canonical
  trajectory reward equals `rewardFromArmStream` almost everywhere, generic
  `IdentDistrib` wrappers retain arbitrary algorithm randomness, and the
  stationary environment-indexed augmented trajectory kernel has fixed-arm
  upper/lower adaptive-count tails. Next mix these pointwise laws through the
  augmented prior and derive measurable clipped-confidence events. The two
  concentration expectations and final Bayesian regret inequality remain
  separate.
- `POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION` now compiles locally in
  `BanditRLProof.RewardKernel`: a measurable policy plus a context/action
  Markov reward kernel gives a context/state Markov reward kernel, with
  measurable event probabilities.
- `POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` now compiles locally in
  `BanditRLProof.RewardKernel`: time-indexed measurable policies plus
  measurable context/state extractors from `Finset.Iic` reward histories give
  Mathlib `partialTraj` finite-prefix reward-history kernels.
- `KERNEL-POLICY-BIND` now compiles locally in `BanditRLProof.RewardKernel`:
  deterministic policy action kernels product with selected reward kernels to
  produce one-step `(Action × Reward)` kernels, and Mathlib `partialTraj`
  assembles finite-prefix action/reward pair trajectory kernels.  The one-step
  and history-step action/reward kernels also expose selected-reward marginal
  wrappers, and one-step `partialTraj` extensions expose their next-coordinate
  step-kernel marginal.
- `KERNEL-REWARD-MAP-LAW-TRANSFER` now compiles locally in
  `BanditRLProof.RewardKernel`: the one-step and history-step action/reward
  kernels push forward along `Prod.snd` to the selected reward measure.  This
  is the measure-level counterpart of the selected-reward event marginals and
  matches the map-law shape consumed by the `COND-EXPECT-REWARD` route.
- The fixed-action bounded/source conditional-MGF route now assembles
  `CenteredRewardCondSubGaussianWitnesses`, the pairwise tail contract, and the
  argmax wrong-commit probability consumer.  The canonical-tail variant now
  removes the explicit tail-domination hypothesis for this fixed
  `actionWithCommit` route, and the infinite-product source specialization is
  also compiled.  The policy/state, policy-generated action-trace,
  finite-history product measurability, reward-kernel regularity, one-step
  policy/reward Markov-kernel composition, finite-prefix reward-history
  `partialTraj`, finite-prefix action/reward pair trajectory kernels,
  selected-reward event and `Measure.map` marginal wrappers, one-step
  `partialTraj` next-coordinate marginal wrappers, and kernel-level
  centered-reward law transfer are compiled; the next layer is
  `partialTraj`/history-to-`condExpKernel`
  reward-law identification, Bayes-rule posterior identification, and final adaptive theorem assembly if moving beyond fixed
  product-coordinate
  `actionWithCommit`.
- The next direction is not another broad deterministic suffix simplification.
- The next proof-design layer is wrong-commit probability, starting with
  event reduction and measurability leaves.
- `research-wiki/open-problems/etc-wrong-commit-probability-design.md` is the
  current theorem card for that bridge.
- Extended Pro then chose `ETC.measurableSet_commitArm_ne_bestArm`; that leaf
  now compiles locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`;
  that pure event-reduction leaf now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`; that
  measure monotonicity wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose `ETC.measurableSet_empMean_ge_empMean`; that
  pairwise empirical-mean comparison-event measurability canary now compiles
  locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`; that finite
  existential wrong-mean event measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`; that finite-union
  probability upper-bound wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`; that final
  elementary event-probability assembly now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`; that abstract
  pairwise-tail consumer wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`; that if-zeroed
  nonbest pairwise-tail consumer wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`; that
  filtered-sum pairwise-tail consumer wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`; that
  deterministic Nat-level denominator-positivity leaf now compiles locally in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Extended Pro then chose
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos`; that
  Rat denominator adapter now compiles locally in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Extended Pro then chose
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero`;
  that Rat nonzero-denominator adapter now compiles locally in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Extended Pro then chose `ETC.empMeanAtExploration` and
  `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`; that
  deterministic empirical-mean API now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- Extended Pro then chose
  `ETC.measurable_sumRewards_actionWithCommit_exploration`; that
  numerator-measurability bridge now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`.
- Extended Pro then chose
  `ETC.measurable_empMeanAtExploration_of_measurable_div_const`; that full
  empirical-mean measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability` under an explicit
  Rat division-by-constant measurability contract.
- Extended Pro then chose `measurable_rat_div_const`; that Rat
  division-by-constant measurability wrapper now compiles locally in
  `BanditRLProof.RatMeasurability` under `[MeasurableSingletonClass Rat]`.
- `ETC.measurable_empMeanAtExploration` now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`, consuming
  `measurable_rat_div_const` to remove the explicit `hdiv_const` argument.
- Extended Pro then chose
  `ETC.measurable_empMeanAtExploration_coordinates`; that coordinate-shaped
  empirical-mean measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`.
- The next plausible leaf from that same Extended Pro response,
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`, now
  compiles locally in `BanditRLProof.Algorithms.ETCMeasurability` as an
  abstract commit-oracle argmax consumer.
- Extended Pro then selected Candidate A,
  `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`; that
  oracle-specialized pairwise-tail probability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate B,
  `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`; that
  oracle-specialized filtered-sum probability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`; that
  oracle-specialized if-zeroed nonbest probability wrapper now compiles
  locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC.measurableSet_commitOracle_ne_bestArm`; that oracle-selected
  wrong-event measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate C,
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD`, and its local compiled
  candidate `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`
  now compiles in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`; the local declaration
  `ETC.measurable_empMeanVector_of_forall_measurable` now compiles in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`; the local
  declaration
  `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean` now
  compiles in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`; the local
  declaration
  `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`
  now compiles in `BanditRLProof.Algorithms.ETCMeasurability`.

## Reward-Only Canonical Conditional Law Increment

- `RewardKernel.instIsMarkovKernel_historyStepKernelFamily` now exposes the
  existing reward-history step-family Markov proof to Mathlib trajectory APIs.
- `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure`
  now proves the selected-reward `condExpKernel.map` law on the canonical
  reward-only Ionescu-Tulcea trajectory measure.  The proof uses Mathlib
  `Kernel.condDistrib_trajMeasure`, the compiled countable-target bridge, and
  `RewardKernel.historyStepKernelFamily_apply`; it does not consume a packaged
  generated random-pair law.
- The contracts are standard Borel/countable reward regularity, a probability
  initial reward measure, and measurable policy context/state inputs.  The
  leaf is project-local and compiled with an external canary.
- The reward-prefix/generated finite-pair-prefix alignment is now compiled:
  the two prefixes induce equal comap measurable spaces,
  `History.historyFiltrationSucc` reduces to the reward-prefix comap, and the
  canonical selected-reward law is exposed on the generated finite-pair
  surface.
- `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim`
  now proves the required trim strengthening soundly: singleton event
  probabilities on both sides are conditioning-measurable, so Mathlib
  `ae_eq_trim_of_measurable` applies before countable singleton extensionality.
  This is not a reversal of `ae_of_ae_trim`.
- The trim bridge is specialized to the reward-only `historyStepKernelFamily`
  trajectory measure, transported through the generated finite-pair comap,
  and consumed by
  `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_trajMeasure`.
  The canonical reward-only process therefore constructs
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource` without an assumed
  selected-reward law.
- `historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure`
  now converts that selected source through the deterministic generated-action
  split, and
  `historyStepKernelFamily_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_trajMeasure`
  proves the full theorem-shaped successor finite-pair conditional law on the
  canonical reward-only process.  This endpoint no longer assumes an ambient
  selected-reward, random-pair, or partialTraj source.
- `historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure`
  now consumes this full law together with `CenteredRewardKernelLaw` and
  explicit ambient centered-reward integrability to prove the canonical
  successor conditional mean-zero theorem.  It does not require the practical
  source's pointwise raw bounds, which are generally unsuitable for the full
  ambient space `Nat -> Rat`.
- `historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure`
  now reaches the canonical concentration interface.  Measurable mean derives
  centered measurability, a finite-history ceiling derives trim-a.e. variance
  domination, and the integrated target-law transfer derives all-real ambient
  exponential integrability from the selected kernel MGF laws.  The theorem no
  longer accepts an ambient `h_integrable_exp` premise.
- The transfer is compiled generically in
  `hasCondSubgaussianMGF_of_condExpKernel_map_eq`: target-wise integrability and
  the common MGF ceiling feed `Measure.integrable_comp_iff`, with the inner norm
  integral bounded over the finite trim measure.  The same strengthening is
  exposed by centered, bounded, definitional, and practical raw-range source
  consumers.
- `generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted`
  now proves the zero-initialized successor centered-reward process adapted to
  generated shifted history.  The index-zero value is deterministic zero, so
  Mathlib's unconditional first-summand contract is discharged without adding
  an artificial initial reward law.
- `historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure`
  combines that adaptedness, the canonical successor conditional-MGF witnesses,
  and `condSubGaussian_sum_tail_ennreal_of_stronglyAdapted` into a canonical
  ENNReal Azuma-Hoeffding bound for the `Finset.range n` sum of centered rewards
  at indices `1..n-1`.
- `historyStepKernelFamily_centeredRewardSuccProcess_average_tail_ennreal_trajMeasure`
  now turns that sum tail into a canonical aggregate average tail: `m > 0`
  rewrites `eps <= sum / m` to `m * eps <= sum`, and `Finset.range (m + 1)`
  still contains exactly successors `1..m` because index zero is deterministic.
  It is deliberately not an arm-wise empirical-mean or confidence-radius
  theorem.  The complete-trace ambient transport route now compiles as
  `historyStepKernelFamily_selectedMeasure_condExpKernel_map_of_identDistrib_trajMeasure_trim`
  and
  `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_identDistrib_trajMeasure`:
  ambient reward-trace `IdentDistrib` with canonical `trajMeasure` transports
  the prefix/next joint law, recovers the ambient conditional distribution,
  and constructs the generated selected source that feeds the existing full
  `partialTraj` converter.  The recursive entry route now compiles as
  `historyStepKernelFamily_identDistrib_trajMeasure_of_condDistrib`,
  `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_condDistrib`,
  and `historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_of_condDistrib`:
  an initial reward marginal and all successor `condDistrib` laws determine the
  complete trajectory law, selected source, and full generated `partialTraj`
  source.  The generic uniqueness proof now lives in the foundation module
  `BanditRLProof.RewardTraceLaw`.  This route now reaches a concrete ambient
  concentration theorem:
  `centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource`
  derives the conditional MGF directly from the full source without raw/mean
  range bounds;
  `historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_of_condDistrib`
  specializes it to recursive laws; and
  `historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_condDistrib`
  derives ambient probability from the initial law, proves strong adaptedness,
  and returns the ENNReal Azuma-Hoeffding sum tail.  The next route is to derive
  those recursive conditional laws from a concrete algorithm/environment or
  align this tail with an arm/sample-count confidence surface; the `COND-EXPECT-REWARD`
  conversion-window and proof-obligation files mentioned by the retrieval
  index are currently absent and must be restored before their metadata is
  used.  The arbitrary-ambient `partialTraj` theorem-card row and final
  adaptive theorem remain open.

## ETC Next Leaf

The canonical bounded-Rat per-arm expected-regret endpoint and its external
exploration-prefix transport now compile. Equal prefix pushforwards through
`m*K-1` give equal generated ETC regret integrals, so the external law inherits
the same gap-weighted armwise tails without a max-gap union, full trajectory
equality, or suffix laws. An initial reward marginal plus successor
`condDistrib` laws now derive this prefix identity and return the per-arm RHS
directly on the original sample space. The scheduled exploration-arm wrapper
also compiles: it fixes the irrelevant context to `Unit`, rewrites the local
step kernel to the stationary arm law, and exposes no local kernel plumbing.
The full action/reward-history constant-law adapter now also compiles: it
projects complete pair-history/next-action conditions to reward prefixes and
extracts the initial marginal without changing the per-arm RHS. The raw
action-selected feedback-kernel adapter now also compiles, using a.e. scheduled
exploration actions and preserving the per-arm conclusion. This closes the
dependency-light bounded-Rat law route. The canonical concentration layer now
also compiles from direct per-arm centered `HasSubgaussianMGF` witnesses at a
common proxy: it builds the kernel law, generated/fixed-filtration reward
witnesses, and exact pairwise empirical-mean tail contract without bounded
support. That contract now also feeds concrete non-best commit fibers, named
finite Real tails, and the canonical gap-weighted per-arm Bochner expected-
regret theorem, with no max-gap collapse or arm union. Its exploration-prefix,
generic initial/successor conditional-law, and scheduled exploration-arm
consumers now also compile on arbitrary external reward processes. The public
scheduled endpoint fixes `Context := Unit` and requires neither bounded support
nor a caller-visible local kernel. The LML-shaped full action/reward-history
direct-MGF adapter now also compiles by marginalizing the initial constant law
and coarsening each complete pair-history/next-action condition to the reward
prefix. The action-dependent selected-kernel adapter now also compiles: raw
action-indexed kernels plus scheduled-action a.e. identities reduce to those
constant laws without changing the per-arm RHS. This closes dependency-light
direct-MGF `Rat` law transport. The new Real scalar regret/pull-count leaf below
closes the target-side bookkeeping mismatch, and its stationary-kernel
specialization now also compiles. The Real ETC count-to-probability endpoint
now compiles too: measurable `actionWithCommit` pull counts are integrable and
their expectation is exactly `m + (n - K*m) * P(commit=a)`. The canonical Rat
arm-law route now also compiles the exact LML exponential constant and the
matching per-arm expected-count bound. The canonical native Real
`Measure.infinitePi` route now compiles the same single-arm tail, expected
count, kernel gap, and full finite-sum regret bound directly for a Markov Real
kernel. Native Real finite-prefix factorization and external process transport
now compile too, including a direct scheduled-arm initial/successor
`condDistrib` endpoint. The next narrow route is mapping the actual
`IsAlgEnvSeq` stationary-environment fields to those compiled premises plus
upstream measurable-argmax action/tie equivalence; direct LML integration is
now the remaining source boundary rather than an optional concentration path.

## Exact ETC Route Update: Real Mean Regret

The completed `REAL-MEAN-REGRET-PULLCOUNT` leaf provides the exact-route Real
scalar bookkeeping surface in `BanditRLProof.RealMeanRegretPullCount`.
`integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount` rewrites the
Bochner expectation of `n * iSup mean - sum mean(action)` as the finite sum of
each `realMeanGap` times the expected pull count. It uses existing finite-sum,
fiber-cardinality, integrability, and Bochner wrappers and requires only
per-arm pull-count integrability.

That stationary Real reward-kernel specialization now compiles in
`BanditRLProof.RealKernelRegretPullCount`, including nonnegative kernel gaps and
the kernel-facing Bochner pull-count equality. The downstream
`REAL-ETC-EXPECTED-PULLCOUNT` leaf now closes pull-count integrability, exact
commit-fiber indicator integration, and the abstract probability-bound
consumer. `ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT` now also
closes the exact `exp (-m*gap^2/(4*sigma2))` arithmetic, canonical Rat-arm-law
commit-fiber bound, and matching per-arm expected-count endpoint.
`ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET` now maps those laws to a Markov Real
kernel, identifies its identity-integral gaps, and closes the full finite-sum
regret assembly. `ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT` now additionally
defines the Real exploration means and deterministic finite argmax directly,
proves their measurability without a countability assumption on Real score
vectors, and connects the resulting action to the exact expected-count
consumer. `ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET` now closes the native Real
canonical product-law concentration route through the exact full finite sum,
using `iIndepFun_infinitePi`, coordinate map laws, the common centered MGF
contract, and the existing Real kernel regret decomposition.
`ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET` now factors the entire
native action/regret through `Fin (m*K)` rewards, transports equal prefix laws,
and derives that equality directly from scheduled-arm initial and successor
conditional laws. `ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` now
also maps the upstream-shaped action-selected initial and complete pair-history
successor feedback laws into those scheduled laws, preserving the exact Real
finite-sum conclusion.

`ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` now identifies the strict
fold with Mathlib `List.argmax`, proves equality with the LML-shaped least-
encode `Nat.find` selector, combines round-robin exploration, commit, and
persistence into action equality, and consumes the selected feedback laws for
the exact native Real finite sum.

`ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` now mirrors the upstream
finite-history count/sum/mean surface, proves the `K*m-1` history score equals
the local exploration score under `ETC.arm_of_lt`-shaped action equality, and
feeds a history-shaped commit law directly into the exact finite-sum theorem.

`ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` now packages the precise
measurability, three-phase action, and stationary feedback-law consequences in
`ETC.RealStationaryETCSequence`. Its theorem projects that bundle into the
history-score endpoint and returns the exact LML-shaped finite sum.

The next narrow boundary is no longer mathematical field compatibility. It is
a task-level decision about importing actual LML symbols across ABRL's Lean/
mathlib `v4.29.1` and pinned LML's Lean `v4.32.0-rc1` toolchains. Any attempt
must isolate the dependency/toolchain and symbol-identity work; do not reopen
history arithmetic, tie semantics, reward laws, concentration, constants,
gaps, or finite sums, and do not call the upstream theorem imported meanwhile.

The active UCB theorem route now also advances through
`UCB-NATIVE-REAL-HISTORY-INDEX`. The new module compiles the exact Real
empirical mean, sample-path-dependent pull-count width, finite-history score,
least-encoded score action, measurability, maximality, and history/trace
alignment used by pinned `Bandits.UCB.regret_le`.

`UCB-FIXED-COUNT-PEELING-LAW` now compiles the source-faithful next stage. A
`FixedArmPrefixSource` records that selected rewards from an arm are exactly
the first `pullCount` entries of a latent arm stream. The adaptive pair event
is peeled over `k <= n` with the finite outer-measure union bound, and one
complete-stream `IdentDistrib` law transports all fixed-count events to a
canonical stream.

`UCB-ARM-STREAM-REWARD-SOURCE` now compiles the next-unused-coordinate part of
LML's array/stream model. For any action trace on a latent arm stream,
`rewardFromArmStream` reads the selected arm at its prior pull count, and a
horizon induction proves the exact selected-sum/prefix invariant. General
measurable and canonical adapters feed this construction directly into the
compiled peeling theorem.

`UCB-ARM-STREAM-PROCESS-LAW` now constructs the recursive source-faithful UCB
action, exact actual finite history, next-unused rewards, and canonical
stationary product arm-stream measure. `UCB-ARM-STREAM-INDEX-TAIL` specializes
product independence and fixed-sum sub-Gaussian concentration through positive
count peeling to the actual random-width lower/upper index events, ending at
the LML-shaped outer-measure bound `1 / (n+1)^(c-1)`.

`UCB-ARM-STREAM-EXPECTED-PULLCOUNT` closes recursive finite-history/action/
reward measurability and the actual-width count consumer. It proves positive
initial counts, deterministic score/gap threshold algebra, the selected-large
bad-event union, its `2*constSum` measure sum, and the ENNReal lower-integral
bound with threshold `ceil(8*c*sigma2*log(n+1)/gap^2)+1`. It also proves
pull-count integrability and converts that endpoint to the exact LML-shaped
Real Bochner expected-count bound.

`UCB-ARM-STREAM-LML-REGRET` now compiles the complete canonical recursive UCB
theorem with the exact pinned gap-weighted finite-sum RHS. The only remaining
generic-process step, `UCB-EXTERNAL-ACTION-LAW-LML-REGRET`, also compiles: an
external action process with complete trace law `IdentDistrib` to the canonical
process inherits exactly the same RHS through measurable regret composition
and integral transport. `UCB-EXTERNAL-ARM-STREAM-SOURCE-LAW-LML-REGRET` now
constructs that action law from a latent arm stream with canonical complete law
and a.e. recursive action generation, but the pinned-source audit shows this is
an optional stronger adapter rather than the `IsAlgEnvSeq` route.
`UCB-EXTERNAL-ACTION-REWARD-TRAJECTORY-LAW-LML-REGRET` now compiles the faithful
route endpoint: complete observable pair-trajectory `IdentDistrib` projects to
the canonical action law and exact RHS.
`UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET` now constructs that complete
law from a common initial pair marginal and all common successor pair
`condDistrib` kernels. Its generic support proves full trace-law equality from
finite-prefix laws using Mathlib projective-limit uniqueness.
`UCB-CANONICAL-ACTION-REWARD-CONDDISTRIB-LML-REGRET` now removes the exposed
common-law bundle by choosing the canonical time-zero pushforward and canonical
regular conditional kernels internally. Remaining work is to derive the
external initial/successor equalities from upstream environment/action
contracts or import the literal trajectory witness. Do not reconstruct unused
arm arrays or substitute the deterministic proxy route.
## Latest UCB Compatibility Leaf

`UCB-ISALGENVSEQ-SPLIT-LAWS-LML-REGRET` is compiled. The route now accepts the
initial action law, initial feedback conditional law, successor action policy,
and successor feedback conditional law separately, combines them by
`Kernel.compProd`, obtains full observable trajectory `IdentDistrib`, and
returns the exact pinned UCB regret RHS. The next narrow UCB leaf is a concrete
producer for those four fields or a deliberate LML toolchain import decision;
do not reopen concentration or reconstruct latent unused-arm arrays.

The follow-on field compatibility theorem is also compiled in
`UCBRealLMLCompat`: `RealStationaryUCBSequence` bundles the source-shaped
fields, the canonical arm-stream process proves the bundle is inhabited, and
`regret_le_of_realStationaryUCBSequence` gives the exact pinned RHS. The next
UCB work item must therefore be a real external producer/import, not another
adapter around the same assumptions.

## Latest Thompson Process Leaf

`LOCAL-LEAF-TS-RECURSIVE-FINITE-HISTORY-DENSITY` is compiled. The new
`HistoryAlgorithm`/`HistoryEnvironment` process contract accepts separate
initial and successor action/feedback laws, assembles their pair kernels, and
proves by induction that every finite pair-history law is the reference law
weighted by `historyDensity`. This is the theorem-level local analogue of
the pinned LML algorithm-density process theorem.

The conditional-on-environment realization now also compiles:
`ConditionalHistoryAlgorithmDensitySource` requires the actual/reference
`condDistrib id` sample laws to satisfy the process contracts a.e.;
`condDistrib_finitePairHistory_eq_withDensity_of_conditionalProcessSource`
derives the conditional history law, and the direct consumer closes
finite-prefix Thompson probability matching.

The split-law producer layer now compiles as well.
`ConditionalHistoryAlgorithmEnvironmentSplitSource` records the initial action,
initial feedback, successor policy, and successor feedback laws under each
conditional sample measure. `conditionalHistoryAlgorithmDensitySource_of_split`
gathers the Nat-indexed laws with `ae_all_iff`, assembles both process contracts,
and the direct split-source consumer closes finite-prefix probability matching.

Next build one concrete recursive TS/reference trajectory that proves those four
split fields, then establish global sampler coupling. Do not re-assume the
combined process or density law, add pointwise RN-finiteness, or jump to
Bayesian regret.

## Latest Thompson Concentration Leaf

`LOCAL-LEAF-TS-STATIONARY-EMPIRICAL-MEAN-TAIL-TRANSPORT` is compiled. The
stationary latent-stream route now reaches the decomposition-facing canonical
trajectory measure: augmented-prior mixing, positive-count peeling, clipped
radius algebra, exact finite exponential summation, and product-associativity
transport yield both fixed-arm empirical-mean confidence failures with bound
`n * delta`.

The next single leaf is `TS-CLIPPED-UCB-CONCENTRATION-EXPECTATIONS`. It must
turn those fixed-arm events into finite arm/time controls and the two clipped
score expectations in `integral_trajectoryBayesMeanRegret_eq_add_clippedUCB`.
Do not reopen latent-stream support, stationary kernel laws, zero-count
peeling, prior mixing, posterior matching, or the decomposition.

## Latest Thompson Horizon Leaf

`LOCAL-LEAF-TS-STATIONARY-SELECTED-ARM-HORIZON-LOWER-TAIL` is compiled. The
stationary canonical trajectory now has a measurable environment-dependent arm
horizon lower-tail bound of `(n - 1) * delta`. Times are collapsed by realized
pull count on the latent stream before the finite union, preserving the pinned
LML constant.

The best-action-minus-clipped-UCB finite-horizon expectation bound now compiles;
the next single leaf is the selected-action clipped-UCB-minus-mean expectation.
It must combine a deterministic clipped-score summation inequality with a
finite-arm horizon upper-confidence event, without reopening the lower-tail
transport proved here.

## Latest Thompson Expectation Theorem

`LOCAL-LEAF-TS-CLIPPED-UCB-BEST-ACTION-EXPECTATION` is compiled with the exact
bound `(u-l) * (n-1) * n * delta`. It consumes the measurable best-action
horizon lower tail, splits the canonical integral into bad-event/complement
pieces, and uses the existing `[l,u]` score and mean contracts.

The next theorem is the selected-action clipped-UCB-minus-mean expectation.
Required supporting obligations are now explicit: a pathwise finite-horizon
clipped-UCB sum inequality and a finite-arm horizon upper-confidence event with
cost `K * (n-1) * delta`. After that theorem, combine both expectations with
the compiled Thompson decomposition.

## Latest Thompson Stationary Final Theorem

The selected-action expectation and stationary `TS-FINAL` route now compile.
The deterministic leaf reindexes the time sum by arm/pull count and bounds the
confidence widths; the probability leaf collapses bad times by realized count
before unioning over arms, preserving the exact `K*(n-1)*delta` cost. The
second expectation therefore matches pinned LML, and the general-`delta`
decomposition join is compiled.

The endpoint
`stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le`
uses `delta = 1/n^2` and proves
`(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)`. The next Thompson work must be a
genuinely broader model adapter or literal cross-toolchain LML import; do not
create another wrapper around this same stationary theorem or claim it covers
nonstationary, contextual, or RL settings.

### EXP3 route update: observed roundwise moments

`BanditRLProof.Exp3PredictableMoments` closes the next concrete EXP3 route
step. Its public theorem
`sampledPredictableObservedSuccessor_first_second_moment` states the one-round
first and second estimator moments directly in terms of the scalar reward
stored in the sampled trajectory, while the right sides expose the full
predictable loss vector. Supporting compiled APIs cover global next-pair
`condDistrib`, initial/successor deterministic feedback support, the retained
`(Env,prefix)` finite-action source, and the `gamma / |arms|` regularity floor.
The finite-horizon integral summation now compiles. Its sampled-Hedge,
exploration-bias, integrability, and expected-regret consumers also compile
downstream, including the tuned square-root theorem.

### EXP3 sampled Hedge route update

`EXP3-SAMPLED-HEDGE` is compiled in `BanditRLProof.Exp3SampledHedge`. The
inclusive sampled score now agrees with deterministic Hedge cumulative loss
at the correctly shifted `n + 1` index; the pure Hedge distribution agrees
with normalized sampled-score weights; and the concrete trajectory
probability is explicitly their uniform exploration mixture. Under pathwise
nonnegative scalar feedback, `sampledHistoryScore_hedge_regret_le` supplies the
finite-horizon second-order comparator inequality. The route uses the existing
sampled-score recursion, `Preorder.frestrictLe`, `cumulativeLoss_succ`, finite
sum congruence, and the compiled generalized Hedge theorem. Next work should
assemble one finite-horizon a.e. `[0,1]` reward-support event, prove the
pure-Hedge/exploration-mixed bias inequalities, and integrate; parameter
optimization and the final EXP3 theorem remain later.

### EXP3 predictable Hedge a.e. update

`EXP3-PREDICTABLE-HEDGE-AE` is compiled. Existing time-zero and successor
selected-feedback laws now yield one common finite-horizon a.e. event on which
all observed rewards are nonnegative. The generated sampled trajectory
therefore satisfies the concrete second-order Hedge inequality almost surely,
with either `cumulativeLoss` or inclusive `sampledHistoryScore` as comparator
surface. This closes the reward-sign law transport. The next theorem route is
the deterministic exploration bridge: compare pure Hedge `q_t` terms against
the actual mixture `p_t = (1-gamma)q_t + gamma/|A|`, establish integrability,
and combine those facts with the finite-horizon moment theorem. Eta/gamma
optimization remains after the integrated bound.

### EXP3 exploration-bias update

`EXP3-EXPLORATION-BIAS` is compiled in
`BanditRLProof.Exp3ExplorationBias`. The concrete exploration mixture now
yields the coordinate comparison `q_t(a) <= p_t(a)/(1-gamma)`, the resulting
pure-q versus explored-p estimator-square bound, and the predictable-loss
bias `p_t dot loss_t <= q_t dot loss_t + gamma`. One finite-horizon theorem
sums both pathwise inequalities. It needs only finite nonempty arms,
decidable equality, the predictable `[0,1]` contract, and
`0 <= gamma < 1`; it has no measure or integrability premise. The next narrow
route was adaptive pure-q first-moment transport plus integrability on the
generated trajectory law; that bridge, the integrated expected-regret consumer,
the large-horizon eta/gamma square-root optimization, the realized selected-loss
expectation adapter, and the uniform-horizon clipped-rate consumer now compile.

### EXP3 predictable expected-regret update

`EXP3-PREDICTABLE-EXPECTED-REGRET` is compiled in
`BanditRLProof.Exp3PredictableIntegration`. The generated predictable EXP3
trajectory now satisfies
`E[sum_t p_t dot loss_t - sum_t loss_t(comparator)] <= log|A|/eta +
eta/(1-gamma)*|A|*T + gamma*T`. The proof uses the new cross-weight identity
`E_p[q dot hat-loss] = q dot loss`, conditional-law transport, measurable
pure-Hedge sources, finite-horizon Bochner integration, the a.e. sampled-Hedge
bound, exploration bias, and the exact estimator second moment.

The theorem requires a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty arms, predictable measurable
`[0,1]` losses, a supported comparator, `eta > 0`, and `0 < gamma < 1`; it does
not assume independence, stationarity, oblivious losses, or concentration.
The route is root-imported and externally instantiated in `Tests.Basic`.
Retrieval is recorded by `LOCAL-LEAF-EXP3-PREDICTABLE-EXPECTED-REGRET` and its
Mathlib/local/paper dependencies. Its deterministic parameter and square-root
consumers now compile; do not reopen the law or integrability layers. The
realized selected-loss adapter and uniform-horizon clipped-rate endpoint also
compile downstream.

### EXP3 tuned expected-regret update

`EXP3-TUNED-EXPECTED-REGRET` is compiled in
`BanditRLProof.Exp3ExpectedRegret`. First,
`expectedRegretBudget_le_four_mul_gamma_mul_horizon` proves the abstract
`4*gamma*T` simplification for `eta=gamma/K`, `gamma<=1/2`, and
`K*log K<=gamma^2*T`. Then `tunedExplorationRate=sqrt(K*log K/T)` and
`tunedLearningRate=gamma/K` are shown positive, within the exploration cap,
and algebraically equivalent to the `sqrt(K*T*log K)` scale. The public
generated-process theorem gives expected predictable regret at most
`4*sqrt(K*T*log K)` when `2<=K`, `0<T`, and `4*K*log K<=T`.

The proof adds only Mathlib Real log/sqrt and ordered-field algebra to the
compiled expectation route; probability, measurability, integrability, and
law assumptions are unchanged. Root import and a complete external canary
compile. The realized selected-loss and uniform-horizon clipped-rate
presentation adapters also compile downstream.

### EXP3 realized expected-regret update

`EXP3-REALIZED-EXPECTED-REGRET` is compiled in
`BanditRLProof.Exp3RealizedRegret`. It defines the actual generated scalar loss,
uses the existing deterministic-feedback law to identify it almost surely with
the selected predictable coordinate, and transports the initial/successor
sampled-action conditional laws into the one-round identity
`E[loss_t(A_t)] = E[p_t dot loss_t]`. Finite-horizon Bochner summation then
rewrites the compiled unoptimized and tuned expected-regret theorems.

The public endpoints cover both the original unoptimized budget and the
large-horizon `4*sqrt(K*T*log K)` bound for actual generated scalar losses.
They retain the existing probability/Standard-Borel/predictable-`[0,1]`
contracts and add no independence, stationarity, concentration, or supplied
integrability assumption. Root import, declaration canaries, and a full
external tuned realized-regret application compile. Its all-horizon clipped-rate
consumer now compiles downstream.

### EXP3 uniform-horizon realized-regret update

`EXP3-UNIFORM-HORIZON-REALIZED-REGRET` is compiled in
`BanditRLProof.Exp3UniformRegret`. The new support theorem bounds actual
generated realized regret by the horizon for any legal rates. The module then
sets `gamma=min(1/2,sqrt(K*log K/T))`, `eta=gamma/K`, packages
`clippedPredictableTrajectoryKernel`, and proves
`sampledPredictable_clippedRealizedExpectedRegret_le_min`:
`E[R_T] <= min(T,4*sqrt(K*T*log K))` for every `T : Nat`, including `T=0`.

The proof uses only the compiled realized-to-mixed expectation transport,
finite-horizon `[0,1]` loss budget, Mathlib finite-sum integration, Real
log/sqrt, and ordered-ring algebra. It splits on `4*K*log K<=T`; the large
branch rewrites the clipped parameters to the tuned parameters, while the
small branch proves the square-root expression is at least `T`. Contracts are
the existing probability/Standard-Borel/predictable-`[0,1]` assumptions,
`2<=K`, and a supported comparator. No positive-horizon, independence,
stationarity, concentration, or manual integrability assumption is added.

The leaf is root-imported, externally instantiated in `Tests.Basic`, indexed by
`LOCAL-LEAF-EXP3-UNIFORM-HORIZON-REALIZED-REGRET`, and marked `leanCompiled`.
This closes the all-horizon expected realized-regret presentation for the
generated predictable adversary. High-probability bounds, stochastic rewards,
non-predictable adversaries, and other EXP3 variants remain separate routes.

### Countably-generated conditional-state freeze update

`COND-EXPECT-REWARD-CONDEXPKERNEL-MEASURABLE-FREEZE` is compiled in
`BanditRLProof.ConditionalExpectationReward`. The APIs
`condExpKernel_map_eq_deterministic_of_measurable` and
`condExpKernel_map_eq_dirac_of_measurable` show that every
conditioning-measurable map into a countably generated target is frozen by the
conditional-expectation kernel under the trimmed conditioning measure.

This removes the earlier `Countable` obstruction for Real-valued EXP3 history
prefixes. The route is entirely Mathlib-backed through the diagonal
composition-product law and finite-kernel a.e. uniqueness. It remains a
support leaf: its generated EXP3 successor-action consumer and one-step
realized-deviation conditional MGF now compile in the downstream concentration
leaf. Initial-time alignment and strongly adapted finite-sum assembly are still
required before invoking Azuma. No high-probability regret claim is made here.

### EXP3 successor realized-deviation conditional-MGF update

`EXP3-REALIZED-DEVIATION-SUCC-COND-MGF` is compiled in
`BanditRLProof.Exp3RealizedConcentration`. The generated predictable EXP3 law
now has a direct successor witness
`sampledPredictableRealizedDeviation_succ_hasCondSubgaussianMGF`: conditioned
on `(Env, finite pair prefix)`, realized loss minus the exploration-mixed
predictable loss is sub-Gaussian with the `[0,1]` Hoeffding proxy.

The new finite-support bridge upgrades successor-action `condDistrib` evidence
to the full `condExpKernel` action map without assuming a countable ambient
action type. The measurable-state freeze fixes Env/history, the finite action
law supplies the exact mixed mean, and the generated feedback equality carries
the result to scalar realized loss. The next narrow leaf is initial-time
alignment plus a zero-shifted strongly adapted process; only after that should
the existing Azuma sum-tail wrapper be invoked. This update is not yet a
finite-horizon or high-probability EXP3 regret theorem. The finite-horizon
concentration part has since compiled in the downstream update below.

### EXP3 finite-horizon realized-deviation tail update

`EXP3-REALIZED-DEVIATION-SUM-TAIL` is compiled in
`BanditRLProof.Exp3RealizedDeviationTail`. The theorem
`sampledPredictableRealizedDeviation_sum_tail_ennreal` packages the initial and
successor generated action laws into a single shifted, strongly adapted
process and applies the existing Mathlib-backed conditional sub-Gaussian sum
tail theorem. Its exact variance proxy is
`horizon * Concentration.intervalVarianceProxy 0 1`.

This closes the probabilistic finite-sum deviation route without a countable
ambient action type, independence, stationarity, or user-supplied exponential
integrability. Its delta confidence-radius consumer now compiles below.

### EXP3 realized-deviation delta-confidence update

`EXP3-REALIZED-DEVIATION-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3RealizedConfidence`. It exposes the standard one-sided
radius `sqrt(2 * V_T * log(1/delta))`, with
`V_T = horizon * intervalVarianceProxy 0 1`, and proves the corresponding
generated-trajectory event has measure at most `delta`.

The attempted next-step audit also sharpened the actual route to full
high-probability regret. `sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae`
controls pure-`q` and comparator importance-weighted estimators, not the true
predictable losses appearing in regret. Therefore the next theorem route must
construct conditional concentration for the comparator estimator and the
pure-`q` cross-weight estimator, and control the random second-moment sum (or
switch to an EXP3.P estimator). A direct deterministic event rewrite would be
mathematically invalid and must not be used.

### EXP3 comparator-estimator delta-confidence update

`EXP3-COMPARATOR-ESTIMATOR-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3ComparatorConfidence`. The fixed supported comparator's
observed importance-weighted loss is centered by the true predictable
comparator loss, with per-round proxy
`intervalVarianceProxy 0 (1 / (gamma / |arms|))`; the finite-horizon delta
radius is the corresponding `sqrt(2 * V_T * log(1/delta))`.

This closes the first probabilistic obligation identified by the Hedge
statement audit. The pure-`q` cross-weight obligation now compiles downstream.

### EXP3 pure cross-weight delta-confidence update

`EXP3-PURE-CROSS-WEIGHT-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3PureConfidence`. It first centers the pure-Hedge weighted
observed importance estimator by the predictable pure-Hedge loss, then negates
the conditional MGF to expose the regret-required predictable-minus-observed
tail. Generated zero/successor instances and finite-history adaptedness compile,
with finite-horizon delta radius using the same range proxy
`intervalVarianceProxy 0 (1 / (gamma / |arms|))`.

This closes the second probabilistic obligation from the Hedge statement audit.
The random estimator-square obligation now compiles downstream.

### EXP3 predictable high-probability regret update

`EXP3-PREDICTABLE-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3HighProbabilityRegret`. Instead of postulating a separate
square concentration theorem, it proves generated rewards are in `[0,1]` a.e.
and uses the exact selected-square formula plus the exploration floor to obtain
`sum square <= horizon/(gamma/|arms|)` a.e. The final event assembly combines
sampled Hedge, exploration bias, pure-q confidence, and comparator confidence;
`measure_mono_ae` and `measure_union_le` first give the explicit two-event
bound. The primary wrapper allocates `delta / 2` to each confidence event and
uses `ENNReal.ofReal_add` to give total failure probability
`ENNReal.ofReal delta`.

The generated realized selected-loss consumer now compiles downstream.
Separately, the current range proxy is quadratic in `|arms|/gamma`, so
ideal-rate EXP3 still needs a variance-sensitive/Freedman analysis or an EXP3.P
estimator modification.

### EXP3 realized high-probability regret update

`EXP3-REALIZED-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3RealizedHighProbabilityRegret`. The route adds the compiled
realized-minus-exploration deviation to the predictable pseudo-regret theorem.
The pathwise finite-sum identity is proved locally, the realized bad event is
contained in the union of the two compiled bad events, and `measure_union_le`
gives the raw three-term failure budget.

The public total-delta wrapper evaluates both the predictable budget and the
realized confidence radius at `delta / 3`, matching the three underlying
pure-q, comparator-estimator, and realized-deviation events. It controls the
actual scalar losses in the generated trajectory with total failure probability
`ENNReal.ofReal delta`. The next EXP3 high-probability target should therefore
be rate optimization or a variance-sensitive/EXP3.P route, not another event
assembly wrapper.

### Fixed-tilt conditional-MGF concentration update

`CONCENTRATION-FIXED-TILT-CONDITIONAL-MGF-SUM-TAIL` is compiled in
`BanditRLProof.ConcentrationFixedMGF`. It introduces kernel, measure, and
`condExpKernel` fixed-tilt MGF witnesses, proves additive composition through
successive kernels, closes strongly-adapted finite sums by induction, and
converts the resulting MGF budget to
`exp (-tilt * eps + sum psi)` with Mathlib's exponential Markov inequality.

The generic layer deliberately assumes all-tilt exponential integrability but
only one-tilt MGF domination. It assumes neither bounded increments nor a
variance process. Repository-wide Mathlib retrieval found no existing
Freedman/Bernstein concentration primitive. The one-step fixed-comparator EXP3
source and generated finite-horizon consumer now compile in the adjacent leaf;
broader ideal-rate claims still require its remaining downstream consumers.

### EXP3 fixed-comparator variance-sensitive update

`EXP3-COMPARATOR-BERNSTEIN-FIXED-TILT` is compiled in
`BanditRLProof.Exp3ComparatorBernstein`. The finite action calculation gives
the exact centered estimator second moment and bounds it by the reciprocal
exploration floor. Combined with the quadratic exponential remainder on
`|tilt * X| <= 1`, this yields the one-step budget `tilt^2 / epsilon` for
`0 <= tilt <= epsilon`.

The result is transported through the generated initial and successor action
laws, converted from predictable to observed feedback a.e., and summed along
the existing strongly adapted filtration. The resulting finite-horizon tail
has exponent `-tilt * threshold + horizon * tilt^2 / epsilon`, with
`epsilon = gamma / |arms|`. Its delta-shaped consumer now compiles below; the
analogous pure-cross estimator bound also compiles below. The remaining route
obligation is the improved high-probability EXP3 regret assembly.

### EXP3 fixed-comparator variance-sensitive delta update

`EXP3-COMPARATOR-BERNSTEIN-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3ComparatorBernstein`. It optimizes the fixed-tilt exponent
with a square-root tilt in the quadratic regime and the legal boundary tilt in
the large-budget regime. For `budget = max(log(1/delta),0)`, the resulting
radius is `2*sqrt(T*budget/epsilon)+budget/epsilon` and the generated bad event
has ENNReal probability at most `ofReal(delta)`.

The theorem holds for every finite horizon and every positive delta. The next
specific theorem route, the pure-cross variance-sensitive delta tail in the
sign consumed by Hedge regret, is now compiled below.

### EXP3 pure-cross variance-sensitive delta update

`EXP3-PURE-CROSS-BERNSTEIN-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3PureBernstein`. Its finite-law calculation identifies the
cross-weighted raw score as `q(a) * loss(a) / p(a)` at the sampled action and
bounds the centered second moment by `1 / epsilon`, using both finite
distribution contracts and the sampling floor.

The module proves the fixed positive-tilt MGF directly for
`pure predictable loss - cross-weighted estimator`, transports it through the
generated conditional action laws, rewrites the latent estimator to observed
feedback a.e., and sums the existing strongly adapted process. Reusing the
compiled scalar optimizer gives radius
`2*sqrt(T*max(log(1/delta),0)/epsilon)+max(log(1/delta),0)/epsilon` for every
`delta>0` and arbitrary finite horizon. The next improved-regret obligation is
now compiled below. The audit showed that the current deterministic
`horizon/epsilon` Hedge-square bound can be reused honestly; improving that
term is a distinct ideal-rate obligation.

### EXP3 predictable Bernstein high-probability regret update

`EXP3-PREDICTABLE-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinHighProbabilityRegret`. It replaces both
range-Hoeffding confidence radii in the generated predictable regret assembly
with the compiled variance-sensitive pure-cross and comparator radii. The raw
theorem exposes two equal-delta failures; the primary theorem evaluates both
radii at `delta/2` and bounds total failure by `ENNReal.ofReal delta`.

The assembly continues to use the pathwise
`sum observedMixedSquaredImportanceWeightedLossAt <= horizon/epsilon` bound,
so no unproved square-term concentration is hidden. It works for arbitrary
finite horizon, including zero, and only requires `delta>0`. Its realized
selected-loss consumer now compiles below; the current theorem is not a general
Freedman or ideal EXP3.P result.

### EXP3 random estimator-square Bernstein regret update

`EXP3-RANDOM-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3RandomSquareHighProbabilityRegret`. The generated moment
upper bound gives `E[sum mixedSquare] <= |arms|*T`; after proving the sum
nonnegative, measurable, and integrable, Mathlib Markov yields threshold
`|arms|*T/deltaSquare` with failure `deltaSquare`.

The complete predictable-regret endpoint includes this square event with the
pure-cross and comparator Bernstein events. Its total-delta wrapper allocates
`delta/3` to each, replacing the deterministic `|arms|*T/gamma` square term by
`3*|arms|*T/delta`. This removes one genuine reciprocal-exploration obstruction.
Its generated realized-regret assembly now compiles below. Beyond that,
logarithmic-confidence square control and the two exploration-floor confidence
radii still require stronger variance-process or EXP3.P machinery.

### EXP3 random-square Bernstein realized-regret update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedHighProbabilityRegret`. The
pathwise identity adds cumulative realized-minus-predictable deviation to the
compiled random-square predictable regret. The raw endpoint keeps separate
allocations for the square, both Bernstein confidence events, and realized
deviation; the public wrapper assigns `delta/4` to each.

This closes the generated selected-loss consumer without reintroducing the
deterministic `T/epsilon` Hedge-square bound. Its learning-rate tuning now
compiles below. The remaining rate work must account honestly for both
exploration-floor Bernstein radii and the bounded-loss realized radius rather
than labeling the result ideal EXP3.P or Freedman.

### EXP3 random-square realized learning-rate tuning update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-TUNING` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedTuning`. The explicit choice
`eta=sqrt(log K*(delta/4)/(T*K))` exactly balances entropy against the
unamplified Markov-square term. Under `gamma<=1/2`, stability increases the
pair to at most `3*sqrt(4*K*T*log K/delta)`.

The public generated tail retains `gamma*T`, both Bernstein radii, and the
realized-deviation radius verbatim, so it needs no cubic or quadratic dominance
contracts and works for every positive delta. This closes eta optimization,
while the adjacent explicit route now chooses gamma without hiding the Markov
`1/sqrt(delta)` contribution.

### EXP3 random-square realized explicit gamma update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning`. It uses the
maximum of the confidence cube-root scale and realized square-root scale,
clipped at `1/2`, and proves the generated tail at
`3*sqrt(4*K*T*log K/delta)+8*gamma*T`. Two factor-eight horizon inequalities
show clipping is inactive and discharge the exact cubic/quadratic contracts.

This advances the random-square route from caller-selected gamma to a concrete
large-horizon schedule. The adjacent all-horizon consumer now covers the
active-clip branch with a coarse pathwise fallback; stronger square/variance
process concentration remains necessary for a sharp replacement.

### EXP3 random-square realized all-horizon update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedAllHorizon`. It branches on the
same two large-horizon inequalities used by the explicit schedule. The true
branch invokes the refined random-square threshold; the false branch reuses
the generated a.e. regret bound and has zero failure probability at `T+1`.

This removes caller-managed regime selection and covers every positive
horizon. It does not improve the active-clipping rate: the fallback is coarse,
and the refined branch still contains Markov `1/sqrt(delta)` and bounded-loss
Hoeffding/Azuma terms. The next genuine rate advance must strengthen the random
square or predictable variance-process concentration rather than repackage the
same branch theorem as Freedman or EXP3.P.

### EXP3 realized regret with Bernstein predictable confidence update

`EXP3-REALIZED-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinRealizedHighProbabilityRegret`. The pathwise
realized-regret decomposition is unchanged, but its predictable component now
uses the compiled pure-cross and fixed-comparator Bernstein confidence radii.
The primary theorem allocates `delta/3` to those two events and the existing
realized-minus-predictable deviation event, yielding total failure probability
`ENNReal.ofReal delta` for generated selected scalar loss.

The realized-deviation event still uses its bounded `[0,1]` Hoeffding/Azuma
radius and therefore keeps the positive-horizon contract. The Hedge-square
contribution also remains the deterministic `horizon/epsilon` bound. The next
route is no longer event assembly: it is a tuning/rate audit that must decide
whether the retained square term permits a meaningful parameterized corollary,
without relabeling this theorem as general Freedman or ideal EXP3.P.

### EXP3 Bernstein tuning update

`EXP3-BERNSTEIN-TUNED-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinTuning`. With
`eta=sqrt(log K * gamma/(T*K))`, the full generated realized Bernstein budget
at `delta/3` is at most `11*gamma*T` under explicit cubic arm-log/confidence
contracts and the realized quadratic contract. The public endpoint transfers
that deterministic comparison through the existing total-delta theorem by
`measure_mono`.

This audit rules out reusing the expected-regret choice `eta=gamma/K`: with
the retained pathwise estimator-square bound, that choice leaves a linear
term. The compiled theorem instead exposes the honest `T^(2/3)`-type regime.
Its explicit clipped cube-root/max consumer now compiles below. An ideal
`sqrt(K*T)` theorem still requires a stronger square/variance route such as
EXP3.P or Freedman-style control.

### EXP3 explicit Bernstein schedule update

`EXP3-EXPLICIT-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinExplicitTuning`. The schedule is
`min(1/2,max((K log K/T)^(1/3),max((K log(3/delta)/T)^(1/3),
sqrt(2*v*log(3/delta)/T))))`, where `v=intervalVarianceProxy 0 1`. Three
large-horizon premises prove clipping inactive and synthesize every dominance
contract consumed by the `11*gamma*T` tail.

The active-clip short-horizon branch now compiles in
`BanditRLProof.Exp3BernsteinAllHorizon`. The generated realized loss is at most
one almost surely and comparator loss is nonnegative, yielding regret at most
`T` almost surely and a zero-probability bad event at `T+1`. The all-horizon
endpoint branches between this fallback and the explicit `11*gamma*T` theorem
without asking the caller for large-horizon proofs.

The remaining rate gap is substantive: the `T+1` branch is coarse, and the
deterministic estimator-square plus bounded realized-deviation route does not
give ideal `sqrt(K*T)` high-probability regret. The next concentration leaf
should target random estimator-square/variance-process control or an EXP3.P
algorithmic correction, not another clipping wrapper.

### Current EXP3 square-process advance

`EXP3-MIXED-SQUARE-EXPONENTIAL-CONFIDENCE` is now compiled. The generated
observed mixed-square sum has a delta-shaped exponential tail at
`K*T + sqrt(2*T*intervalVarianceProxy(0,K/gamma)*log(1/delta))`. The route
uses the exact finite-action conditional mean, frozen-history
`condExpKernel` transport, a strongly-adapted centered process, and the
existing observed/predictable a.e. score equality.

The adjacent predictable-regret consumer now replaces
`sampledPredictableObservedMixedSquared_sum_tail_markov` with this exponential
tail, and the realized selected-loss consumer also compiles. Both preserve the
existing eta/gamma parameters; the exact learning-rate retuning now compiles
below.
That consumer must preserve the honest `(K/gamma)^2` interval proxy; a
variance-sensitive Freedman square-process theorem remains a separate target.

The exponential square tail is now consumed by
`Exp3MixedSquareExponentialHighProbabilityRegret`. The generated predictable
regret theorem uses the square threshold `K*T + radius`, the existing two
Bernstein confidence events, and a `delta/3` union bound. Thus the earlier
Markov `K*T/delta` contribution is no longer present in this theorem route.

`Exp3MixedSquareExponentialRealizedHighProbabilityRegret` now adds the
generated realized-minus-predictable deviation to this predictable theorem.
Its total-delta wrapper allocates `delta/4` to the exponential square,
pure-cross Bernstein, comparator Bernstein, and bounded realized-deviation
events. `Exp3MixedSquareExponentialRealizedTuning` now performs the fresh
learning-rate balance without reusing the old Markov formula: it sets
`S=K*T+squareRadius(delta/4)` and `eta=sqrt(log K/S)`, yielding the threshold
`3*sqrt(log K*S)+gamma*T` plus the two Bernstein and realized radii.

`Exp3MixedSquareExponentialRealizedExplicitTuning` now supplies that concrete
consumer. It uses a clipped maximum of an arm square root, a mixed-square
sixth root, a confidence cube root, and a realized square root, while retaining
the exact eta balance above. Under four explicit horizon contracts the
generated realized tail has threshold `14*gamma*T`. The sixth root follows
from the exact `(K/(2*gamma))^2` interval proxy and records that route cost
honestly. After multiplication by `T` it has square-root horizon scaling; the
current overall `T^(2/3)` limitation comes from the Bernstein confidence
cube-root component, so this is still not an ideal EXP3.P claim.

`Exp3MixedSquareExponentialRealizedAllHorizon` now consumes the explicit leaf.
It names the exact four-contract regime and branches between the refined
explicit threshold, already bounded by `14*gamma*T`, and the strict `T+1`
zero-probability fallback. The generated theorem therefore covers every
positive horizon for `0<delta<=1` without a caller-supplied regime proof. It
is root imported and externally instantiated in `Tests.Basic`.

This closes the active-clipping presentation only at a deliberately coarse
fallback.

`Exp3MixedSquareBernstein` now supplies the first substantive square-process
improvement. The exact finite-law centered second moment is at most
`K/epsilon`, while the centered range remains `1/epsilon`; a two-parameter
fixed-tilt optimizer therefore gives the generated observed-square radius
`2*sqrt(T*(K/epsilon)*log_+) + log_+/epsilon` for every natural horizon.
`Exp3MixedSquareBernsteinHighProbabilityRegret` consumes that tail in the
three-event generated predictable-regret theorem, with root imports and full
external canaries for both endpoints. The adjacent
`Exp3MixedSquareBernsteinRealizedHighProbabilityRegret` now closes generated
realized selected-loss assembly by adding the compiled realized-deviation
radius and allocating `delta/4` across the four underlying events. The new
`Exp3MixedSquareBernsteinRealizedTuning` module also closes exact eta balancing
against `S=K*T+mixedSquareBernsteinRadius(delta/4)`, yielding the generated
threshold `3*sqrt(log K*S)+gamma*T` plus the three remaining confidence radii.

The explicit gamma schedule and all-horizon consumer for this tuned budget now
compile below. A stronger random predictable-quadratic-variation theorem
remains a separate route. The compiled fixed-tilt result and its consumers
should not be relabeled as anytime/general Freedman or ideal EXP3.P; the
linear `log_+/epsilon` correction and bounded-loss Hoeffding/Azuma realized
radius remain visible.

The first supporting leaf on that separate route now compiles as
`Exp3MixedSquarePredictableVariance`. It exposes the exact finite-law centered
second moment as a measurable generated process, proves the finite-action
integral representation and `K/(gamma/K)` pointwise bound, shifts it into an
`IsPredictable` process for the existing filtration, and proves the finite
horizon cumulative bound. Root import and external predictability/cumulative
canaries compile. `Exp3MixedSquarePredictableVariance` now also identifies the
actual generated centered square through the ambient `condExpKernel`: the
generic score pushforward, zero/successor wrappers, and unified shifted-process
conditional-square theorem all compile with an external full theorem canary.
`Exp3MixedSquarePredictableVarianceTail` now completes the next fixed-horizon
step: exact finite-law compensation, generated zero/successor conditional-MGF
transport, and fixed-MGF iteration yield
`P(sum X>=x and sum V<=v)<=exp(-t*x+t^2*v)`. Its optimized delta wrapper uses
`2*sqrt(v*log_+(1/delta))+log_+(1/delta)/(gamma/K)`. The module is root
imported and externally canaried.

`Exp3MixedSquarePredictableVarianceHighProbabilityRegret` now performs the
next consumer step without collapsing `sum V` to the deterministic envelope.
It first transports the centered joint tail to the observed Hedge square sum,
then combines it with the sampled Hedge inequality, exploration bias, and the
pure-cross/comparator Bernstein events. Its primary theorem gives
`P(predictable regret>=budget(v,delta)) <= delta + P(sum V>v)`, and a stronger
joint-event wrapper gives failure at most `delta` on `sum V<=v`. The module is
root imported, externally instantiated in `Tests.Basic`, and consumed by the
realized route below.

`Exp3MixedSquarePredictableVarianceRealizedHighProbabilityRegret` now adds the
compiled realized-minus-predictable deviation without collapsing the random
variance. Its joint theorem bounds realized selected-loss regret together with
`sum V<=v` by `delta`; its primary theorem gives
`P(realized regret>=budget(v,delta)) <= delta + P(sum V>v)`. The budget allocates
`delta/4` across random-square, pure-cross, comparator, and realized-deviation
events. The module is root imported and its residual total-delta theorem is
externally instantiated in `Tests.Basic`; it is consumed by the Markov route
below.

`Exp3MixedSquarePredictableVarianceRealizedMarkovHighProbabilityRegret` now
provides the first closed overflow consumer. Mathlib Markov proves
`P(sum V>v)<=lintegral(ofReal(sum V))/ofReal(v)`. Under the explicit generated
trajectory contract `lintegral(ofReal(sum V))<=ofReal(M)`, the primary theorem
sets `v=M/(delta/5)` and proves a realized selected-loss regret tail at total
failure `delta`, with all five events allocated `delta/5`. The module is root
imported, externally instantiated in `Tests.Basic`, and consumed by the
loss-energy specialization below.

`Exp3MixedSquarePredictableVarianceLossEnergyRealizedMarkovHighProbabilityRegret`
now discharges that abstract lintegral contract under a pathwise predictable
loss-square energy budget. The finite-law bound is
`Var(mixed-square estimator)<=sum_a loss(a)^2/epsilon`; generated summation
gives `sum V<=(1/(gamma/K))*L2`. Integrating this pathwise inequality supplies
`M=(1/(gamma/K))*L2` to the prior Markov theorem and yields the realized
total-delta endpoint. The module is root imported, externally instantiated in
`Tests.Basic`, and consumed by the small-loss theorem below.

`Exp3MixedSquarePredictableVarianceSmallLossRealizedMarkovHighProbabilityRegret`
now derives `L2<=L1` for
`L1=sum_t sum_a predictableLoss_t(a)` and carries `L1` through the entire
regret assembly. In particular, the observed-square/Hedge mean upper bound is
`L1` rather than `K*T`, cumulative variance is at most
`(1/(gamma/K))*L1`, and the
five-event total-delta theorem uses
`v=((1/(gamma/K))*L1)/(delta/5)`. This module is root imported and externally
instantiated in `Tests.Basic`, and consumed by the sparse-loss scenario below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovHighProbabilityRegret`
now constructs that `L1` budget from a concrete scenario contract. It defines
the per-round nonzero predictable-loss support inside `arms`, proves its loss
mass is at most its cardinality, and sums a uniform pathwise support cap `s` to
obtain `L1<=s*T`. The final theorem instantiates the existing realized
small-loss total-delta theorem with `lossMassBudget=s*T`. It is root imported,
focused/root built, externally instantiated in `Tests.Basic`, and consumed by
the eta-tuned route below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovTuning` now defines
the exact sparse Markov scale
`S=s*T+predictableVarianceRadius(((K/gamma)*s*T)/(delta/5),delta/5)` and sets
`eta=sqrt(log K/S)`. With `K>=2` and `0<gamma<=1/2`, the complete
eta-dependent budget is at most `3*sqrt(log K*S)`. Its final generated theorem
uses this internal eta and retains the same total failure `delta`. The module
is root imported, focused/root built, and externally instantiated in
`Tests.Basic`, and is consumed by the explicit-gamma route below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning`
now closes the large-horizon gamma schedule. For `B=log(5/delta)`, it uses the
clipped maximum of `sqrt(s*log K/T)`, the new fifth-root Markov scale
`(5*K*s*(log K)^2*B/(delta*T^3))^(1/5)`, the confidence cube root, and the
realized square root. Four explicit horizon contracts make clipping inactive,
recover the quadratic/fifth-power/cubic/quadratic dominance conditions, and
reduce the tuned threshold to `14*gamma*T`. Both eta and gamma are internal in
the final generated tail. The module is root imported, focused/root built,
externally instantiated in `Tests.Basic`, and consumed by the all-horizon
wrapper below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAllHorizon` now
defines the exact four-contract regime and branches between the explicit
`14*gamma*T` threshold and the strict `T+1` zero-probability fallback. Its
generated theorem covers every positive horizon for `0<delta<=1` without a
caller-supplied regime proof, using the same internal eta and clipped gamma in
both branches. It is root imported, focused/root built, and externally
instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAESparsityAllHorizon`
now removes the universal pathwise support requirement. The exact internally
tuned generated measure may discard a null exceptional set, after which every
time before the horizon has support cardinality at most `s`. The small-loss
lintegral and observed-square bridges were generalized to consume the
resulting a.e. `L1<=s*T` budget, so the final all-horizon theorem keeps total
failure `delta` with no extra sparsity allocation. It is root imported,
focused-built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsity`
now handles positive-probability violations. It defines the exact generated
event where some support cardinality exceeds `S`, proves every sample has
`L1<=S*T` or belongs to that event, and propagates the event through new
observed-square, predictable, and realized residual consumers. Because
exceptional paths need not satisfy the sparse variance bound, Markov overflow
uses the unconditional `L1<=K*T` envelope. The practical endpoint assumes
`mu(sparsityFailure)<=ofReal(epsilon)` and proves the generated realized-regret
tail at `ofReal(delta)+ofReal(epsilon)`. It is root imported, focused/root
built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsity`
now removes the global Markov envelope at the caller-selected eta/gamma
surface. Outside the exact failure event, the existing pointwise loss-mass and
variance inequalities give `sum V <= (1/(gamma/K))*S*T`. New off-bad
observed/predictable/realized small-loss APIs allocate four `delta/4`
confidence events, and the final decomposition charges `sparsityFailure`
exactly once. The practical endpoint proves `delta+epsilon` without event
measurability, restricted measures, global `K*T`, or Markov `1/delta`. It is
root imported, focused/root built, and externally instantiated in
`Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityTuning`
now removes caller eta on the sharper route. It uses
`scale=S*T+predictableVarianceRadius((1/(gamma/K))*S*T,delta/4)` and
`eta=sqrt(log K/scale)`, proves the exact square balance and the three-copy
Hedge bound under `gamma<=1/2`, and exposes residual `delta+mu(failure)` and
practical `delta+epsilon` theorems under the identical internally eta-tuned
measure. It is root imported, focused/root built, and externally instantiated
in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityExplicitTuning`
now removes caller gamma in the large-horizon regime. The clipped maximum
uses the sparse arm square root, the sharper pathwise mixed fifth root
`(K*S*log(K)^2*log(4/delta)/T^3)^(1/5)`, the Bernstein cube root, and the
realized square root. Four horizon contracts yield the generated
`14*gamma*T` residual and `delta+epsilon` endpoints under identical internal
eta/gamma measures. This route has no global `K*T` variance envelope, no
`K^2` mixed numerator, and no polynomial Markov `1/delta`. It is root
imported, focused/root built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityTuning`
now removes caller eta. It uses
`v=((1/(gamma/K))*(K*T))/(delta/5)`,
`scale=S*T+predictableVarianceRadius(v,delta/5)`, and
`eta=sqrt(log K/scale)`. The generated residual theorem keeps
`delta+mu(sparsityFailure)`, while the practical theorem consumes the exact
internally tuned generated-measure epsilon bound and proves `delta+epsilon`.
The module is root imported, focused/root built, and externally instantiated
in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityExplicitTuning`
now removes caller gamma in the large-horizon regime. The global variance
threshold closes to `5*K^2*T/(gamma*delta)`, producing the fifth-root schedule
`(5*K^2*log(K)^2*log(5/delta)/(delta*T^3))^(1/5)`. The clipped maximum with
the sparse arm, Bernstein, and realized-deviation scales supplies all four
dominance contracts; the generated endpoint has threshold `14*gamma*T` and
failure `delta+epsilon` under the exact internally eta/gamma-tuned
sparsity-failure premise. The module is root imported, focused/root built, and
externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityAllHorizon`
now removes the caller regime proof. Its threshold branches between the
explicit `14*gamma*T` probabilistic-sparsity result and strict `T+1`, while
keeping identical internal eta/gamma and generated measures. The residual
endpoint gives `delta+mu(sparsityFailure)` and the practical endpoint gives
`delta+epsilon` for every positive horizon. It is root imported, focused/root
built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityAllHorizon`
now closes that route for every positive horizon. It branches between the
refined pathwise threshold, already bounded by `14*gamma*T`, and strict
`T+1`, while preserving the exact same internal eta, clipped gamma, generated
trajectory measure, and sparsity-failure event. The residual endpoint gives
`delta+mu(sparsityFailure)` and the practical endpoint gives
`delta+epsilon` without caller horizon inequalities or the old global
Markov scale. It is root imported, focused/root and `Tests.Basic` built, and
externally instantiated.

This closes the active-clipping presentation for the pathwise
probabilistic-sparsity branch at the same deliberately coarse fallback used by
the neighboring generated EXP3 routes.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityBestArmAllHorizon`
now closes the finite fixed-comparator gap. It defines hindsight best
supported-arm predictable loss by `Finset.inf'`, rewrites the regret event as
the finite union of comparator events, and applies the preceding all-horizon
off-bad theorem at confidence share `delta/K`. Raw, eta-tuned,
gamma-characterized, explicit, and all-horizon fixed-comparator off-bad
surfaces now compile. Distributing removal of the common failure set through
the finite comparator union gives a best-arm off-bad tail at `delta`; adding
that set once gives residual `delta+mu(sparsityFailure)`. Under the exact
same-measure calibration
`mu(sparsityFailure)<=ofReal(epsilon)`, the practical endpoint is
`delta+epsilon`. It is root imported, focused/root and `Tests.Basic` built,
and externally instantiated at the single-charge theorem. The old
`K*mu(bad)`/`epsilon/K` wrappers remain compatible.

This theorem is a finite hindsight best-supported-arm result, not a
stochastic-mean or first-order best-arm bound. Single charging of the common
sparsity-failure event is closed; the `delta/K` schedule still carries the
expected logarithmic arm-count cost. The next narrow theorem-level gap is
replacement of bounded realized deviation by a genuine
variance-sensitive/Freedman route; sharper clipping, anytime control, and
ideal EXP3.P remain open.

`Exp3MixedSquareBernsteinRealizedExplicitTuning` now consumes the preceding
variance-sensitive eta-tuned theorem. It proves the exact `K^2/gamma`
variance-coefficient identity, controls both the square-root and linear pieces
of the fixed-tilt mixed-square radius under the existing four horizon
contracts, and obtains a generated realized-regret tail at `14*gamma*T`.
The Lean endpoint is
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail`; it is root
imported and has a full external canary in `Tests.Basic`.

The gamma definition deliberately aliases the already compiled conservative
four-scale clipped schedule. This closes the explicit large-horizon consumer
without claiming a sharper fifth-root or jointly optimized schedule. The
all-horizon wrapper below combines this explicit branch with the existing
strict `T+1` zero-probability fallback. The current linear
`log_+/epsilon` correction is compiled into the constant; eliminating or
improving it, Hoeffding/Azuma realized deviation, random
predictable quadratic variation, general Freedman, and ideal EXP3.P remain
separate theorem routes.

`Exp3MixedSquareBernsteinRealizedAllHorizon` now consumes that explicit leaf.
It names the exact four-contract regime and branches between the refined
variance-sensitive threshold, already bounded by `14*gamma*T`, and the strict
`T+1` zero-probability fallback. The generated theorem therefore covers every
positive horizon for `0<delta<=1` without a caller-supplied regime proof. It
is root imported and externally instantiated in `Tests.Basic`.

This closes the active-clipping presentation at the same deliberately coarse
fallback used by the neighboring generated EXP3 routes. The refined branch
still contains the controlled linear `log_+/epsilon` term and bounded-loss
Hoeffding/Azuma realized deviation. Sharper clipping, a better coupled gamma
schedule, random predictable quadratic variation, general Freedman, and
ideal EXP3.P remain separate targets.

`Exp3MixedSquareBernsteinRealizedBestArmAllHorizon` now upgrades that
fixed-comparator endpoint to the finite best supported arm in hindsight. A
shared `Exp3BestArm` module owns the `Finset.inf'` cumulative-loss definition
and event equivalence. The theorem calibrates the common all-horizon schedule
at `delta/K`, unions the comparator events, and proves failure at most
`ofReal(delta)` for every positive horizon. It is root imported, focused/root
and `Tests.Basic` built, and externally instantiated without a caller
comparator or large-horizon contract.

This closes the finite best-arm presentation for the current fixed-tilt
Bernstein-square route. The next concentration-level theorem gap is no longer
a best-arm wrapper: it is a genuine random-quadratic-variation or
variance-sensitive realized-deviation input that can replace the current
deterministic variance/Hoeffding components without overstating a general
Freedman theorem.

`Exp3RealizedPredictableVariance` and
`Exp3RealizedPredictableVarianceTail` now provide that narrow
variance-sensitive realized-deviation input. They identify the exact
finite-action selected-loss centered second moment, transport its compensated
MGF through generated zero/successor conditional action laws, move from
selected to realized deterministic feedback by AE equality, construct the
predictable shifted variance process, and prove the joint tail with radius
`2*sqrt(V*log_+(1/delta))+log_+(1/delta)`.

`Exp3MixedSquarePredictableVarianceRealizedDoublePredictableVarianceHighProbabilityRegret`
joins this tail to the existing mixed-square predictable-regret route.
`Exp3MixedSquarePredictableVarianceSmallLossRealizedDoublePredictableVarianceHighProbabilityRegret`
then preserves an explicit bad set while replacing the generic `K*T`
predictable mean budget by the sparse loss-mass budget.
`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsity`
then closes the caller-parameterized sparse theorem with budgets
`S*T`, `(K/gamma)*S*T`, and `S*T` for loss mass, mixed variance, and
realized variance respectively. It exposes off-bad `delta`, residual
`delta+mu(sparsityFailure)`, and practical `delta+epsilon` surfaces, charging
the common bad event once. Root and `Tests.Basic` builds pass.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityTuning`
now reuses the old sparse pathwise scale and chooses
`eta=sqrt(log K/scale)`. The tuned threshold is
`3*sqrt(log K*scale)+gamma*T` plus the two Bernstein confidence radii and the
exact realized predictable-variance radius at `S*T`. The external practical
endpoint proves `delta+epsilon` under the same generated-measure sparsity
failure premise.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityExplicitTuning`
now closes that explicit gamma leaf. Its clipped schedule is the maximum of
the previous sparse arm/mixed/confidence scales and the new
`sqrt(S*log(4/delta)/T)` selected-loss variance scale, clipped at `1/2`.
Four transparent horizon contracts make clipping inactive and give
quadratic/fifth-power/cubic/quadratic dominance. The exact realized radius is
at most `3*gamma*T`, and the full fixed-comparator threshold is
`16*gamma*T`. Off-bad, residual, and practical `delta+epsilon` endpoints all
compile under the same internal eta/gamma/generated measure, with the common
sparsity-failure event charged once.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityAllHorizon`
now consumes that explicit leaf. It packages the same four-contract regime
and branches between the exact explicit threshold, already bounded by
`16*gamma*T`, and strict `T+1` otherwise. Off-bad, residual, and practical
`delta+epsilon` endpoints use the identical internal eta/gamma/generated
measure and cover every positive horizon without a caller regime proof.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityBestArmAllHorizon`
now upgrades that exact surface to the finite best supported arm in hindsight.
It runs the common eta/gamma/generated measure at `delta/K`, rewrites the
best-arm event through `Finset.inf'` as a finite comparator union, and
normalizes the union bound to `ofReal(delta)`. Removing the common
sparsity-failure event before the union and adding it afterward yields the
single-charge residual `delta+mu(bad)` and practical `delta+epsilon` endpoint
from an unscaled same-measure epsilon premise.

This closes finite hindsight best-arm transport for the exact selected-loss
predictable-variance route. The `delta/K` schedule retains the expected log-K
cost, and active-clipping coverage still uses a deliberately coarse strict
`T+1` fallback. This is not stochastic-mean or first-order best-arm regret;
general Freedman, anytime/self-normalized control, sharp clipping, and ideal
EXP3.P remain separate theorem routes.

### Predictable-compensator fixed-tilt concentration update

`ConcentrationFixedMGF` now exposes
`measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt`. For a
strongly adapted compensated process `tilt*Y_i-varianceCoeff*V_i`, unit-tilt
zero-budget initial and successor conditional-MGF witnesses imply
`P(sum Y>=threshold, sum V<=varianceBudget) <=
exp(-tilt*threshold+varianceCoeff*varianceBudget)` in ENNReal form.

The proof reuses the compiled fixed-tilt finite-sum MGF theorem, performs the
`Measure.real` to ENNReal conversion once, and handles the random compensator
through event inclusion. The realized selected-loss predictable-variance EXP3
tail now calls this theorem with `varianceCoeff=tilt^2`, so the leaf is tested
on an existing theorem route rather than remaining an unused abstraction.

Contracts remain explicit: Standard Borel ambient space, finite
zero-or-probability measure, strong adaptedness, source-record exponential
integrability, initial/successor MGF bounds, and nonnegative coefficients. This
is fixed-horizon and fixed-tilt; it is not maximal/anytime, self-normalized,
tilt-optimized, or a general Freedman theorem.

### Quadratic fixed-MGF delta route update

`ConcentrationQuadraticFixedMGF` now compiles the complete optimization route
from a family of quadratic fixed-tilt tails to a delta-shaped joint
deviation/variance tail. Its radius is
`2*sqrt(c*V*log_+(1/delta))+log_+(1/delta)/cap`, and the theorem handles every
positive delta, including the trivial `delta>1` branch.

The algebraic tilt optimizer was moved out of the EXP3-specific Bernstein
module into this concentration layer. Both
`sampledPredictableRealizedDeviation_sum_tail_predictableVariance_delta` and
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta`
now consume the generic theorem, using caps `1` and `gamma/|arms|`. Their
public statements and downstream regret routes are unchanged.

Contracts are positive variance scale, variance budget, tilt cap, and delta,
plus the fixed-tail family on one unchanged joint event. Model probability,
adaptedness, conditional-MGF, and law-transport requirements remain with the
fixed-tail producer. This closes quadratic fixed-horizon tilt optimization,
not one-step MGF construction, maximal/anytime mixtures, optional stopping,
self-normalization, or a general Freedman theorem.

### Finite-prefix quadratic maximal update

`ConcentrationQuadraticMaximal` now lifts the quadratic delta theorem over a
nonempty finite index set. It uses confidence `delta/|times|` for every event,
applies the existing optimizer, and normalizes the finite outer-measure union
back to `ofReal(delta)`. No event-measurability premise is introduced.

`Exp3RealizedPredictableVarianceMaximal` consumes this theorem on
`times=range horizon`: index `t` denotes the positive prefix of length `t+1`,
so the covered lengths are `1` through `horizon` inclusive. All prefixes
share one selected-loss predictable-variance budget, and the
result controls their union under the generated EXP3 trajectory measure.

The generic layer requires a measurable ambient space, a decidable nonempty
finite index set, positive scale/budget/cap/delta, and one fixed-tail family
per index. The EXP3 specialization supplies its probability, Standard Borel,
loss regularity, and fixed-tilt law contracts. This is a finite union bound
with the explicit log-horizon cost; it is not a Ville/Doob inequality,
horizon-free anytime theorem, mixture boundary, optional-stopping result,
self-normalized theorem, or general Freedman theorem.

## Practical selected-policy centered-sum tail leaf

`ConditionalExpectationReward.centeredRewardSuccProcess_sum_tail_ennreal_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
now compiles in `BanditRLProof.ConditionalRewardLawSource`. On an ambient
probability space it turns the per-time policy-selected reward-coordinate
`condExpKernel.map` law, raw reward and selected-mean ranges, measurable
context/state/mean surfaces, `CenteredRewardKernelLaw`, and selected-history
variance ceilings into an ENNReal Azuma-Hoeffding bound for the zero-initialized
`Finset.range n` centered-reward sum. The random sum contains rewards `1`
through `n-1`.

The route reuses generated-history `StronglyAdapted`, the practical
selected-policy one-step conditional-MGF producer, and
`Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`. It is a
fixed-horizon aggregate tail, not an arm-wise empirical mean, confidence
inversion, anytime bound, or regret theorem. If a concrete model lacks the
selected reward law or variance transport, keep that obligation explicit
rather than assuming independence or an abstract conditional-MGF witness.

## Practical selected-policy two-sided delta confidence

The next theorem-facing layer now compiles. Generic declarations in
`BanditRLProof.ConcentrationSubGaussian` turn strongly adapted conditional
sub-Gaussian increments into a two-sided ENNReal finite-sum tail and calibrate
the radius
`Concentration.subGaussianSumConfidenceRadius V delta = sqrt (2*V*log(2/delta))`.
The practical endpoint
`ConditionalExpectationReward.centeredRewardSuccProcess_sum_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
instantiates this route from the selected reward-coordinate law and the same
raw/mean/history-variance contracts as the one-sided theorem.

The result controls the absolute aggregate centered-reward sum for rewards
`1..n-1` by `ENNReal.ofReal delta` under positive total proxy variance and
`0 < delta <= 1`. It is fixed-horizon aggregate confidence, not an arm-wise
empirical mean, random pull-count confidence sequence, anytime theorem, or
regret theorem. The next concrete route should supply an arm/sample-count
process or a model-specific selected-law transport; missing law, variance, or
positive-total-variance evidence must remain explicit.

## Practical selected-policy fixed-sample average confidence

The fixed-sample average leaf now compiles at both generic and practical
surfaces. `Concentration.measure_average_abs_tail_le_of_measure_sum_abs_tail`
transports any two-sided sum-confidence event through a positive deterministic
sample count, while
`Concentration.condSubGaussian_average_abs_tail_ennreal_delta_of_stronglyAdapted`
packages that transport with the compiled conditional sub-Gaussian sum route.
The practical endpoint is
`ConditionalExpectationReward.centeredRewardSuccProcess_average_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

Its prefix is exactly `Finset.range (m+1)`: slot zero is zero and slots
`1..m` are the `m` centered successor rewards, so the sum and radius are both
divided by `m`. Contracts are the existing selected-law/raw-range/mean-range/
history-variance surface plus `0<m`, positive total proxy variance, and
`0<delta<=1`. The next theorem route must introduce a genuine arm/sample-count
process before claiming arm-wise or random-count confidence; this result is
not anytime, self-normalized, Freedman, or regret concentration.

## UCB arm-stream fixed-prefix empirical-mean theorem

The arm/sample process requested by the preceding route is now instantiated
for the canonical stationary product arm-stream model. The generic independent
layer compiles two-sided finite-sum, delta-calibrated sum, and exact
`Finset.range k` average theorems using Mathlib
`HasSubgaussianMGF.sum_of_iIndepFun`. The concrete endpoint
`UCB.measure_armPrefixAverageConfidenceRadius_le_abs_empiricalMean_sub`
controls one arm's first `k>0` latent rewards around its supplied mean by
`ENNReal.ofReal delta`.

`UCB.armPrefixEmpiricalMean` averages coordinates `0..k-1`, and its radius is
`sqrt(2*(k*sigma2)*log(2/delta))/k`. Product-law coordinate independence and
the centered one-coordinate MGF law discharge the generic assumptions; total
variance positivity is derived internally from `k>0` and `sigma2!=0`.
Adaptive realized pull-count confidence remains on the already compiled
fixed-count peeling/index-tail route. This theorem adds no anytime,
self-normalized, Freedman, or new non-product selected-law transport claim.

## Selected-policy fixed-arm masked sum theorem

The non-product selected-policy route now has a real arm-wise aggregate step.
`ProbabilityTheory.HasCondSubgaussianMGF.indicator` uses conditional-kernel
support on a conditioning-measurable event to retain the same proxy after
masking. `generatedActionFromRewardHistory_succ_measurable_historyFiltrationSucc`
derives action predictability from the reward-prefix comap identity, and the
practical endpoint controls the absolute fixed-arm masked centered sum over
`Finset.range n` by `ENNReal.ofReal delta`.

The deterministic proxy sum in this older theorem still includes every
`varianceCeiling i`, including times when the arm is not selected. The newer
predictable-variance route below supplies the stronger masked proxy as a
separate compiled theorem.

## Selected-policy successor-arm empirical-mean theorem

The practical selected-policy route now reaches a genuine fixed-arm empirical
mean on the event that its realized successor pull count is positive.
`successorArmPullCount` and `successorArmRewardSum` cover exactly coordinates
`1..n-1`; `armMaskedCenteredRewardSuccProcess_sum_eq_successorArmRewardSum_sub_pullCount_mul`
uses a stationary arm mean to identify the masked centered sum; and the generic
`measure_randomCount_average_abs_tail_le_of_measure_sum_abs_tail` divides the
sum confidence event by the realized count. The final theorem is
`successorArmEmpiricalMean_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

This older endpoint closes random positive-denominator transport with radius
`sqrt(2*V_horizon*log(2/delta))/N_arm`, where `V_horizon` is the full
deterministic horizon proxy.

The next count-adaptive layer now compiles. At one step,
`HasCondSubgaussianMGF.indicator_compensated_hasCondMGFUpperBoundAt` pays the
quadratic MGF budget only on the predictable arm-selection event. The generic
fixed-horizon theorem retains the cumulative masked proxy in a joint event and
optimizes the fixed tilt. In the practical selected-policy specialization,
`armMaskedVarianceSuccProcess_sum_eq_mul_successorArmPullCount` identifies a
constant ceiling's proxy sum with `sigma2 * successorArmPullCount`. Consequently
`successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
charges exactly `k*sigma2` on every fixed positive fiber `pullCount=k`.

Finite count peeling now closes the single random-count confidence event.
`measure_positive_randomCount_event_le_sum_exactCount` covers any positive
Nat-valued count event by its exact fibers under a deterministic ceiling, and
`measure_positive_randomCount_event_le_of_exactCount_uniform` assigns equal
`delta/maxCount` shares without count or event measurability. For the practical
route, `successorArmPullCount_le_horizon` supplies `maxCount=n`, and
`successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
uses the realized count in `successorArmEmpiricalMeanPeelingRadius` and has total
failure `ENNReal.ofReal delta`.

The simultaneous finite arm/time confidence event now compiles.
`successorArmEmpiricalMeanFiniteArmTimeBadEvent` unions over the explicit
nonempty family `arms.product (Finset.range T)`, using horizon `i+1` for every
`i<T`. `successorArmEmpiricalMeanFiniteArmTimeConfidenceShare` gives every
arm/time member an equal outer share, and its member theorem performs the prior
realized-count peeling internally. The final endpoint is
`successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`,
with total failure `ENNReal.ofReal delta`.

The random-width UCB score adapter now compiles in
`BanditRLProof.Algorithms.UCBConditionalRewardLaw`. It keeps the realized-count
radius instead of forcing the theorem through `UCB.finiteHorizonConfidenceBadEvent`,
whose radius is sample-independent. `SelectedPolicySuccessorInitializedScoreMaxSource`
packages an explicit post-initialization time set, candidate membership,
positive best/chosen counts, and score maximality. The pointwise consumer gives
`gap <= 2 * chosenRadius` outside the practical simultaneous event, and
`measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
therefore gives total large-gap failure `ENNReal.ofReal delta`.

The concrete producer and expected-count transport described by this earlier
checkpoint are now closed in the following leaf. The route remains fixed
finite horizon and still does not provide regret, maximal/anytime,
self-normalized, or general Freedman concentration.

## Generated selected-policy UCB pull-count route

The concrete producer and pull-count consumer now compile in
`BanditRLProof.Algorithms.UCBConditionalRewardLawPolicy`. A measurable
finite-history policy reconstructs the actual pair prefix from generated
rewards, initializes all `Fin K` arms once on successor coordinates `1..K`,
and then chooses `UCB.scoreArgmax` for the same realized-count index used by
the random-width large-gap theorem. The reconstruction invariant proves that
the policy-side counts, sums, and indices are the generated trace quantities,
so `selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource` is a concrete
producer rather than an assumed algorithm contract.

For a chosen arm with positive gap, the full-horizon inequalities
`32*sigma2*L_T < gap^2*B` and `4*L_T < gap*B` uniformly imply
`2*radius(k,n) < gap` for `B<=k` and `n<=T`. The compiled consumers therefore
give both `P(N_chosen(T+1)>B) <= ENNReal.ofReal delta` and
`lintegral N_chosen(T+1) <= B + T*ENNReal.ofReal delta`. The practical tail
endpoint consumes the existing selected reward law, raw/mean range,
measurability, stationary arm mean, centered kernel, and uniform variance
contracts. The module is root-imported and externally canaried in
`Tests.Basic`.

The closed-form threshold and finite-arm gap-weighted pseudo-regret assembly
described by this checkpoint now compile in the following leaves. Model-side
production of the selected reward law and any anytime/self-normalized/general
Freedman or final broad UCB claim remain separate.

## Explicit-threshold practical UCB expected count

`selectedPolicySuccessorRealPullThreshold` is now the maximum of
`32*sigma2*L_T/gap^2` and `4*L_T/gap`, and
`selectedPolicySuccessorPullThreshold` is its `Nat.ceil` plus one.
`selectedPolicySuccessorPullThreshold_contracts` proves positivity and both
strict full-budget inequalities from only `gap>0`; the explicit radius, tail,
and ENNReal expectation consumers therefore expose no caller-supplied `B`,
`hradius`, or numeric inequalities.

The end-to-end theorem is
`lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_reward_map_eq_selected_policy`.
It first builds the concrete source large-gap bound from the trim-a.e. selected
reward law, then concludes `lintegral N_chosen(T+1) <= threshold + T*ofReal
delta`. Its regularity surface is exactly the practical selected-law,
measurability, raw/mean range, centered-kernel, stationary-mean, positive
uniform-variance, `K,T>0`, `delta>0`, and positive chosen-gap contracts.

This leaf is Mathlib-backed through `Nat.le_ceil`, max/order and positive
division algebra, plus the already compiled measure and `lintegral` route. It
is consumed by the finite-arm practical pseudo-regret leaf below.

## Explicit-threshold practical UCB pseudo-regret

`BanditRLProof.Algorithms.UCBConditionalRewardLawRegret` now defines
`selectedPolicySuccessorGeneratedUCBRegretAction`, shifting generated successor
actions `1..T` to the standard pseudo-regret coordinates `0..T-1`, and proves
that its arm pull counts equal the existing successor counts at `T+1`.
`modelMeanGap_bestArm_eq_realGap` aligns the Real UCB mean gap with
`FiniteBanditModel.gap`.

The reusable theorem
`lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount`
expands scalar pseudo-regret into the finite arm sum, exchanges `lintegral`
with that sum, and asks for a count bound only when an arm gap is positive.
Model gap nonnegativity makes every zero-gap term vanish. The end-to-end
selected-law theorem then applies the explicit expected-count leaf armwise and
bounds practical ENNReal pseudo-regret by the `Finset.univ` sum of
`ofReal(gap) * explicitThreshold(gap)` and
`ofReal(gap) * (T * ofReal(delta))`.

Imports/APIs are `UCBConditionalRewardLawPolicy`,
`FiniteBanditModelInvariants`, `ScalarPseudoRegret`, the scalar
`ofReal_pseudoRegret` pull-count identity, `FiniteBanditModel.gap_nonneg`,
`MeasureTheory.lintegral_finset_sum`, and
`MeasureTheory.lintegral_const_mul`. The practical regularity surface retains
the probability/Standard-Borel, selected reward law, measurability, raw/mean
range, centered-kernel, stationary-model-mean, positive uniform variance,
`K,T>0`, and `delta>0` contracts; it exposes no per-arm positive-gap premise.

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET`
is `leanCompiled`, root imported, focused-built, and externally canaried in
`Tests.Basic`. Retrieval evidence is compiled local/Mathlib code; theorem-card
and weapon-only text is not proof evidence. Its ceiling/max finite sum is now
simplified by the following leaf.

## Textbook positive-gap practical UCB pseudo-regret

`selectedPolicySuccessorTextbookGapBudget K sigma2 T delta gap` is
`32*sigma2*L_T/gap + 4*L_T + 2*gap`. The ceiling lemma bounds the integer
threshold by its real maximum plus two; the two nonnegative maximum branches
are bounded by their sum, and multiplication by a positive gap removes one
gap power. The ENNReal transport uses `ENNReal.ofReal_natCast`,
`ENNReal.ofReal_mul`, and `ENNReal.ofReal_le_ofReal`.

`sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum` filters the arm
sum to strictly positive model gaps, preserves the
`ofReal(gap)*(T*ofReal(delta))` term exactly, and removes zero-gap arms using
`FiniteBanditModel.gap_nonneg`. The full practical endpoint is
`lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_of_reward_map_eq_selected_policy`.
It directly exposes the positive-gap sum of the textbook arm budget plus the
confidence-failure contribution.

The imports and regularity contracts are unchanged from the explicit-threshold
practical theorem: probability/Standard Borel, selected reward
`condExpKernel.map` law, measurable context/reward/state/mean, raw/mean ranges,
centered kernel, stationary model means, positive uniform variance, `K,T>0`,
and `delta>0`. No per-arm positivity, threshold, radius, or numeric inversion
premise is caller-visible.

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET` is
`leanCompiled`, root imported through the existing module, focused-built, and
externally canaried in `Tests.Basic`. Compiled local/Mathlib declarations are
the retrieval evidence; theorem-card and weapon-only text is not proof. This
leaf is consumed by the canonical reward-only `trajMeasure` endpoint below.

## Canonical reward-only trajMeasure UCB pseudo-regret

`selectedPolicySuccessorRewardStepKernelFamily` specializes
`RewardKernel.historyStepKernelFamily` to the generated UCB policy/state.
`isMarkovKernel_selectedPolicySuccessorRewardStepKernelFamily` supplies the
family instances, and `selectedPolicySuccessorRewardTrajMeasure` plus its
probability instance expose the canonical Ionescu-Tulcea trajectory law.

`selectedPolicySuccessorGeneratedUCBSelectedRewardLawSource_trajMeasure`
specializes the canonical comap-trim selected-reward theorem and transports it
through
`generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy`.
Its public projection
`selectedPolicySuccessorGeneratedUCB_reward_map_eq_selected_policy_trajMeasure`
has the exact trim-a.e. `historyFiltrationSucc` `condExpKernel.map` surface used
by the practical theorem. The final
`lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure`
therefore supplies that law internally and returns the positive-gap textbook
ENNReal finite sum under the canonical reward-only trajectory measure.

The route imports `UCBConditionalRewardLawRegret` and uses
`Kernel.trajMeasure`, `ProbabilityTheory.IsMarkovKernel`, the canonical
trim-aware law, the finite-pair comap adapter,
`historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`, and
`measurable_pi_apply`. Contracts remain explicit: probability initial law,
measurable context/state extraction, Markov reward kernel, measurable mean,
centered kernel law, stationary model means, positive selected-history
variance ceiling, `K,T>0`, `delta>0`, mean range, and pointwise raw range.

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-CANONICAL-REWARD-TRAJMEASURE-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`, root imported, focused-built, and canaried in `Tests.Basic`.
Evidence is the compiled declarations and Mathlib kernel/measure APIs; theorem
cards and weapon-only text are not proofs. The canonical selected-law premise
is closed. This compatibility endpoint is now consumed by the stronger
centered-kernel route below; its pointwise `hraw` and mean-range fields are no
longer blockers for the canonical theorem.

## Centered-kernel canonical UCB pseudo-regret

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The final statement
`lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel`
uses the same canonical reward-only trajectory measure and textbook
positive-gap finite sum, but removes `hraw`, mean-range bounds, and the caller
selected-law premise completely.

The random variable at successor time `i+1` is reward minus the
history-selected kernel mean; the filtration is `historyFiltrationSucc`.
`CenteredRewardKernelLaw` already supplies selected-law integrability, zero
mean, and `HasSubgaussianMGF`. The canonical trim-a.e.
`condExpKernel.map` identity transfers this directly to
`HasCondSubgaussianMGF`. A predictable arm-selection indicator charges
`sigma2` exactly on pulls, exact-count fibers give two-sided confidence,
finite peeling handles the random count, and a finite arms-times union supplies
the generated-UCB large-gap event. Existing deterministic UCB algebra then
produces expected pull counts, finite-arm pseudo-regret, and the textbook
`32*sigma2*L/gap + 4*L + 2*gap` budget.

The module imports `UCBConditionalRewardLawTrajMeasure` and reuses the
integrated conditional-MGF transfer, generated-history `StronglyAdapted`
helpers, predictable-variance tail, exact-count peeling, finite union bounds,
score-max source, pull-count integration, and textbook sum algebra. Contracts
are now only probability `mu0`, measurable context and mean, a Markov reward
kernel with `CenteredRewardKernelLaw`, stationary means equal to `model.mean`,
positive selected-history variance ceiling, `K,T>0`, and `delta>0`.

Focused/root/`Tests.Basic` builds and twelve external canaries pass. Compiled
local declarations and Mathlib probability/kernel/integration APIs are the
evidence; theorem-card and weapon-only material is not proof. The complete
canonical ENNReal textbook pseudo-regret route is closed. Optional Real/
Bochner presentation and context-independent direct-subGaussian/bounded
constructors are closed by the downstream routes below. Context-dependent
constructors, anytime/self-normalized/general Freedman, cross-LML, and other
bandit/RL algorithms remain outside this route.

## Real/Bochner canonical UCB pseudo-regret

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The final theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel`
integrates the Real cast of canonical generated-UCB pseudo-regret with
`MeasureTheory.integral` and exposes the explicit positive-gap Real sum
`textbookGapBudget + gap * (T * delta)`. The public RHS contains no
`ENNReal.toReal`.

The supporting leaf `integrable_real_pullCount_of_measurable_action` derives
finite-horizon pull-count integrability from timewise action measurability,
`measurable_natCast_pullCount`, `pullCount_le_time`, and
`Integrable.of_bound` under a finite measure. The generated-UCB wrapper feeds
these witnesses to `integrable_real_pseudoRegret_of_integrable_pullCount`.
The final proof establishes pseudo-regret nonnegativity from the finite-arm
pull-count decomposition, rewrites `ofReal (integral ...)` as the compiled
lintegral, consumes the centered-kernel ENNReal theorem, proves the finite RHS
is not infinity, and normalizes it with `ENNReal.toReal_sum/add/mul/ofReal`.

Imports are `UCBConditionalRewardLawCenteredKernel` and
`ExpectationRegretPullCount`. The final regularity contracts remain exactly
the centered-kernel canonical contracts: probability initial law, measurable
context/mean, `CenteredRewardKernelLaw`, stationary model means, selected-
history variance bounded by positive `sigma2`, `K,T>0`, and `delta>0`.
Finite-horizon integrability is internal; no caller integrability, raw/mean
range, support restriction, or selected-law premise is added. Focused/root/
`Tests.Basic` builds and four new canaries pass. Compiled local declarations,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, and the pinned Mathlib Bochner/
ENNReal APIs are the retrieval evidence. Context-independent direct-subGaussian
and bounded centered-kernel constructors, plus a bounded finite-arm theorem,
now compile downstream. Do not reopen the completed ENNReal-to-Real conversion
or weaken the theorem to a `.toReal` RHS.

## Bounded finite-arm canonical UCB theorem

Card
`LOCAL-LEAF-UCB-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The final theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_boundedFiniteArmLaws`
instantiates the canonical Real route from stationary per-arm probability laws
sharing one nondegenerate interval `[lo,hi]`.

`FiniteArmRewardKernelLaw` is algorithm independent. It exposes
`contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF` from exact
means and direct per-arm MGF witnesses, and
`contextIndependentBoundedCenteredRewardKernelLaw` from a.e. measurable reward
casts, common a.s. interval bounds, and exact means. The latter reuses the
Mathlib-backed bounded centered-MGF wrapper. The supporting theorem
`intervalVarianceProxy_pos_of_lt` proves strict positivity of the Hoeffding
proxy from `lo < hi`.

The UCB theorem takes `Context := Unit`, uses `armLaw defaultAction` for the
initial reward and `contextIndependentOfActionLaws` for successors, sets the
kernel mean to `model.mean`, and discharges the constant variance ceiling and
all canonical trajectory contracts internally. Callers provide only per-arm
probability laws, `lo < hi`, a.e. measurability and a.s. interval membership,
exact model means, a default arm, `T>0`, and `delta>0`. The result is the same
explicit positive-gap Real textbook sum; no centered law, selected law,
trajectory law, variance premise, or integrability premise remains.

Focused/root/`Tests.Basic` builds and four external canaries pass. Retrieval
found the older ETC-specific bounded constructor first; the new generic module
avoids importing the large ETC theorem route into UCB. Exact local declarations,
`MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MEASURE-INTEGRAL`, and the prior canonical
Real card are proof evidence. Unequal-range finite-arm laws compile in the
armwise route below; context-dependent, anytime/Freedman, and other algorithm
routes remain separate.

## Armwise bounded finite-arm canonical UCB theorem

Card
`LOCAL-LEAF-UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_armwiseBoundedFiniteArmLaws`
accepts separate support endpoints `lo arm` and `hi arm` for every finite arm.

`finiteArmIntervalVarianceProxy` computes the `Finset.univ.sup` of all armwise
Hoeffding proxies. `intervalVarianceProxy_le_finiteArmIntervalVarianceProxy`
discharges the selected-history variance ceiling, and
`finiteArmIntervalVarianceProxy_pos` uses `model.hK` plus pointwise
nondegeneracy to prove the UCB proxy is positive. The armwise reward-kernel
constructor applies the bounded centered MGF theorem independently to every
arm before the canonical Real endpoint is invoked.

The public contracts are per-arm probability laws, pointwise `lo arm < hi arm`,
a.e. measurable reward casts, per-arm a.s. interval support, exact model means,
a default arm, `T>0`, and `delta>0`. No common interval, caller variance
ceiling, centered law, selected law, trajectory law, or integrability witness
is required. Context-dependent/nonstationary laws and anytime/Freedman routes
remain separate.

## Direct sub-Gaussian finite-arm canonical UCB theorem

Card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_finiteArmSubgaussianLaws`
removes bounded-support assumptions entirely. Callers supply exact arm means
and a centered `HasSubgaussianMGF` witness with an `NNReal` proxy for each arm.

`finiteArmVarianceProxy` computes the finite maximum proxy;
`varianceProxy_le_finiteArmVarianceProxy` provides every selected-arm ceiling;
and `finiteArmVarianceProxy_pos_of_exists` needs only one positive member.
Zero-proxy deterministic arms are therefore allowed. The direct centered-law
constructor supplies integrability and zero mean, while the theorem constructs
the Unit-context stationary kernel and canonical trajectory internally.

The final result is the explicit Real positive-gap textbook sum at the maximum
proxy. There is no bounded support, common interval, caller variance ceiling,
abstract centered law, selected law, trajectory law, or integrability premise.
The all-zero-proxy degenerate model remains a separate route because the current
canonical UCB theorem assumes a strictly positive common proxy.

## Context-dependent bounded reward-kernel canonical UCB theorem

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-BOUNDED-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The generic `BoundedRewardKernelLaw` layer now constructs a
`CenteredRewardKernelLaw` for an arbitrary `MarkovRewardKernel`: either directly
from pointwise centered `HasSubgaussianMGF` witnesses and exact means, or from a
common nondegenerate a.s. interval by the Mathlib-backed bounded MGF theorem.

The final theorem accepts a measurable history-dependent context extractor and
allows the selected reward distribution to vary with context and action. It
requires the arm mean to remain `model.mean arm`, matching the stationary
`pseudoRegret` definition, and uses one common `lo < hi` support interval. The
interval proxy, centered law, selected-law probability instances, trajectory
law, variance ceiling, centered/raw integrability, and zero-centered-mean facts
are constructed internally.

The conclusion is the explicit positive-gap Real textbook sum. Focused and
external canary builds pass. Context/action-dependent intervals, direct
context-dependent sub-Gaussian laws with an automatically constructed positive
common ceiling, nonstationary regret, and anytime/Freedman routes remain
separate leaves. The direct sub-Gaussian route with an explicit global ceiling
is closed below.

## Context-dependent direct sub-Gaussian canonical UCB theorem

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The theorem accepts an arbitrary context-dependent Markov
reward kernel, a pointwise `NNReal` proxy, and direct centered
`HasSubgaussianMGF` evidence for every context/action selected law. Rewards and
proxies may vary with context/action, while exact means remain
`model.mean arm` to match stationary pseudo-regret.

Callers supply one strictly positive `sigma2` and prove every pointwise proxy
is at most it. This is the necessary general contract for an arbitrary
measurable context space: unlike `Fin K`, it has no finite `Finset.sup` from
which Lean can compute a maximum. The centered kernel law, selected-law and
trajectory transports, centering, and all integrability obligations are
constructed internally, with no bounded-support assumption.

The result is the explicit positive-gap Real textbook sum at `sigma2`.
Automatic ceilings for finite/compact context families, all-zero/noiseless
models, context-dependent means/nonstationary regret, and anytime/Freedman
routes remain separate.
