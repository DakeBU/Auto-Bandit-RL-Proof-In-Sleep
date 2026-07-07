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
- measure, finite-history, history-filtration, policy-measurability,
  reward-kernel, finite-prefix `partialTraj`, and conditional-expectation
  bridge surfaces;
- independent and strongly adapted conditional sub-Gaussian tail wrappers;
- a deterministic finite-action EXP3 potential surface with exponential-weight
  updates, nonnegativity, one-step increment algebra, and finite-horizon
  telescoping;
- a generic finite-action FTRL one-step minimizer wrapper over an explicit
  feasible predicate or finite-simplex predicate;
- a finite-simplex Tsallis power-sum/entropy/negative-entropy regularizer
  surface with `Real.rpow` and denominator well-definedness facts;
- thin algorithm surfaces for Explore-Then-Commit, UCB, and Thompson sampling;
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
- local imports or ports of LML UCB/ETC/Thompson theorem routes;
- complete UCB, ETC, Thompson sampling, EXP3 regret, Tsallis-INF/FTRL,
  OFUL/LinUCB, BwK, or finite-horizon RL theorem proofs;
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
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the definitional
  centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`,
  a source-projection wrapper exposing the packaged practical base
  raw-range/measurable-mean-range bounded source from a selected-history
  variance source.
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
  regret obligation names.

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
ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE compiled-local
ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY compiled-local
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
  pair/reward law source and ambient trajectory-to-`condExpKernel`
  identification remain open.
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
  under integrability.  The pair/reward-law source and ambient
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
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the uniform variance-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the same definitional
  centered-source projection.  This gives downstream centered-source consumers
  a direct interface from the uniform variance source while keeping the random
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
    The pointwise wrong-commit regret assembly bridge is now compiled as
    `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE`.
    The abstract lower-integral wrong-commit regret assembly is now compiled
    as `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY`.
    The concrete finite-argmax/infinitePi lower-integral regret assembly is now
    compiled as `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY`.
    The conservative sum-gap suffix adapter for that assembly is now compiled
    as `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY`.
    The sharper max-gap suffix adapter is now compiled as
    `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY`.
    The polished fixed product-coordinate max-gap wrapper is now compiled as
    `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER`.
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
  `[Fintype]` finite-union outer-measure wrappers; this is a probability
  assembly leaf, not a concentration theorem.
- `TAIL-SUMMABILITY-UCB` now compiles locally in
  `BanditRLProof.UCBSummability` as an abstract finite-arm finite-horizon
  bad-event summability wrapper consuming per-arm/per-time ENNReal tail bounds;
  UCB log/sqrt side conditions and the final regret theorem remain separate.
- `EXP3-POTENTIAL` now compiles locally in `BanditRLProof.Exp3Potential` as
  a deterministic finite-action exponential-weights potential surface with
  update unfolding, nonnegativity, one-step increment algebra, and
  finite-horizon telescoping; estimator, exp/log, learning-rate, and regret
  leaves remain separate.
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
- `ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE` now compiles
  locally in `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` now compiles locally in
  `BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`.
- `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` now compiles locally in
  `BanditRLProof.Algorithms.ETCExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` now compiles locally
  in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` now compiles
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
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
  prior/likelihood/posterior surface is named.  Bayes-rule identification,
  regular conditional distribution existence, Thompson probability matching,
  and Bayesian regret remain separate.
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
