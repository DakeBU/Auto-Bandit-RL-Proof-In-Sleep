# ETC Wrong-Commit Probability Design

Status: theorem-card-only / missing-leaf design, with the concrete
lower-integral support chain now compiled locally.

Source gate:

- Prompt: `reports/extended_pro_after_bestarm_commit_phase_candidate_prompt_2026-06-30.md`
- Response: `reports/extended_pro_after_bestarm_commit_phase_response_2026-06-30.md`
- Boundary before review: `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE`
- Follow-up prompt: `reports/extended_pro_after_commitarm_ne_bestarm_meas_candidate_prompt_2026-06-30.md`
- Follow-up response: `reports/extended_pro_after_commitarm_ne_bestarm_meas_response_2026-06-30.md`
- Boundary before follow-up: `ETC-MEAS-COMMITARM-NE-BESTARM`
- Chosen follow-up leaf: `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT`
- Second follow-up prompt: `reports/extended_pro_after_wrong_commit_subset_candidate_prompt_2026-06-30.md`
- Second follow-up browser prompt: `reports/extended_pro_after_wrong_commit_subset_browser_prompt_2026-06-30.md`
- Second follow-up response: `reports/extended_pro_after_wrong_commit_subset_response_2026-06-30.md`
- Boundary before second follow-up: `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT`
- Chosen second follow-up leaf: `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET`
- Third follow-up prompt: `reports/extended_pro_after_wrong_commit_measure_wrapper_candidate_prompt_2026-06-30.md`
- Third follow-up response: `reports/extended_pro_after_wrong_commit_measure_wrapper_response_2026-06-30.md`
- Boundary before third follow-up: `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET`
- Chosen third follow-up leaf: `ETC-MEAS-EMPMEAN-GE-EMPMEAN`
- Fourth follow-up prompt: `reports/extended_pro_after_empmean_pairwise_meas_candidate_prompt_2026-06-30.md`
- Fourth follow-up response: `reports/extended_pro_after_empmean_pairwise_meas_response_2026-06-30.md`
- Boundary before fourth follow-up: `ETC-MEAS-EMPMEAN-GE-EMPMEAN`
- Chosen fourth follow-up leaf: `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM`
- Fifth follow-up prompt: `reports/extended_pro_after_finite_wrong_mean_event_meas_candidate_prompt_2026-06-30.md`
- Fifth follow-up response: `reports/extended_pro_after_finite_wrong_mean_event_meas_response_2026-06-30.md`
- Boundary before fifth follow-up: `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM`
- Chosen fifth follow-up leaf: `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM`
- Sixth follow-up prompt: `reports/extended_pro_after_finite_union_wrong_mean_prob_candidate_prompt_2026-06-30.md`
- Sixth follow-up response: `reports/extended_pro_after_finite_union_wrong_mean_prob_response_2026-06-30.md`
- Boundary before sixth follow-up: `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM`
- Chosen sixth follow-up leaf: `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS`
- Seventh follow-up prompt: `reports/extended_pro_after_wrong_commit_sum_assembly_candidate_prompt_2026-06-30.md`
- Seventh follow-up response: `reports/extended_pro_after_wrong_commit_sum_assembly_response_2026-06-30.md`
- Boundary before seventh follow-up: `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS`
- Chosen seventh follow-up leaf: `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL`
- Eighth follow-up prompt: `reports/extended_pro_after_pairwise_tail_candidate_prompt_2026-06-30.md`
- Eighth follow-up response: `reports/extended_pro_after_pairwise_tail_response_2026-06-30.md`
- Boundary before eighth follow-up: `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL`
- Chosen eighth follow-up leaf: `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL`
- Ninth follow-up prompt: `reports/extended_pro_after_nonbest_pairwise_tail_candidate_prompt_2026-06-30.md`
- Ninth follow-up response: `reports/extended_pro_after_nonbest_pairwise_tail_response_2026-06-30.md`
- Boundary before ninth follow-up: `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL`
- Chosen ninth follow-up leaf: `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL`
- Tenth follow-up prompt: `reports/extended_pro_after_filtered_sum_pairwise_tail_candidate_prompt_2026-06-30.md`
- Tenth follow-up response: `reports/extended_pro_after_filtered_sum_pairwise_tail_response_2026-06-30.md`
- Boundary before tenth follow-up: `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL`
- Chosen tenth follow-up leaf: `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`
- Eleventh follow-up prompt: `reports/extended_pro_after_exploration_pulls_pos_candidate_prompt_2026-06-30.md`
- Eleventh follow-up response: `reports/extended_pro_after_exploration_pulls_pos_response_2026-06-30.md`
- Boundary before eleventh follow-up: `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`
- Chosen eleventh follow-up leaf: `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`
- Twelfth follow-up prompt: `reports/extended_pro_after_ratcast_exploration_pulls_pos_candidate_prompt_2026-06-30.md`
- Twelfth follow-up response: `reports/extended_pro_after_ratcast_exploration_pulls_pos_response_2026-06-30.md`
- Boundary before twelfth follow-up: `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`
- Chosen twelfth follow-up leaf: `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO`
- Thirteenth follow-up prompt: `reports/extended_pro_after_ratcast_ne_zero_candidate_prompt_2026-06-30.md`
- Thirteenth follow-up response: `reports/extended_pro_after_ratcast_ne_zero_response_2026-06-30.md`
- Boundary before thirteenth follow-up: `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO`
- Chosen thirteenth follow-up leaf: `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION`
- Fourteenth follow-up prompt: `reports/extended_pro_after_empmean_definition_candidate_prompt_2026-06-30.md`
- Fourteenth follow-up response: `reports/extended_pro_after_empmean_definition_response_2026-06-30.md`
- Boundary before fourteenth follow-up: `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION`
- Chosen fourteenth follow-up leaf: `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION`
- Fifteenth follow-up prompt: `reports/extended_pro_after_empmean_numerator_meas_candidate_prompt_2026-06-30.md`
- Fifteenth follow-up response: `reports/extended_pro_after_empmean_numerator_meas_response_2026-06-30.md`
- Boundary before fifteenth follow-up: `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION`
- Chosen fifteenth follow-up leaf: `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
- Sixteenth follow-up prompt: `reports/extended_pro_after_empmean_div_const_candidate_prompt_2026-06-30.md`
- Sixteenth follow-up response: `reports/extended_pro_after_empmean_div_const_response_2026-06-30.md`
- Boundary before sixteenth follow-up: `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
- Chosen sixteenth follow-up leaf: `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON`
- Seventeenth follow-up prompt: `reports/extended_pro_after_empmean_meas_candidate_prompt_2026-06-30.md`
- Seventeenth follow-up response: `reports/extended_pro_after_empmean_meas_response_2026-06-30.md`
- Boundary before seventeenth follow-up: `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION`
- Chosen seventeenth follow-up leaf: `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES`
- Implemented next plausible leaf from the seventeenth response: `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER`
- Eighteenth follow-up prompt: `reports/extended_pro_after_commit_oracle_argmax_candidate_prompt_2026-06-30.md`
- Eighteenth follow-up response: `reports/extended_pro_after_commit_oracle_argmax_response_2026-06-30.md`
- Boundary before eighteenth follow-up: `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER`
- Chosen eighteenth follow-up leaf: `ETC-COMMIT-ORACLE-PROB-WRAPPER`
- Nineteenth follow-up prompt: `reports/extended_pro_after_commit_oracle_prob_candidate_prompt_2026-06-30.md`
- Nineteenth follow-up response: `reports/extended_pro_after_commit_oracle_prob_response_2026-06-30.md`
- Boundary before nineteenth follow-up: `ETC-COMMIT-ORACLE-PROB-WRAPPER`
- Chosen nineteenth follow-up leaf: `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL`
- Twentieth follow-up prompt: `reports/extended_pro_after_commit_oracle_filtered_candidate_prompt_2026-06-30.md`
- Twentieth follow-up response: `reports/extended_pro_after_commit_oracle_filtered_response_2026-06-30.md`
- Boundary before twentieth follow-up: `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL`
- Chosen twentieth follow-up leaf: `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL`
- Twenty-first follow-up prompt: `reports/extended_pro_after_commit_oracle_nonbest_candidate_prompt_2026-06-30.md`
- Twenty-first follow-up response: `reports/extended_pro_after_commit_oracle_nonbest_response_2026-06-30.md`
- Boundary before twenty-first follow-up: `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL`
- Chosen twenty-first follow-up leaf: `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY`
- Twenty-second follow-up prompt: `reports/extended_pro_after_commit_oracle_event_meas_candidate_prompt_2026-06-30.md`
- Twenty-second follow-up response: `reports/extended_pro_after_commit_oracle_event_meas_response_2026-06-30.md`
- Boundary before twenty-second follow-up: `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY`
- Chosen twenty-second follow-up route: `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD`
- Implemented compiled candidate from the twenty-second response: `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE`
- Twenty-third follow-up prompt: `reports/extended_pro_after_commit_oracle_choice_meas_candidate_prompt_2026-06-30.md`
- Twenty-third follow-up response: `reports/extended_pro_after_commit_oracle_choice_meas_response_2026-06-30.md`
- Boundary before twenty-third follow-up: `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE`
- Chosen twenty-third follow-up leaf: `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`
- Twenty-fourth follow-up prompt: `reports/extended_pro_after_empmean_vector_meas_candidate_prompt_2026-06-30.md`
- Twenty-fourth follow-up response: `reports/extended_pro_after_empmean_vector_meas_response_2026-06-30.md`
- Boundary before twenty-fourth follow-up: `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`
- Chosen twenty-fourth follow-up leaf: `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`
- Twenty-fifth follow-up prompt: `reports/extended_pro_after_oracle_choice_coord_meas_candidate_prompt_2026-06-30.md`
- Twenty-fifth follow-up response: `reports/extended_pro_after_oracle_choice_coord_meas_response_2026-06-30.md`
- Boundary before twenty-fifth follow-up: `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`
- Chosen twenty-fifth follow-up leaf: `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`
- Local review prompt: `reports/local_dual_review_after_oracle_wrong_event_coord_meas_prompt_2026-06-30.md`
- Local review response: `reports/local_dual_review_after_oracle_wrong_event_coord_meas_decision_2026-06-30.md`
- Boundary before local review: `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`
- Chosen local route card: `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`
- Implemented local route leaf: `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX`
- Local review after concrete argmax:
  `reports/local_dual_review_after_concrete_argmax_decision_2026-06-30.md`
- Implemented local post-argmax leaf:
  `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`
- Implemented pairwise-tail contract surface:
  `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE`
- Implemented empirical-mean finite-sum comparison bridge:
  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM`
- Implemented independent sub-Gaussian finite-sum tail import wrapper:
  `TAIL-SUBGAUSS-SUM`
- Implemented sub-Gaussian pairwise-tail producer surface:
  `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS`
- Implemented centered reward-difference Finset bridge:
  `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`
- Implemented centered-diff sub-Gaussian producer specialization:
  `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF`
- Implemented centered-diff sub-Gaussian witness contract:
  `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT`
- Implemented centered-diff canonical sub-Gaussian tail helper:
  `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL`
- Implemented fixed product-coordinate Real wrong-commit probability bridge:
  `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND`
- Implemented concrete argmax/infinitePi lower-integral regret assembly:
  `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY`
- Implemented polished fixed product-coordinate bad-gap lower-integral wrapper:
  `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER`
- Implemented conservative sum-gap suffix adapter:
  `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY`
- Implemented polished fixed product-coordinate sum-gap lower-integral wrapper:
  `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER`
- Implemented sharper max-gap suffix adapter:
  `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY`
- Implemented polished fixed product-coordinate max-gap wrapper:
  `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER`

## Leaf

`ETC-WRONG-COMMIT-PROBABILITY-DESIGN`

## Exact Lean-Facing Statement Shape

Do not add this as a local Lean theorem yet.  The intended theorem-card shape is:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_commit : Measurable commitArm)
    (hmeas_empMean : forall a : Fin K, Measurable (fun omega => empMean omega a))
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hbest_gap_pos :
      forall a : Fin K, (a = model.bestArm -> False) -> 0 < model.gap a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

The `reward` and `hbest_gap_pos` fields are intentionally part of the design
contract, but the first compiled proof attempt may discover that they are not
needed for this event-inclusion layer.

## Local APIs And Imports

Expected imports when promoted to a proof attempt:

```lean
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC
```

Useful local evidence:

- `FiniteBanditModel.gap_bestArm`
- `FiniteBanditModel.gap_nonneg`
- `FiniteBanditModel.mean_le_bestArm_mean`
- `ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le`
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm`

The event-reduction theorem itself should only need the commit-arm argmax
contract and measure monotonicity; the deterministic ETC trace/regret lemmas are
evidence for why this event reduction is the right next bridge.

## Intended Design Route

1. Show set inclusion from the wrong-commit event to the empirical comparison event.
2. For `omega` in the wrong-commit event, set `a := commitArm omega`.
3. Use `hcommit_argmax omega model.bestArm` to get
   `empMean omega model.bestArm <= empMean omega (commitArm omega)`.
4. Repackage that as an existential comparison event.
5. Apply monotonicity of `mu`.

No concentration inequality is used in this layer.

## Regularity Contracts

Keep these explicit:

- `[MeasurableSpace Omega]`
- `mu : Measure Omega`
- `[MeasureTheory.IsProbabilityMeasure mu]`
- `commitArm : Omega -> Fin K`
- `empMean : Omega -> Fin K -> Rat`
- `hmeas_commit : Measurable commitArm`
- `hmeas_empMean : forall a, Measurable (fun omega => empMean omega a)`
- `hcommit_argmax : forall omega a, empMean omega a <= empMean omega (commitArm omega)`

Do not introduce yet:

- filtration;
- conditional expectation;
- sub-Gaussian assumptions;
- Hoeffding or martingale tails;
- reward independence;
- Bochner expectation;
- final ETC regret.

## Retrieval Evidence

Extended Pro selected this after the deterministic fixed-commit ETC layer was
closed through:

- trace phase theorems;
- exploration-prefix and suffix count facts;
- exploration-horizon regret bound;
- suffix regret phase split;
- best-arm suffix no-regret and suffix regret bound;
- best-arm commit-phase trace theorem.

Mathlib route expected later:

- measurable set construction for commit-arm inequality events;
- measure monotonicity over set inclusion;
- Mathlib/Rat division-measurability import or wrapper, argmax wiring, and
  pairwise concentration/tail wrappers.

## First Compiled Event Leaf

Extended Pro selected the commit-arm wrong-event measurability canary in
`reports/extended_pro_after_wrong_commit_design_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False}
```

Status: project-local compiled event/measurability leaf.

This theorem only consumes singleton measurability and complement closure.  It
does not prove empirical-mean comparison measurability, event reduction, measure
monotonicity, concentration, or final ETC regret.

## Compiled Event-Reduction Leaf

Extended Pro next selected the pure wrong-commit set-inclusion leaf in
`reports/extended_pro_after_commitarm_ne_bestarm_meas_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    Set.Subset
      {omega : Omega | commitArm omega = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

Status: project-local compiled event-reduction leaf.

This theorem only consumes the explicit empirical-mean argmax contract.  It
does not require or prove measurability, measure monotonicity, probability,
finite event unions, concentration, or final ETC regret.

## Compiled Measure-Wrapper Leaf

Extended Pro next selected the measure monotonicity wrapper in
`reports/extended_pro_after_wrong_commit_subset_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

Status: project-local compiled probability-wrapper leaf.

This theorem only consumes `Measure.mono`/`mu.mono` and the compiled set
inclusion.  It does not require a probability measure, event measurability,
empirical-mean measurability, finite event unions, concentration, or final ETC
regret.

## Compiled Pairwise Empirical-Mean Event Leaf

Extended Pro next selected the pairwise ordered-event measurability canary in
`reports/extended_pro_after_wrong_commit_measure_wrapper_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b}
```

Status: project-local compiled event-regularity leaf.

This theorem only consumes coordinate measurability of `empMean` and Mathlib's
ordered measurable comparison API.  It does not prove finite existential/union
event measurability, concentration, filtration, empirical-mean construction, or
final ETC regret.

## Compiled Finite Existential Wrong-Mean Event Leaf

Extended Pro next selected the finite existential wrong-mean event
measurability wrapper in
`reports/extended_pro_after_empmean_pairwise_meas_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

Status: project-local compiled event-regularity leaf.

This theorem consumes finite-arm enumeration through `Finset.univ`,
`Finset.measurableSet_biUnion`, and the compiled pairwise comparison event
wrapper.  It does not prove a probability union bound, concentration,
filtration, empirical-mean construction, or final ETC regret.

## Compiled Finite-Union Probability Wrapper Leaf

Extended Pro next selected the finite-union probability upper-bound wrapper in
`reports/extended_pro_after_finite_wrong_mean_event_meas_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

Status: project-local compiled probability-wrapper leaf.

This theorem consumes `MeasureTheory.measure_biUnion_finset_le` and a bounded
union representation over `Finset.univ`.  It does not require event
measurability, empirical-mean coordinate measurability, a probability measure,
`commitArm`, argmax, concentration, filtration, empirical-mean construction, or
final ETC regret.

The generic reusable form now also compiles as
`ProbabilityUnionBound.measure_biUnion_finset_le` and
`ProbabilityUnionBound.measure_iUnion_fintype_le_sum` in
`BanditRLProof.ProbabilityUnionBound`; the ETC theorem above is the guarded
wrong-mean specialization.

## Compiled Final Elementary Probability Assembly Leaf

Extended Pro next selected the terminal elementary event-probability assembly in
`reports/extended_pro_after_finite_union_wrong_mean_prob_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

Status: project-local compiled elementary probability-assembly leaf.

This theorem consumes only
`ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`,
`ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`, and `le_trans`.  It
does not require event measurability, empirical-mean coordinate measurability, a
probability measure, concentration, filtration, empirical-mean construction,
pairwise tail bounds, or final ETC regret.

## Compiled Abstract Pairwise-Tail Consumer Leaf

Extended Pro next selected the abstract unguarded pairwise-tail wrapper in
`reports/extended_pro_after_wrong_commit_sum_assembly_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum tail
```

Status: project-local compiled tail-consumer probability-wrapper leaf.

This theorem consumes
`ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`,
`Finset.sum_le_sum`, guard erasure by `mu.mono`, and the abstract non-best
pairwise tail assumptions.  It does not prove the pairwise tail assumptions
themselves, and it does not require a probability measure, event measurability,
empirical-mean construction, actual concentration, filtration, conditional
expectation, independence, or final ETC regret.

## Compiled If-Zeroed Nonbest Pairwise-Tail Consumer Leaf

Extended Pro next selected the if-zeroed nonbest pairwise-tail wrapper in
`reports/extended_pro_after_pairwise_tail_response_2026-06-30.md`.  It now
compiles locally as:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

Status: project-local compiled if-zeroed tail-consumer probability-wrapper
leaf.

This theorem consumes
`ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`,
`Finset.sum_le_sum`, empty-event simplification for the best-arm summand,
guard erasure by `mu.mono`, and the abstract non-best pairwise tail
assumptions.  It does not prove empirical-mean construction, actual
concentration, filtration, conditional expectation, independence, the filtered
`Finset.filter` normalization, or final ETC regret.

## Compiled Filtered-Sum Pairwise-Tail Consumer Leaf

Extended Pro next selected the true filtered-sum normalization wrapper in
`reports/extended_pro_after_nonbest_pairwise_tail_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

Status: project-local compiled filtered-sum tail-consumer probability-wrapper
leaf.

This theorem consumes
`ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`,
`Finset.sum_filter`, and `Finset.sum_congr`.  It only normalizes the RHS from
the if-zeroed `Finset.univ` sum to an explicit filtered sum over non-best arms.
It does not prove empirical-mean construction, actual concentration,
filtration, conditional expectation, independence, or final ETC regret.

## Compiled Exploration Pull-Count Positivity Leaf

Extended Pro next selected the deterministic Nat-level denominator-positivity
leaf in
`reports/extended_pro_after_filtered_sum_pairwise_tail_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K)
```

Status: project-local compiled deterministic trace-count support leaf.

This theorem consumes
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq` and only rewrites
the configured exploration-horizon count to `spec.explorationPulls`.  It does
not define empirical means, introduce a measure, or prove concentration,
filtration, conditional expectation, independence, or final ETC regret.

## Compiled Rat-Cast Exploration Pull-Count Positivity Leaf

Extended Pro next selected the Rat-cast denominator adapter in
`reports/extended_pro_after_exploration_pulls_pos_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

Status: project-local compiled Rat denominator adapter.

This theorem consumes
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos` and transports the
Nat positivity theorem across the Nat-to-Rat cast with `exact_mod_cast`.  It
does not define empirical means, introduce a measure, or prove concentration,
filtration, conditional expectation, independence, or final ETC regret.

## Compiled Rat-Cast Exploration Pull-Count Nonzero Leaf

Extended Pro next selected the Rat nonzero denominator adapter in
`reports/extended_pro_after_ratcast_exploration_pulls_pos_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0)
```

Status: project-local compiled Rat nonzero-denominator adapter.

This theorem consumes
`ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos` and
converts strict Rat positivity into nonzeroness with `ne_of_gt`.  It does not
define empirical means, introduce division or zero-fallback API choices,
introduce a measure, or prove concentration, filtration, conditional
expectation, independence, or final ETC regret.

## Compiled Fixed-Commit Exploration Empirical-Mean Leaf

Extended Pro next selected the deterministic empirical-mean construction in
`reports/extended_pro_after_ratcast_ne_zero_response_2026-06-30.md`.  It now
compiles locally as:

```lean
def ETC.empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat

theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat)
```

Status: project-local compiled deterministic empirical-mean API.

The theorem unfolds `ETC.empMeanAtExploration` and rewrites the denominator
with `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.  It requires
only `spec : ETC.Spec K`, `commitArm a : Fin K`, and
`reward : RewardTrace Rat`; no `0 < spec.explorationPulls` proof is needed for
this rewrite because Rat division is total.  It does not introduce an argmax
oracle, stochastic reward trace, empirical-mean measurability wrapper,
probability measure, concentration, filtration, conditional expectation,
independence, or final ETC regret.

## Compiled Fixed-Commit Exploration Numerator-Measurability Leaf

Extended Pro next selected the numerator-measurability bridge in
`reports/extended_pro_after_empmean_definition_response_2026-06-30.md`.  It
now compiles locally as:

```lean
theorem ETC.measurable_sumRewards_actionWithCommit_exploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K))
```

Status: project-local compiled numerator-measurability bridge.

The theorem instantiates `measurable_sumRewards` with the constant stochastic
action trace `fun _ : Omega => ETC.actionWithCommit spec commitArm`, then
discharges action-coordinate measurability by `measurable_const`.  It consumes
only timewise reward-coordinate measurability and the usual measurable-space
contracts for `Omega`, `Fin K`, and `Rat`.  It does not introduce `Measure`,
`MeasurableDiv`, argmax wiring, concentration, filtration, conditional
expectation, independence, or final ETC regret; by itself it is only the
numerator bridge.

## Compiled Fixed-Commit Exploration Empirical-Mean Measurability Leaf

Extended Pro next selected the full empirical-mean measurability wrapper in
`reports/extended_pro_after_empmean_numerator_meas_response_2026-06-30.md`.
It now compiles locally as:

```lean
theorem ETC.measurable_empMeanAtExploration_of_measurable_div_const
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

Status: project-local compiled full empirical-mean measurability wrapper.

The theorem composes the compiled numerator-measurability bridge with the
explicit division-by-constant contract and unfolds `ETC.empMeanAtExploration`.
It does not decide the Mathlib/Rat division import route, introduce `Measure`,
argmax wiring, concentration, filtration, conditional expectation,
independence, or final ETC regret.

## Compiled Rat Division-By-Constant Measurability Wrapper

Extended Pro next selected the corrected Rat division wrapper in
`reports/extended_pro_after_empmean_div_const_response_2026-06-30.md`.  It now
compiles locally as:

```lean
theorem measurable_rat_div_const
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat]
    (c : Rat) :
    Measurable (fun x : Rat => x / c)
```

Status: project-local compiled import-route wrapper.

The theorem uses `Mathlib.Data.Rat.Encodable` and
`Mathlib.MeasureTheory.MeasurableSpace.Basic`, then closes by
`measurable_of_countable`.  The corrected contract is important: it does not
claim that all functions `Rat -> Rat` are measurable under an arbitrary
`[MeasurableSpace Rat]`; it also requires `[MeasurableSingletonClass Rat]`.
It does not remove `hdiv_const` from the ETC empirical-mean theorem in this
batch, prove argmax wiring, concentration, filtration, conditional
expectation, independence, or final ETC regret.

## Compiled No-Explicit-Division Fixed-Commit Empirical-Mean Measurability Leaf

The local Rat wrapper has now been consumed by the ETC empirical-mean layer.
The resulting theorem compiles locally as:

```lean
theorem ETC.measurable_empMeanAtExploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

Status: project-local compiled empirical-mean measurability wrapper.

The theorem is a thin consumer of
`ETC.measurable_empMeanAtExploration_of_measurable_div_const` and
`measurable_rat_div_const`.  It does not prove commit argmax wiring, actual
pairwise tails, filtration, conditional expectation, independence, or final
ETC regret.

## Compiled Coordinate Fixed-Commit Empirical-Mean Measurability Leaf

Extended Pro next selected the coordinate-shaped wrapper in
`reports/extended_pro_after_empmean_meas_response_2026-06-30.md`.  It compiles
locally as:

```lean
theorem ETC.measurable_empMeanAtExploration_coordinates
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    forall a : Fin K,
      Measurable (fun omega : Omega =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec commitArm (reward omega) b) a)
```

Status: project-local compiled coordinate wrapper.

The theorem simply packages `ETC.measurable_empMeanAtExploration` in the
`forall a : Fin K, Measurable ...` shape consumed by existing
empirical-mean event measurability lemmas.  It does not introduce
`ETC.CommitOracle`, argmax contracts, pairwise concentration, filtration,
conditional expectation, or final probability instantiation.

## Compiled Abstract Commit-Oracle Argmax Consumer Leaf

The next plausible leaf recommended in
`reports/extended_pro_after_empmean_meas_response_2026-06-30.md` now compiles
locally as:

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
    {Omega : Type u} {K : Nat}
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores)) :
    Set.Subset
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

Status: project-local compiled event-reduction consumer.

The theorem instantiates the previously compiled
`ETC.wrong_commit_subset_exists_empMean_ge_bestArm` with
`commitArm omega := oracle.choose (empMean omega)` and derives the required
argmax contract from `hchoose_argmax`.  It does not construct a concrete
argmax oracle, prove oracle measurability, add a probability measure, prove
pairwise concentration, add filtration, or instantiate the final ETC theorem.

## Compiled Oracle-Specialized Pairwise-Tail Probability Wrapper

Extended Pro selected Candidate A in
`reports/extended_pro_after_commit_oracle_argmax_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum tail
```

Status: project-local compiled oracle-specialized probability wrapper.

The theorem specializes
`ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail` to
`commitArm omega := oracle.choose (empMean omega)` and derives the arbitrary
commit-arm argmax contract from `hchoose_argmax`.  It does not require a
probability measure instance, event measurability, oracle measurability,
concrete oracle construction, actual concentration, filtration, or final ETC
regret.

## Compiled Oracle-Specialized Filtered-Sum Pairwise-Tail Probability Wrapper

Extended Pro selected Candidate B in
`reports/extended_pro_after_commit_oracle_prob_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

Status: project-local compiled oracle-specialized filtered-sum probability
wrapper.

The theorem specializes
`ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail` to
`commitArm omega := oracle.choose (empMean omega)` and derives the arbitrary
commit-arm argmax contract from `hchoose_argmax`.  It does not require a
probability measure instance, event measurability, oracle measurability,
concrete oracle construction, actual concentration, filtration, or final ETC
regret.

## Compiled Oracle-Specialized If-Zeroed Nonbest Pairwise-Tail Probability Wrapper

Extended Pro selected Candidate A in
`reports/extended_pro_after_commit_oracle_filtered_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

Status: project-local compiled oracle-specialized if-zeroed probability
wrapper.

The theorem specializes
`ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail` to
`commitArm omega := oracle.choose (empMean omega)` and derives the arbitrary
commit-arm argmax contract from `hchoose_argmax`.  It does not require a
probability measure instance, event measurability, oracle measurability,
concrete oracle construction, actual concentration, filtration, or final ETC
regret.

## Compiled Oracle-Selected Wrong-Event Measurability Wrapper

Extended Pro selected Candidate A in
`reports/extended_pro_after_commit_oracle_nonbest_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_choose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega))) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

Status: project-local compiled oracle-selected wrong-event measurability
wrapper.

The theorem specializes `ETC.measurableSet_commitArm_ne_bestArm` to
`commitArm omega := oracle.choose (empMean omega)` and consumes a direct
composed choice measurability contract.  It does not require a measure,
probability instance, concrete oracle construction, proof of oracle choice
measurability from empirical means, actual concentration, filtration, or final
ETC regret.

## Compiled Oracle-Choice Measurability Bridge

Extended Pro selected Candidate C in
`reports/extended_pro_after_commit_oracle_event_meas_response_2026-06-30.md`
and identified a project-local compiled candidate after the route-card check.
The resulting theorem compiles locally as:

```lean
theorem ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)]
    [MeasurableSpace (Fin K -> Rat)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_emp :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

Status: project-local compiled Mathlib-backed oracle-choice measurability
bridge.

The theorem uses Mathlib `measurable_of_countable` to show
`fun score : Fin K -> Rat => oracle.choose score` is measurable under explicit
countable score-vector and measurable-singleton contracts, then composes with
empirical-mean vector measurability.  It does not require concrete oracle
construction, argmax correctness, actual concentration, filtration, or final
ETC regret.

## Compiled Empirical-Mean Vector Measurability Bridge

Extended Pro selected Candidate A in
`reports/extended_pro_after_commit_oracle_choice_meas_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

Status: project-local compiled Mathlib Pi-space empirical-mean vector
measurability bridge.

The theorem applies Mathlib `measurable_pi_lambda` to package coordinatewise
empirical-mean measurability into vector-valued measurability for
`Fin K -> Rat` under the standard Pi measurable-space instance induced by
`[MeasurableSpace Rat]`.  It deliberately does not assume an arbitrary
`[MeasurableSpace (Fin K -> Rat)]`, construct an oracle, prove argmax
correctness, prove concentration, add filtration, or prove final ETC regret.

## Compiled Coordinatewise Oracle-Choice Measurability Wrapper

Extended Pro selected Candidate A in
`reports/extended_pro_after_empmean_vector_meas_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

Status: project-local compiled coordinatewise empirical-mean-to-oracle-choice
measurability composition wrapper.

The theorem composes
`ETC.measurable_empMeanVector_of_forall_measurable` with
`ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`.  It
produces oracle-choice measurability directly from coordinatewise empirical
mean measurability, while letting `[MeasurableSpace Rat]` synthesize the Pi
measurable-space instance for `Fin K -> Rat`.  It does not assume an arbitrary
local `[MeasurableSpace (Fin K -> Rat)]`, construct an oracle, prove argmax
correctness, introduce probability, prove concentration, add filtration, or
prove final ETC regret.

## Compiled Coordinatewise Oracle Wrong-Event Measurability Wrapper

Extended Pro selected Candidate A in
`reports/extended_pro_after_oracle_choice_coord_meas_response_2026-06-30.md`.
The resulting theorem compiles locally as:

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

Status: project-local compiled pairwise empirical-mean tail contract surface
and concrete argmax consumer.

This compiled leaf adds
`ETC.PairwiseEmpMeanTailContract` and
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`
in `BanditRLProof.Algorithms.ETCPairwiseTailContract`.  It packages the
fixed-commit ETC empirical-mean pairwise-tail assumption and consumes it through
the concrete argmax filtered probability wrapper.  It still does not prove the
tail contract, prove Hoeffding/sub-Gaussian concentration, add filtration, or
prove final ETC regret.

## Compiled Empirical-Mean Comparison Finite-Sum Leaf

The latest compiled leaf adds
`ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos` in
`BanditRLProof.Algorithms.ETCEmpiricalMean`:

```lean
theorem ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a b : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.empMeanAtExploration spec commitArm reward b <=
      ETC.empMeanAtExploration spec commitArm reward a ↔
    sumRewards (ETC.actionWithCommit spec commitArm) reward b
        (spec.explorationPulls * K) <=
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
        (spec.explorationPulls * K)
```

Status: project-local compiled deterministic algebra leaf.

It removes the common positive exploration denominator from a pairwise
fixed-commit ETC empirical-mean comparison.  It does not center rewards, import
sub-Gaussian/Hoeffding concentration, introduce filtration, or prove final ETC
regret.

## Compiled Independent Sub-Gaussian Finite-Sum Tail Wrapper

`TAIL-SUBGAUSS-SUM` is now compiled locally in
`BanditRLProof.ConcentrationSubGaussian` as:

```lean
theorem Concentration.subGaussian_sum_tail_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= s.sum (fun i => X i omega)} <=
      Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))
```

Status: project-local compiled Mathlib import-wrapper leaf.

It exposes Mathlib
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` under the
project namespace.  It does not instantiate ETC reward differences, convert the
`mu.real` bound to the `ENNReal` tail surface, introduce filtration, or prove
final ETC regret.

## Compiled ENNReal Independent Sub-Gaussian Finite-Sum Tail Wrapper

`TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is now compiled locally in
`BanditRLProof.ConcentrationSubGaussian` as:

```lean
theorem Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= s.sum (fun i => X i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real))))
```

Status: project-local compiled Mathlib import/boundary-wrapper leaf.

It converts the independent sub-Gaussian finite-sum tail into the `ENNReal`
event-probability shape consumed by local pairwise-tail contracts.  It still
keeps the summands abstract and does not instantiate ETC reward differences,
introduce filtration, or prove final ETC regret.

## Compiled Conditional Sub-Gaussian Finite-Prefix Tail Wrapper

`TAIL-COND-SUBGAUSS` is now compiled locally in
`BanditRLProof.ConcentrationSubGaussian` as:

```lean
theorem Concentration.condSubGaussian_sum_tail_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))
```

Status: project-local compiled Mathlib import/boundary-wrapper leaf.

The companion declaration
`Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted` gives the
same strongly adapted conditional tail in the `ENNReal.ofReal` event-measure
shape.  These wrappers do not define an ETC history filtration, prove
full policy predictability, provide conditional MGF witnesses for reward
differences, or prove final ETC regret.

## Compiled Finite-History Product Surface

`MEAS-HISTORY` is now compiled locally in
`BanditRLProof.HistoryFiltration` as `History.FiniteActionHistory`,
`History.FiniteRewardHistory`, `History.FiniteHistory`, the corresponding
`History.finite*OfTrace` restriction maps, coordinate projection measurability
theorems, and full-trace-to-finite-history measurability theorems over
`Finset.Iic` prefixes.  This is a product-object and trace-restriction
measurability surface.  It does not prove filtration generation, policy
predictability, kernel-law assembly, conditional reward-law transfer,
conditional expectation identities, posterior kernels, or final adaptive ETC
regret.

## Compiled History Filtration Canary

`FILTRATION-HISTORY` is now compiled locally in
`BanditRLProof.HistoryFiltration` as `History.historyFiltration`, with
supporting declarations for history generators, generated sigma-algebras,
monotonicity, ambient sub-sigma-algebra inclusion, and past action/reward
singleton-event measurability.  This is a singleton-event history canary.  It
does not prove policy predictability, conditional reward laws, conditional
expectation identities, conditional MGF witnesses, kernels, or final adaptive
ETC regret.

## Compiled Adapted-Coordinate Canary

`ADAPTED-ACTION` is now compiled locally in
`BanditRLProof.HistoryFiltration` as
`History.measurable_action_mem_historyFiltration_of_lt`, with the reward-side
companion `History.measurable_reward_mem_historyFiltration_of_lt`.  These
theorems show that past action/reward coordinates are measurable with respect
to the generated history filtration under countable/discrete codomain
contracts.  They do not prove arbitrary policy predictability, conditional
reward laws, conditional MGF witnesses, or final adaptive ETC regret.

## Compiled Policy Measurability Surface

`MEAS-POLICY` is now compiled locally in
`BanditRLProof.PolicyMeasurability` as `Policy.MeasurablePolicy`,
`Policy.measurable_action_of_measurable_state`,
`Policy.measurable_action_mem_filtration_of_measurable_state`, and
`Policy.measurable_action_mem_historyFiltration_of_measurable_state`.  It
packages a measurable policy action map and proves that composing it with a
measurable history/context state gives a measurable action, including
arbitrary-filtration and generated-history-filtration specializations.  It
does not construct kernels, policy-generated trajectories, reward laws,
conditional reward laws, or final adaptive ETC regret.

`POLICY-GENERATED-ACTION-TRACE-MEASURABILITY` is now compiled locally in
`BanditRLProof.PolicyMeasurability` as `Policy.generatedActionTrace`,
`Policy.measurable_generatedActionTrace_eval_of_measurable_state`,
`Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state`,
and
`Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state`.
It turns a measurable policy plus a time-indexed measurable state process into
an action trace with coordinate measurability.  It does not construct reward
kernels, bind kernels, trajectory measures, conditional reward laws, or final
adaptive ETC regret.

`KERNEL-REWARD` is now compiled locally in `BanditRLProof.RewardKernel` as
`RewardKernel.MarkovRewardKernel`,
`RewardKernel.measurable_apply_of_measurable_index`,
`RewardKernel.measurable_eventProbability_of_measurable_index`,
`RewardKernel.isProbabilityMeasure_apply`,
`RewardKernel.selectedMeasure`,
`RewardKernel.measurable_selectedMeasure_of_measurable`, and
`RewardKernel.measurable_selectedEventProbability_of_policy_state`.  It wraps
Mathlib `ProbabilityTheory.Kernel` plus `IsMarkovKernel` as an arm/context
reward-law contract and proves that measurable context/action or policy/state
inputs select measurable reward measures and event probabilities.  It does not
bind policy and reward kernels, construct trajectory measures, derive
conditional reward laws, or prove final adaptive ETC regret.

`POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION` is now compiled locally in
`BanditRLProof.RewardKernel` as `RewardKernel.policyContextStateIndex`,
`RewardKernel.measurable_policyContextStateIndex`,
`RewardKernel.composePolicy`, `RewardKernel.composePolicy_kernel_apply`,
`RewardKernel.isMarkovKernel_composePolicy`, and
`RewardKernel.measurable_composePolicy_eventProbability`.  It composes a
measurable policy with a context/action Markov reward kernel to obtain a
context/state Markov reward kernel.  It does not construct a finite-horizon
trajectory law, perform Ionescu-Tulcea assembly, derive conditional reward
laws, or prove final adaptive ETC regret.

`POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` is now compiled locally in
`BanditRLProof.RewardKernel` as `RewardKernel.historyStepRewardKernel`,
`RewardKernel.historyStepKernelFamily`,
`RewardKernel.historyStepKernelFamily_apply`,
`RewardKernel.isMarkovKernel_historyStepKernelFamily`,
`RewardKernel.measurable_historyStepKernelFamily_eventProbability`,
`RewardKernel.partialTrajectoryKernel`,
`RewardKernel.isMarkovKernel_partialTrajectoryKernel`, and
`RewardKernel.measurable_partialTrajectoryKernel_eventProbability`.  It turns
time-indexed measurable policies plus measurable context/state extractors from
`Finset.Iic` reward histories into Mathlib `partialTraj` finite-prefix
reward-history kernels.  It does not derive conditional reward-law transfer,
build posterior kernels, prove infinite trajectory laws, or prove final
adaptive ETC regret.

`KERNEL-POLICY-BIND` is now compiled locally in `BanditRLProof.RewardKernel`
as `RewardKernel.policyActionKernel`,
`RewardKernel.composePolicyActionReward`,
`RewardKernel.actionRewardHistoryStepKernelFamily`, and
`RewardKernel.actionRewardPartialTrajectoryKernel`, with Markov-kernel,
event-probability measurability, and selected-reward marginal wrappers.  It
turns deterministic policy
action kernels plus selected reward kernels into one-step `(Action × Reward)`
kernels and feeds them to Mathlib `partialTraj` for finite-prefix
action/reward pair trajectories.  `RewardKernel.CenteredRewardKernelLaw` also
transfers centered integrability, zero-integral, and sub-Gaussian MGF witnesses
through policy/history step kernels.  It does not identify `condExpKernel`
reward laws for those trajectories, build posterior kernels, prove infinite
trajectory laws, or prove final adaptive ETC regret.

## Compiled Conditional Centered-Diff Witness Contract

`ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is now compiled locally in
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` as
`ETC.CenteredDiffCondSubGaussianWitnesses` and
`ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`.
The package consumes per-arm filtrations, `StronglyAdapted` centered
reward-difference processes, zeroth `HasSubgaussianMGF`, later
`HasCondSubgaussianMGF`, and tail domination to produce
`ETC.PairwiseEmpMeanTailContract`.  It does not derive those fields from a
concrete reward law, prove a conditional expectation identity, prove full
policy predictability, or prove final adaptive ETC regret.

`ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY` is now also compiled locally in
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.  It introduces
`History.historyFiltrationSucc` and proves
`ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc`, so the
fixed-commit centered reward-difference process has the required
`StronglyAdapted` field under timewise reward-coordinate measurability.  It
still does not prove conditional MGF, conditional mean-zero, full policy
predictability, or final adaptive ETC regret.

`ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS` is now compiled locally in
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` as
`ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss`, and
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss`.
It proves the unconditional and conditional zero-variance MGF witnesses for
time indices where `actionWithCommit` pulls neither the comparison arm nor
`model.bestArm`.

`ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER` is now compiled locally in
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` as
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm`,
and
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm`.
It transfers sampled centered-reward conditional MGF witnesses to centered
pairwise reward differences when `actionWithCommit` pulls either the
comparison arm or `model.bestArm`.

`ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is now compiled locally
in `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` as
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward`,
`ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward`,
`ETC.CenteredRewardCondSubGaussianWitnesses`, and
`ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`.
It packages sampled centered-reward conditional MGF witnesses and constructs
`ETC.CenteredDiffCondSubGaussianWitnesses`.  Fixed-action bounded/source
assembly is now compiled separately in
`ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE`, and its canonical-tail
no-`htail` form is compiled as
`ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-BOUNDED-SOURCE`; the fixed
product-coordinate specialization is compiled as
`ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE`.  Kernel-law
conditional MGF, full policy predictability, and final adaptive ETC regret
remain open.

`ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE` is now compiled locally in
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` as
`ETC.centeredReward_condExp_eq_zero_of_indep`,
`ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep`,
`ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`, and
`ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`.
It wraps Mathlib `MeasureTheory.condExp_indep_eq`: centered reward conditional
expectation is zero when the centered reward coordinate is independent of the
conditioning sigma-algebra and has integral zero.  The shifted-history
specialization targets `History.historyFiltrationSucc`; the succ-indexed
specialization targets the Mathlib conditional-tail shape; the iIndepFun
specialization consumes the fixed-action full-history independence bridge.  It
still does not produce conditional MGF witnesses.

`ETC-CENTERED-REWARD-COND-MGF-INDEP-SOURCE` is now compiled locally in
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` as
`ETC.hasCondSubgaussianMGF_of_indep_comap` and
`ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`.
The Lean-facing generic statement is:

```lean
theorem ETC.hasCondSubgaussianMGF_of_indep_comap
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real) (c : NNReal)
    (hmeasX : @Measurable Omega Real mOmega inferInstance X)
    (h_subG : ProbabilityTheory.HasSubgaussianMGF X c mu)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap X inferInstance) mcond mu) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu
```

The ETC-shaped consumer is:

```lean
theorem ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) (c : NNReal)
    (h_subG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward (fun _t : Nat => measurable_const) hreward i)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward (fun _t : Nat => measurable_const) hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      c mu
```

Local APIs/imports: `Mathlib.Probability.Moments.SubGaussian`,
`Mathlib.Probability.Kernel.Condexp`, `Mathlib.Probability.ConditionalExpectation`,
`ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat`,
`ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel`,
`MeasureTheory.condExp_indep_eq`, and the local
`ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`.
Proof route: unfold `HasCondSubgaussianMGF` to the conditional expectation
kernel form, prove the kernel MGF bound first on rational exponents with
`of_rat`, identify the conditional-kernel integral with conditional expectation,
then use independence to rewrite the conditional expectation to the global MGF
and close by `h_subG.mgf_le`.  The `of_rat` step requires fully explicit
ambient measurable-space arguments for `condExpKernel`, `condExp`, and the
kernel integral; otherwise Lean may synthesize the conditioning sigma-algebra
where the ambient one is needed.  Status: project-local.  Failure policy: keep
this leaf as a bridge only; bounded/source assembly is now handled separately,
and kernel-law or full-policy failures should not weaken this statement or
start final ETC theorem work.

`ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE` is now compiled locally across
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
`BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource` as
`ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward` and
`ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`.  It derives
independence of the centered reward at time `i + 1` from the reward-only past
coordinate sigma-algebra generated by `j <= i`, with an infinite-product
specialization.

`ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE` is now compiled locally across
`BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
`BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource` as
`ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup`,
`ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`, and
`ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi`.  It extends
the reward-only past bridge to fixed `actionWithCommit`
`History.historyFiltrationSucc` independence.

`INT-REWARD-BOUNDED` /
`ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE` is now compiled locally across
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
`BanditRLProof.Algorithms.ETCBoundedRewardSource` as
`ETC.centeredReward_integrable_of_mem_Icc` and
`ETC.centeredReward_integrable_of_boundedRewardTraceSource`.  It wraps Mathlib
`MeasureTheory.Integrable.of_mem_Icc`, turning a.e. measurable and a.s.
bounded reward coordinates into raw reward integrability.

`ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE` is now compiled locally across
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
`BanditRLProof.Algorithms.ETCBoundedRewardSource` as
`ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`,
`ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, and
`ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`.  It
proves the zero-integral side condition for centered rewards from an exact raw
mean identity plus raw reward integrability or bounded-Icc facts, and
instantiates the exact mean through `ETC.BoundedRewardTraceSource.mean`.  It
still does not prove conditional MGF witnesses.

`ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE` is now compiled locally in
`BanditRLProof.Algorithms.ETCBoundedRewardSource` as
`ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`.
It combines `ETC.BoundedRewardTraceSource.indep`, the action-matched
zero-integral wrapper above, and the existing succ-indexed fixed-history
conditional mean-zero theorem.  It is fixed to deterministic
`ETC.actionWithCommit`; it is not a condExpKernel trajectory-law theorem or a
final adaptive-policy conditional expectation theorem.

`MART-DIFF-REWARD` now has compiled global and finite-prefix witness surfaces
in `BanditRLProof.MartingaleDifference` as
`MartingaleDiff.SuccMartingaleDifference` and
`MartingaleDiff.SuccMartingaleDifferencePrefix`.  The abstract partial-sum
Mathlib wrapper is compiled as
`MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference`.  The
fixed deterministic `actionWithCommit` bounded-source centered-reward instance
is compiled as
`ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource`.
This records adaptedness, prefix integrability, and succ-indexed conditional
mean-zero inside the exploration horizon for the fixed ETC source; it is not an
optional-stopping theorem, condExpKernel reward-law identification, or final
adaptive regret theorem.

## Compiled Sub-Gaussian Pairwise-Tail Producer Surface

`ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is now compiled locally in
`BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail` as
`ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`.  It produces
`ETC.PairwiseEmpMeanTailContract` from explicit non-best-arm independent
sub-Gaussian finite-sum witnesses, event-subset hypotheses, and tail RHS
domination inequalities.

Status: project-local compiled sub-Gaussian pairwise-tail producer surface.

It does not instantiate ETC reward differences, introduce filtration, or prove
final ETC regret.

## Compiled Empirical-Mean Event-Subset Bridge

`ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` is now compiled locally in
`BanditRLProof.Algorithms.ETCEmpiricalMean` as
`ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`.
It consumes
`ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos` and
turns a pointwise fixed-horizon `sumRewards bestArm <= sumRewards a`
implication into the set inclusion required by the sub-Gaussian producer:

```lean
theorem ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Idx -> Omega -> Real)
    (eps : Real)
    (himp :
      forall omega : Omega,
        sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            model.bestArm (spec.explorationPulls * K) <=
          sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            a (spec.explorationPulls * K) ->
        eps <= idx.sum (fun i => X i omega)) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega | eps <= idx.sum (fun i => X i omega)}
```

Status: project-local compiled event-shape bridge.

It does not construct centered reward-difference summands, prove independence
or sub-Gaussianity, introduce filtration, or prove final ETC regret.

## Compiled Centered Pairwise SumRewards Diff Bridge

`ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` is now compiled locally in
`BanditRLProof.Algorithms.ETCSumRewardsDiff`.  The main declarations are:

```lean
noncomputable def ETC.centeredPairwiseRewardDiff
noncomputable def ETC.centeredPairwiseGapThreshold
theorem ETC.sumRewards_le_imp_centered_pairwise_sum_ge
theorem ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event
```

Status: project-local compiled deterministic centered-diff bridge.

It connects the fixed-horizon `sumRewards bestArm <= sumRewards a` comparison
to the concrete centered reward-difference finite-sum event over
`Finset.range (spec.explorationPulls * K)`.  It does not prove independence,
sub-Gaussianity, filtration, or final ETC regret.

## Compiled Centered-Diff Sub-Gaussian Producer Specialization

`ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` is now compiled locally in
`BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail` as
`ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`.

Status: project-local compiled producer specialization.

It instantiates `ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`
with the concrete centered summands and exploration-horizon index set, and
derives nonnegative threshold from `FiniteBanditModel.mean_le_bestArm_mean`.
It still leaves independence, `HasSubgaussianMGF`, and tail RHS domination as
explicit hypotheses.

## Compiled Centered-Diff Sub-Gaussian Witness Contract

`ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` is now compiled locally in
`BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses`.

```lean
structure ETC.CenteredDiffSubGaussianWitnesses
theorem ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses
```

Status: project-local compiled witness contract surface.

The structure packages exactly the reward-law witnesses required by the
centered-diff producer: variance proxies, non-best-arm independence, per-index
`HasSubgaussianMGF` facts over the exploration horizon, and tail RHS
domination.  It does not prove those fields from a reward distribution,
filtration, conditional expectation, or kernel.

## Compiled Centered-Diff Canonical Sub-Gaussian Tail

`ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` is now compiled locally in
`BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail`.

```lean
noncomputable def ETC.centeredDiffSubGaussianTail
noncomputable def ETC.centeredDiffSubGaussianWitnesses_of_indep_subG
theorem ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG
```

Status: project-local compiled canonical tail helper.

This leaf chooses the exact exponential tail produced by the independent
sub-Gaussian route and removes the separate tail-domination hypothesis.  It
still requires the actual non-best-arm independence and per-index
`HasSubgaussianMGF` witnesses for `ETC.centeredPairwiseRewardDiff`; the later
independence-transfer leaf discharges the deterministic transform once
trace-level reward-coordinate independence is supplied.

## Compiled Canonical Wrong-Commit Probability Bound

`ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` is now compiled locally in
`BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail`.

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail
```

Status: project-local compiled canonical wrong-commit probability bound.

This leaf composes the canonical centered-diff `PairwiseEmpMeanTailContract`
producer with the concrete argmax-oracle filtered-sum wrong-commit probability
consumer.  It still requires the actual non-best-arm independence and
per-index `HasSubgaussianMGF` witnesses for
`ETC.centeredPairwiseRewardDiff`; it is not a full ETC expected-regret theorem.

## Compiled Centered-Diff Independence Transfer

`ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` is now compiled locally in
`BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence`.

```lean
theorem ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward
```

Status: project-local compiled deterministic independence transfer.

This leaf proves that time-coordinate `iIndepFun` for the raw reward trace
transfers to `ETC.centeredPairwiseRewardDiff` by `iIndepFun.comp`.  At this
layer, the remaining source obligation was trace-level reward independence,
and the leaf did not prove any `HasSubgaussianMGF` witness.
The later infinite-product bounded-reward source layer below discharges this
for a fixed product-coordinate reward source.

## Compiled Reward-Coordinate Sub-Gaussian Wrong-Commit Bound

`ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` and
`ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` are now compiled locally in
`BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`.

```lean
noncomputable def ETC.centeredPairwiseRewardDiffVarianceProxy
theorem ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG
```

Status: project-local compiled reward-coordinate-law wrong-commit bound.

This layer reduces the canonical wrong-commit probability theorem to two raw
reward-coordinate assumptions: time-coordinate independence of
`fun t omega => reward omega t`, and per-arm/time centered reward
`HasSubgaussianMGF` up to the exploration horizon.  It still does not build
that stochastic reward trace law from a kernel, boundedness assumption, or
filtration.

## Compiled Bounded-Reward Wrong-Commit Bound

`ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
`ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` are now compiled locally in
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.

```lean
noncomputable def ETC.centeredRewardBoundVarianceProxy
theorem ETC.centeredReward_integrable_of_mem_Icc
theorem ETC.centeredReward_integral_eq_zero_of_integral_eq_mean
theorem ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean
theorem ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered
```

Status: project-local compiled strong all-arm bounded-reward wrong-commit
probability bound.

This layer uses Mathlib's bounded-variable Hoeffding lemma to replace the
per-time centered reward `HasSubgaussianMGF` assumption with a.e.
measurability, a.s. interval bounds, and exact mean identities for raw reward
coordinates.  This version assumes those facts for every arm/time coordinate;
the practical fixed-commit route below weakens them to the arm actually pulled
at each time.  It still does not build those source facts or trace-level
reward-coordinate independence from a stochastic environment.

## Compiled Action-Matched Bounded-Reward Source Contract

`ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND`,
`ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND`, and
`ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT` are now compiled locally in
`BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
`BanditRLProof.Algorithms.ETCBoundedRewardSource`.

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered
structure ETC.BoundedRewardTraceSource
theorem ETC.centeredReward_integrable_of_boundedRewardTraceSource
theorem ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean
theorem ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource
```

Status: project-local compiled action-matched fixed-commit ETC source
contract and consumers.

This layer keys the boundedness and exact mean facts to
`ETC.actionWithCommit spec commitArm t`, which is the actual arm pulled at
time `t` in the fixed-commit ETC trace.  The next concrete source leaf should
construct the `ETC.BoundedRewardTraceSource` fields from a product-coordinate
law or another explicit stochastic model, not start final expected-regret
assembly.

## Compiled Infinite-Product Bounded-Reward Source

`ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
`ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE` are now compiled locally in
`BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.

```lean
theorem ETC.boundedRewardTraceSource_infinitePi_actionWithCommit
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean
```

Status: project-local compiled fixed-commit product-coordinate reward source
and wrong-commit probability bound.

This layer uses `Measure.infinitePi coordLaw` for reward traces
`RewardTrace Rat`, Mathlib's `iIndepFun_infinitePi`, coordinate projection
map identities, and coordinate integral transport to discharge the
`ETC.BoundedRewardTraceSource` fields.  It still does not build a random
selected-commit trace, adaptive filtration, conditional expectation route, or
expected-regret theorem.

## Compiled Fixed-Product Real Wrong-Commit Probability Bridge

`ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND` is now compiled locally in
`BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
theorem ETC.real_measure_fixedProductArgmaxCommit_ne_bestArm_le_fixedProductWrongCommitTailBudgetReal_of_infinitePi_bounded_actionMean
```

Status: project-local compiled `Measure.real` probability bridge for the
fixed-product argmax/infinitePi source.

This layer reuses
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`,
names the finite ENNReal supplier as
`ETC.fixedProductWrongCommitTailBudget`, converts it through
`ENNReal.toReal_mono`, and exposes the Real supplier
`ETC.fixedProductWrongCommitTailBudgetReal` consumed by Bochner expected-regret
wrappers.  Its regularity contracts are exactly the fixed product-coordinate
source contracts: probability coordinate laws, fixed `spec`, `model`, and
`baseCommitArm`, positive exploration count, action-matched coordinate a.s.
bounds, and coordinate mean identities.  It does not prove integrability,
event measurability beyond the compiled argmax source, lower-integral or
Bochner regret assembly, adaptive policy laws, or the final ETC theorem.

## Compiled Pointwise Wrong-Commit Regret Assembly

`ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` is now compiled locally in
`BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`.

```lean
theorem ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap
```

Status: project-local compiled pointwise deterministic regret assembly.

This layer turns an `Omega`-indexed commit selector into an exploration-budget
plus suffix-penalty bound.  The suffix term is `0` when the selected commit arm
is `model.bestArm`, and otherwise uses an explicit `badGapBound` for all
non-best gaps.  It still does not integrate the pointwise bound, prove event
measurability for this selector, or connect the suffix penalty to the compiled
wrong-commit probability inequality.

## Compiled Lower-Integral Wrong-Commit Regret Assembly

`ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` is now compiled locally in
`BanditRLProof.Algorithms.ETCExpectedRegretAssembly`.

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
```

Status: project-local compiled `ENNReal.ofReal` lower-integral regret
assembly with an abstract wrong-probability supplier.

This layer integrates the pointwise wrong-commit regret bridge under a
probability measure.  It consumes wrong-event measurability and an abstract
upper bound `pWrong` on the wrong-commit event probability, producing an
exploration lower-integral budget plus `suffixBudget * pWrong`.  It is not a
Bochner/Rat-valued expected-regret theorem and still does not instantiate the
concrete argmax oracle or the infinite-product wrong-commit probability bound.

## Compiled Concrete Argmax/InfinitePi Lower-Integral Regret Assembly

`ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` is now compiled locally
in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
```

Status: project-local compiled concrete `ENNReal.ofReal` lower-integral regret
assembly for the finite argmax commit oracle under an infinite product
bounded-reward source.

This layer defines the commit selector by applying `ETC.argmaxCommitOracle` to
the fixed-commit exploration empirical means, proves the wrong event is
measurable from `ETC.measurable_empMeanAtExploration_coordinates` and
`ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`, and
supplies the abstract `pWrong` bound with
`ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`.
It remains fixed-product/fixed-exploration and does not prove Bochner expected
regret, adaptive filtrations, conditional concentration, or final ETC theorem
assembly.

## Compiled Sum-Gap Suffix Adapter

`ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` is now compiled
locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean
```

Status: project-local compiled conservative suffix adapter.

This wrapper instantiates the concrete argmax/infinitePi lower-integral theorem
with `badGapBound := (Finset.univ : Finset (Fin K)).sum (fun a => model.gap a)`.
The non-best gap bound follows from `FiniteBanditModel.gap_nonneg` and Mathlib
`Finset.single_le_sum`.  It removes the explicit `badGapBound`/`hbadGap`
contract at the cost of a conservative suffix constant.  It still does not
introduce Bochner expectation or prove the final adaptive ETC theorem.

## Compiled Max-Gap Suffix Adapter

`ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY` is now compiled
locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
```

Status: project-local compiled sharper suffix adapter.

This wrapper instantiates the concrete argmax/infinitePi lower-integral theorem
with `badGapBound := model.maxGap`.  The non-best gap bound follows from
`FiniteBanditModel.gap_le_maxGap`, where `FiniteBanditModel.maxGap` is the
finite `Finset.sup'` maximum of local model gaps.  It removes the explicit
`badGapBound`/`hbadGap` contract with a sharper suffix constant.  It still does
not introduce Bochner expectation or prove the final adaptive ETC theorem.

## Compiled Fixed Product-Coordinate Bad-Gap Wrapper

`ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER` is now compiled locally in
`BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
noncomputable def ETC.fixedProductBadGapLintegralRegretBound

theorem ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductBadGapLintegralRegretBound_of_infinitePi_bounded_actionMean
```

Status: project-local compiled fixed product-coordinate bad-gap wrapper.

This wrapper names the argmax-commit action trace and the bad-gap
`ENNReal.ofReal` RHS budget, then reuses the compiled concrete bad-gap
infinitePi lower-integral theorem.  It remains fixed-product/fixed-exploration
and keeps the explicit `badGapBound` contract; it does not introduce Bochner
expectation, filtration, conditional concentration, or final adaptive ETC
theorem assembly.

## Compiled Fixed Product-Coordinate Sum-Gap Wrapper

`ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER` is now compiled locally in
`BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
noncomputable def ETC.fixedProductSumGapLintegralRegretBound

theorem ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductSumGapLintegralRegretBound_of_infinitePi_bounded_actionMean
```

Status: project-local compiled fixed product-coordinate conservative sum-gap
wrapper.

This wrapper names the argmax-commit action trace and the conservative
sum-gap `ENNReal.ofReal` RHS budget.  It reuses the fixed-product bad-gap
wrapper with `badGapBound` instantiated to the total finite sum of model gaps,
discharging the non-best gap bound with `FiniteBanditModel.gap_nonneg` and
`Finset.single_le_sum`.  It remains fixed-product/fixed-exploration and does
not introduce Bochner expectation, filtration, conditional concentration, or
final adaptive ETC theorem assembly.

## Compiled Fixed Product-Coordinate Max-Gap Wrapper

`ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` is now compiled locally in
`BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
noncomputable def ETC.fixedProductArgmaxCommit
noncomputable def ETC.fixedProductArgmaxAction
noncomputable def ETC.fixedProductMaxGapLintegralRegretBound

theorem ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean
```

Status: project-local compiled fixed product-coordinate wrapper.

This wrapper names the argmax-commit action trace and max-gap RHS budget, then
reuses the compiled max-gap infinitePi lower-integral theorem.  It is still
fixed-product/fixed-exploration and does not introduce Bochner expectation,
filtration, conditional concentration, or final adaptive ETC theorem assembly.

## Compiled Canonical Exploration Fixed-Product Bochner Endpoint

`ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET` is now compiled locally
in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.

```lean
noncomputable def ETC.explorationArgmaxCommit
noncomputable def ETC.explorationArgmaxAction
noncomputable def ETC.explorationMaxGapIntegralRegretBoundReal

theorem ETC.integral_real_pseudoRegret_explorationArgmaxAction_le_explorationMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_exploreMean
```

Status: project-local compiled fixed-product Bochner/Real expected-regret
endpoint.

The wrapper exposes only round-robin `ETC.exploreArm` in its coordinate a.s.
bounds and mean identities.  It fixes `model.bestArm` internally solely to
reuse the existing base-commit surface, justified by
`ETC.actionWithCommit_eq_exploreArm_of_lt` on the exploration horizon.  It
does not construct an adaptive action-dependent reward law, conditional reward
transport, or the final LML ETC theorem.

## Compiled Exploration Empirical-Mean Prefix Congruence

`ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` is now compiled locally in
`BanditRLProof.Algorithms.ETCEmpiricalMean` as
`ETC.empMeanAtExploration_eq_of_eq_on_prefix`. It transports equality of
reward coordinates on the strict horizon `t < spec.explorationPulls * K` to
equality of every exploration empirical-mean coordinate. The proof uses the
finite `sumRewards` filter/range representation and `Finset.sum_congr` only.
It is a deterministic prerequisite for a future finite reward-history commit
policy; no tail bound, probability law, policy equality, filtration, or
conditional expectation is proved here.

Failure policy: apply this lemma only after the proposed history completion is
proved equal to the ambient reward trace at every exploration coordinate. Do
not treat a finite history at an earlier time as sufficient, or identify this
support lemma with the adaptive ETC theorem.

## Compiled Finite-History Score Reconstruction

`ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` is now compiled through
`History.completeRewardTrace` and
`ETC.empMeanAtExploration_completeRewardTrace_eq_of_explorationHorizon_le`.
The completion reads a finite history through `t` and uses zero afterward. If
`spec.explorationPulls * K <= t + 1`, every coordinate needed by the exploration
score is inside that history, so the completed trace and ambient trace have
equal score at every arm. This is deliberately a score-level fact: it does not
yet show that a finite-history policy chooses the matching argmax, nor that a
generated trace equals `ETC.actionWithCommit`.

Failure policy: retain the horizon inclusion exactly. The zero-filled suffix is
not an assumption about actual rewards and cannot justify reward-law transport.

## Compiled Generated Finite-History ETC Policy Alignment

`ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` is now compiled in
`BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy`. It defines a measurable
policy over `RewardTrace Rat`: successor action `t + 1` uses round-robin
exploration inside the prefix and otherwise applies the finite score-vector
argmax to the zero-completed reward history. The theorem
`ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction` proves
function-level equality with the canonical empirical-mean ETC action generator
under `0 < spec.explorationPulls`.

The positive-pulls contract is essential only for time zero, whose generated
default action is `ETC.exploreArm spec 0`. Later commit-time equality is
obtained from `spec.explorationPulls * K <= t + 1` and finite-history score
reconstruction. No reward kernel, selected reward law, conditional expectation,
or concentration conclusion is obtained.

Failure policy: do not call this an adaptive bandit environment. The next route
must identify an action-dependent selected reward law for this generated trace;
the current fixed product-coordinate law is not automatically such a law.

## Compiled Canonical Generated ETC Trajectory Law

`ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` is now compiled as
`ETC.explorationArgmaxGeneratedActionPartialTrajectoryPairLawSource_trajMeasure`.
It instantiates the existing `RewardKernel.historyStepKernelFamily`
canonical-trajectory construction at the finite-history ETC policy and packages
the full generated finite-pair `partialTraj` law. This is a real
action-dependent `condExpKernel` law under the Markov-kernel trajectory
measure, not merely a source hypothesis.

Failure policy: its probability space is the canonical kernel trajectory.
Do not identify it with the current independent product-coordinate reward law,
or with an arbitrary adaptive finite-bandit environment, without a separate
measure/kernel transport theorem and model regularity identification.

## Compiled Model-Mean Conditional MGF On Canonical ETC Trajectory

`ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` is now compiled
as `ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure`.
It specializes the canonical trajectory MGF theorem to the context-independent
mean `fun _ arm => model.mean arm`. A centered reward-kernel law supplies the
one-step centered MGF, and a variance ceiling keyed to the selected finite
reward history supplies the requested proxy.

Failure policy: this is not a derivation of the kernel law, the variance
ceiling, product-coordinate independence, or a wrong-commit probability bound.
Those contracts must be constructed and transported before applying the
existing finite-sum concentration and regret assemblies.

## Compiled Finite-Arm Laws To Markov Reward Kernel

`ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` is now compiled as
`RewardKernel.contextIndependentOfActionLaws` with selected-measure theorem
`RewardKernel.selectedMeasure_contextIndependentOfActionLaws`. The constructor
uses Mathlib `Kernel.ofFunOfCountable` on action-indexed laws and
`Kernel.comap Prod.snd`, requiring measurable singletons, countable actions,
and an `IsProbabilityMeasure` witness for every action. For `Fin K`, this
provides the raw finite-bandit reward kernel expected by the canonical ETC
trajectory route.

Failure policy: selected-measure equality alone does not prove that the arm law
has `model.mean`, bounded support, a centered MGF, or the requested variance
proxy. It also does not identify the resulting trajectory with the fixed
product-coordinate source.

## Compiled Bounded Arm Laws To Canonical Conditional MGF

`ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` is compiled in
`BanditRLProof.Algorithms.ETCFiniteArmRewardLaw`. The declaration
`ETC.finiteArmBoundedCenteredRewardKernelLaw` packages bounded integrability,
exact centered integral zero, and Mathlib's bounded Hoeffding MGF into the
context-independent centered kernel law. The direct theorem
`ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws`
feeds that law into the canonical generated-history trajectory and discharges
the selected-history variance ceiling because the common interval gives a
constant proxy.

Failure policy: this is a one-step conditional MGF under canonical
`trajMeasure` for successor coordinates. It does not align arbitrary `mu0`
with the time-zero selected arm or prove its unconditional MGF, and it is not
the conditional sum tail, finite-arm wrong-commit union bound, product-source
identification, or expected-regret theorem.

## Compiled Full Canonical Centered-Reward Sum Tail

`ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL` is compiled as
`ETC.explorationArgmaxHistory_centeredRewardProcess_sum_tail_ennreal_of_boundedArmLaws`.
The initial law is the law of `ETC.exploreArm spec 0`, and
`RewardKernel.trajMeasure_map_eval_zero` transfers its bounded centered MGF to
the actual zeroth trajectory coordinate. Together with the successor
conditional MGF witnesses and generated-history StronglyAdapted process, this
gives Mathlib's one-sided Azuma-Hoeffding bound for all terms in
`Finset.range n`.

Failure policy: the event is a total selected-reward sum. Wrong commit is an
arm-specific empirical-mean comparison, requiring masked or pairwise centered
processes and an event adapter before the existing finite-arm union bound can
be used. No product/arbitrary-law transport or expected regret follows here.

## Compiled Canonical Bounded-Arm Pairwise Wrong-Commit Bound

`ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now supplies the previously
missing pairwise endpoint under the canonical generated-history trajectory.
The key bridge is finite-prefix rather than global: for every time before
`spec.explorationPulls * K`,
`ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt` identifies the
generated policy action with the fixed round-robin action. Consequently
`History.historyFiltrationSucc_eq_of_action_eq_on_prefix` identifies the two
conditioning sigma-algebras used by the canonical selected-reward MGF and the
existing fixed-commit centered-diff witness package.

Because `HasCondSubgaussianMGF` depends on the proof that the conditioning
space is below the ambient space, ordinary rewriting is insufficient. The
generic compiled adapter
`ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq` performs this
dependent transport. The bounded arm laws then construct
`ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_boundedArmLaws`,
which feeds the existing centered-diff tail contract and yields
`ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws`.

Concentration ledger: the summand is the fixed-exploration masked centered
reward for a non-best arm plus the sign-flipped masked centered reward for the
best arm; the filtration is generated finite action/reward history; the proxy
is the masked common interval proxy; the event is one-sided at the fixed
exploration horizon and then union-bounded over non-best arms.

Failure policy: do not extend the prefix equality past commitment, and do not
claim an external environment law or expected regret from this probability
bound alone. The downstream canonical Bochner leaf now performs the conversion
and expected-regret assembly; external law transport remains separate.

## Compiled Canonical Bounded-Arm Bochner Regret

`ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` packages the pairwise tail as
`ETC.canonicalBoundedArmWrongCommitTailBudget` and its Real view, then proves
`ETC.real_measure_explorationArgmaxCommit_ne_bestArm_le_canonicalBoundedArmWrongCommitTailBudgetReal`.
Finiteness follows definitionally from the finite sum of `ENNReal.ofReal`
exponentials, allowing `ENNReal.toReal_mono` to convert the probability bound.

The final local endpoint
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal`
uses coordinatewise empirical-mean measurability to obtain a measurable argmax
commit and wrong event, then reuses the finite-valued integrability and generic
Bochner exploration/suffix assembly. The suffix is charged by `model.maxGap`.

Failure policy: the expected-regret theorem is under the canonical
`RewardKernel.historyStepKernelFamily` trajectory measure initialized by the
first exploration arm law. An external adaptive bandit environment must provide
an equality of trajectory laws or finite-horizon pushforward identities before
this integral can be transported. Do not identify the measures from matching
one-step arm laws alone, and do not claim the LML theorem until its model,
regret, horizon, and constant conventions are explicitly mapped.

## Compiled External Exploration-Prefix Law Transport

`ETC.explorationArgmaxPrefixRegretReal` and its measurability/factorization
theorems show that finite-horizon generated ETC pseudo-regret depends only on
the reward prefix through `spec.explorationPulls * K - 1`. Consequently,
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq`
transports the canonical bound to an arbitrary external reward-trace
probability law from equality of those finite-prefix pushforwards. No suffix
reward law or full infinite-trajectory equality is assumed.

Proof route: measurable completed-prefix regret, exploration-score
reconstruction, generated/canonical action equality, two applications of
`MeasureTheory.integral_map`, then the canonical theorem. Regularity contracts:
positive exploration pulls, external probability, finite-prefix pushforward
equality, and the existing common-bounded exact-mean arm-law inputs.

The downstream theorem
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_condDistrib`
now discharges the prefix equality from an external initial marginal and the
successor `condDistrib` laws through exploration. Its generic source is
`RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib`, proved by
joint-law induction through Mathlib `compProd` and `trajMeasure` recurrence.

Regularities are coordinate measurability, probability/finite measures,
standard Borel reward target for the generic theorem, bounded exact-mean Rat
arm laws and measurable context for ETC, and positive exploration pulls. The
conditional laws are required only for `i < m*K-1`; no suffix law, full
trajectory equality, or independence is assumed.

Failure policy: a concrete environment still has to prove these conditional
identities; one-step marginal equality alone is insufficient. The scheduled
exploration-arm adapter below removes local kernel plumbing, while a concrete
source or `IsAlgEnvSeq` bridge remains required. The exact LML theorem is
strictly stronger in interface and conclusion: it uses Real stationary arm
kernels with a common sub-Gaussian proxy, upstream measurable-argmax semantics,
and per-arm gap-weighted pull-count bounds. Do not relabel the bounded Rat
max-gap union theorem as that port.

## Compiled Scheduled Exploration-Arm Conditional-Law Adapter

`ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt` proves
that, under `i+1 < explorationPulls*K`, the generated-history reward step
kernel is exactly `armLaw (ETC.exploreArm spec (i+1))`. Consequently,
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib`
states the external regret endpoint using only the initial exploration-arm law
and scheduled exploration-arm conditional laws.

Proof route: unfold `explorationArgmaxHistoryPolicy` on its deterministic
exploration branch, then unfold `historyStepKernelFamily` and the selected
measure of `contextIndependentOfActionLaws`; transport the external a.e.
arm-law equality to the previous step-kernel theorem. The public endpoint
instantiates the irrelevant context as `Unit`, so context/state/policy kernels
and `trajMeasure` no longer appear in the caller signature.

Failure policy: this theorem does not manufacture conditional laws from
unconditional marginals. A concrete source or LML `IsAlgEnvSeq` bridge must
prove the scheduled-arm `condDistrib` identities. Exact LML Real/sub-Gaussian,
argmax, and per-arm RHS alignment remains independent.

## Compiled Full Action/Reward-History Conditional-Law Transport

`RewardKernel.condDistrib_ae_eq_const_of_comp` proves that a constant target
law conditioned on a fine variable remains constant after measurable
projection to a coarser variable. Its proof maps the defining product joint law
with `Measure.map_prod_map`; injectivity is unnecessary. The companion
`RewardKernel.map_eq_of_condDistrib_ae_eq_const` recovers the target marginal
through `Measure.snd`.

`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib`
uses these results for reward zero conditioned on action zero and for reward
`i+1` conditioned on `(finitePairHistoryOfTrace action reward i, action (i+1))`.
This is the conditioning shape of LML `IsAlgEnvSeq` feedback fields at seed
`19dc3ab`, but the local assumption is already the constant scheduled-arm law.

Failure policy: LML `stationaryEnv` first yields a feedback kernel depending on
the next action, while `ETC.arm_of_lt` supplies only an a.e. constant action in
exploration. The remaining seed adapter must combine those facts before this
consumer applies; the dependency-light version is compiled immediately below.
Do not describe the current theorem as a direct LML import.

## Compiled Action-Dependent Feedback-Kernel Adapter

`RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected` pushes an a.e.
selector identity from the source measure to the conditioning-variable law and
rewrites a pointwise selected kernel as a constant kernel. The ETC theorem
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib`
instantiates this with `id` at action zero and `Prod.snd` at successor full
histories, then consumes the constant-law full-history endpoint.

This closes the dependency-light mathematical analogue of the exact-seed
`IsAlgEnvSeq` law transport. A direct LML wrapper would only translate
`HasCondDistrib` and `ETC.arm_of_lt`; it is not needed by the local bounded Rat
theorem. Failure policy now moves to the independent Real/common-sub-Gaussian,
argmax, and per-arm RHS layers.

## Failure Policy

- Do not start broad Hoeffding, martingale, kernel, or final ETC theorem work
  from this card.
- The local two-agent review workflow replaces the Extended Pro gate for
  current route decisions.
- `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` and
  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` are compiled locally.
- `TAIL-SUBGAUSS-SUM`, `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`,
  `TAIL-COND-SUBGAUSS`, `MEAS-HISTORY`, `FILTRATION-HISTORY`,
  `KERNEL-POLICY-BIND`, and `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` are
  compiled locally.
- `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT`,
  `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`, and
  `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` are compiled locally.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL`,
  `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND`,
  `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS`,
  `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS`, and
  `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND`,
  `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE`, and
  `ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE`, and
  `ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE`, and
  `ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE`, and
  `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND`,
  `ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND`,
  `ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND`, and
  `ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT`,
  `ETC-BOUNDED-REWARD-INFINITEPI-SOURCE`, and
  `ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE`, and
  `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND`, and
  `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE`, and
  `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY`, and
  `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY`,
  `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER`,
  `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY`,
  `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER`,
  `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY`, and
  `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` are compiled locally.
  The later native Real exact route now compiles through finite-prefix law and
  scheduled initial/successor `condDistrib` transport in
  `ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET`. This older design branch
  remains retrieval evidence only. Do not reopen its bounded/lower-integral
  route; the source-shaped history-score wrapper and faithful local LML-field
  theorem now compile, leaving only actual cross-toolchain symbol import.

## Compiled Per-Arm Expected-Regret Assembly

`ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob`
now preserves the suffix as `sum_a (r * gap a) * P(commit=a)`. The proof uses
measurable singleton fibers of the finite commit selector, the local Bochner
finite-sum wrapper, and Mathlib indicator integrals. This closes the generic
expectation-assembly half of the per-arm RHS mismatch.

The sharper probability leaf is now compiled: for each non-best `a`,
`P(explorationArgmaxCommit = a) <= pairwiseTail a` under the canonical bounded-
arm trajectory. It follows from the concrete argmax fiber inclusion and the
matching `PairwiseEmpMeanTailContract.bound a`, with no union. Its finite Real
conversion and termwise gap-weighted substitution now compile as
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal`.
The proof uses gap nonnegativity for non-best arms and `gap_bestArm` to remove
the unconstrained best-arm term. The per-arm integral now also transports
through exploration-prefix pushforward equality via
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq`.
This needs neither full trajectory nor suffix/fiber law equality. The per-arm
conditional-law consumer derives the prefix identity from initial and
successor `condDistrib` laws and pulls the mapped reward integral back to the
original sample space. Its stationary scheduled exploration-arm adapter now
also compiles, with no caller-visible local kernel. The full action/reward-
history constant-law per-arm adapter now compiles through generic coarsening
and marginal extraction. Its action-dependent selected-kernel counterpart now
also compiles, closing the dependency-light bounded-Rat law route. Direct
common-proxy arm MGFs now compile through the canonical pairwise empirical-mean
tail contract without bounded support. Concrete commit-fiber bounds, finite
Real tails, and the canonical gap-weighted per-arm Bochner theorem now compile
as well. Its external exploration-prefix equality, generic initial/successor
conditional-law, scheduled exploration-arm, and LML-shaped full action/reward-
history constant-law transport and its action-dependent selected-kernel
consumer now also compile, closing dependency-light direct-MGF `Rat` law
transport. The subsequent native Real product, exact regret, finite-prefix,
selected conditional-law, least-encoded tie, and action assembly endpoints also
compile. Upstream history empirical-mean equality and the local `IsAlgEnvSeq`-
field consumer now compile as well. Only direct import over the actual LML
symbols remains; do not return to a max-gap union or another concentration
theorem.
