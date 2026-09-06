import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.OuterMeasure.Basic
import BanditRLProof.Core
import BanditRLProof.Algorithms.ETC

/-!
# ETC measurability canaries

This module starts the probability-facing ETC layer with event measurability.
It deliberately avoids measures, probability inequalities, empirical means,
filtrations, concentration, and final regret theorems.
-/

universe u

open MeasureTheory

namespace BanditRLProof
namespace ETC

/--
If the commit arm is measurable, then the event that it is not the selected
best arm is measurable.

This is the first wrong-commit event canary after the deterministic fixed-commit
ETC layer.  It is intentionally only an event measurability fact.
-/
theorem measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False} := by
  have hEq : MeasurableSet {omega : Omega | commitArm omega = model.bestArm} := by
    simpa [Set.preimage] using
      (hmeas_commit (MeasurableSet.singleton model.bestArm))
  simpa [Set.compl_setOf] using hEq.compl

/--
Coordinatewise empirical-mean measurability packages into measurability of the
empirical-mean score vector.

This is the `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` project-local leaf
selected by the Extended Pro review after
`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE`. It is a direct producer for
`measurable_commitOracle_choose_of_measurable_empMeanVector`; it does not
construct an oracle, prove argmax correctness, add concentration, or introduce
filtration.
-/
theorem measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) := by
  exact measurable_pi_lambda _ hmeas_coord

/--
An abstract commit oracle has a measurable composed choice map whenever the
empirical-mean score vector is measurable and the finite-score-vector domain is
countable with measurable singletons.

This is the compiled candidate identified by the
`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD`. It discharges the direct
`hmeas_choose` contract used by `measurableSet_commitOracle_ne_bestArm` for the
current `Rat` score-vector surface. It does not construct a concrete argmax
oracle, prove argmax correctness, introduce concentration, or use filtration.
-/
theorem measurable_commitOracle_choose_of_measurable_empMeanVector
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
    Measurable (fun omega : Omega => oracle.choose (empMean omega)) := by
  have hchoose :
      Measurable (fun score : Fin K -> Rat => oracle.choose score) := by
    exact measurable_of_countable _
  exact hchoose.comp hmeas_emp

/--
Coordinatewise empirical-mean measurability is enough to make an abstract
commit oracle's composed choice map measurable.

This is the `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`
project-local leaf selected after
`ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`. It composes the Mathlib Pi-space
empirical-mean vector bridge with the countable score-vector oracle-choice
bridge. It does not construct a concrete oracle, prove argmax correctness,
introduce probability, or use concentration/filtration facts.
-/
theorem measurable_commitOracle_choose_of_forall_measurable_empMean
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
    Measurable (fun omega : Omega => oracle.choose (empMean omega)) := by
  have hvec :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) :=
    ETC.measurable_empMeanVector_of_forall_measurable
      (empMean := empMean) hmeas_coord
  exact
    ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
      (oracle := oracle)
      (empMean := empMean)
      hvec

/--
If an abstract commit oracle's composed choice map is measurable, then the
event that the oracle-selected arm is not the selected best arm is measurable.

This is the `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` project-local leaf.
It deliberately assumes measurability of the composed oracle choice directly,
so it does not construct a concrete argmax oracle, prove oracle measurability
from empirical means, add probability assumptions, or introduce concentration
and filtration obligations.
-/
theorem measurableSet_commitOracle_ne_bestArm
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
        oracle.choose (empMean omega) = model.bestArm -> False} := by
  simpa using
    (ETC.measurableSet_commitArm_ne_bestArm
      (model := model)
      (commitArm := fun omega : Omega => oracle.choose (empMean omega))
      (hmeas_commit := hmeas_choose))

/--
Coordinatewise empirical-mean measurability is enough to make the
oracle-selected wrong-commit event measurable.

This is the
`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`
project-local leaf. It composes the coordinatewise oracle-choice measurability
wrapper with the oracle-selected wrong-event measurability wrapper. It does
not construct a concrete oracle, prove argmax correctness, introduce a
probability measure, or use concentration/filtration facts.
-/
theorem measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
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
        oracle.choose (empMean omega) = model.bestArm -> False} := by
  have hchoose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega)) :=
    ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
      (oracle := oracle)
      (empMean := empMean)
      hmeas_coord
  exact
    ETC.measurableSet_commitOracle_ne_bestArm
      (model := model)
      (oracle := oracle)
      (empMean := empMean)
      hchoose

/--
Pairwise empirical-mean comparison events are measurable when each empirical
mean coordinate is measurable.

This is an ordered-event regularity canary for the wrong-mean event.  It does
not use measures, probability, commit-arm argmax, finite unions, concentration,
or filtration assumptions.
-/
theorem measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b} := by
  change MeasurableSet {omega : Omega | empMean omega b <= empMean omega a}
  exact measurableSet_le (hmeas_empMean b) (hmeas_empMean a)

/--
The finite existential wrong-mean event is measurable when each empirical mean
coordinate is measurable.

This packages the pairwise empirical-mean comparison canary into the exact
finite event shape used by the wrong-commit probability bridge.  It does not
use measures, probability, commit-arm argmax, concentration, filtration, or an
empirical-mean construction.
-/
theorem measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} := by
  classical
  have hset :
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
      =
      (⋃ a ∈ (Finset.univ : Finset (Fin K)),
        {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}) := by
    ext omega
    simp
  rw [hset]
  refine Finset.measurableSet_biUnion _ ?_
  intro a _ha
  by_cases h : a = model.bestArm
  · have hempty :
        {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
        = (∅ : Set Omega) := by
        ext omega
        simp [h]
    rw [hempty]
    exact MeasurableSet.empty
  · have hpair :
        MeasurableSet {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} :=
        measurableSet_empMean_ge_empMean
          empMean hmeas_empMean a model.bestArm
    simpa [h] using hpair

/--
The wrong-commit event is contained in the event that some non-best arm's
empirical mean beats or ties the selected best arm's empirical mean, assuming
the commit arm is an empirical-mean argmax.

This is a pure event-reduction leaf: no measurability, measure, probability, or
concentration assumptions are used.
-/
theorem wrong_commit_subset_exists_empMean_ge_bestArm
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
          empMean omega a >= empMean omega model.bestArm} := by
  intro omega hwrong
  refine Exists.intro (commitArm omega) ?_
  exact And.intro hwrong (by
    change empMean omega model.bestArm <= empMean omega (commitArm omega)
    exact hcommit_argmax omega model.bestArm)

/--
A commit oracle with an explicit argmax certificate satisfies the deterministic
wrong-commit event reduction when used as the commit-arm selector.

This is the `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` project-local leaf. It consumes
only the oracle's abstract argmax contract and the compiled set-inclusion
event reduction; it does not prove oracle optimality, oracle measurability,
concentration, filtration, or final ETC regret.
-/
theorem wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
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
          empMean omega a >= empMean omega model.bestArm} := by
  exact
    ETC.wrong_commit_subset_exists_empMean_ge_bestArm
      model
      (fun omega : Omega => oracle.choose (empMean omega))
      empMean
      (by
        intro omega a
        exact hchoose_argmax (empMean omega) a)

/--
The measure of the wrong-commit event is bounded by the measure of the
empirical wrong-mean event, using only the compiled set inclusion and measure
monotonicity.

This is a probability-facing wrapper leaf, but it does not require a probability
measure, event measurability, empirical-mean measurability, concentration, or
filtration assumptions.
-/
theorem prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
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
        empMean omega a >= empMean omega model.bestArm} := by
  exact mu.mono
    (wrong_commit_subset_exists_empMean_ge_bestArm
      model commitArm empMean hcommit_argmax)

/--
The finite existential wrong-mean event is bounded by the finite sum of its
guarded pairwise arm events.

This is an outer-measure finite-union wrapper.  It intentionally does not
require event measurability, a probability measure, empirical-mean
measurability, commit-arm argmax, concentration, filtration, or an
empirical-mean construction.
-/
theorem prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
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
          empMean omega a >= empMean omega model.bestArm}) := by
  classical
  let E : Fin K -> Set Omega := fun a =>
    {omega : Omega | (a = model.bestArm -> False) /\
      empMean omega a >= empMean omega model.bestArm}
  have hset :
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
      =
      (⋃ a ∈ (Finset.univ : Finset (Fin K)), E a) := by
    ext omega
    simp [E]
  rw [hset]
  simpa [E] using
    (MeasureTheory.measure_biUnion_finset_le
      (μ := mu)
      (I := (Finset.univ : Finset (Fin K)))
      (s := E))

/--
The wrong-commit event is bounded by the finite sum of guarded pairwise
wrong-mean event measures.

This is the terminal elementary probability assembly for the wrong-commit
event reduction.  It composes the compiled set-inclusion measure wrapper with
the compiled finite-union probability wrapper, without adding empirical-mean
construction, concentration, filtration, or final regret assumptions.
-/
theorem prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
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
          empMean omega a >= empMean omega model.bestArm}) := by
  exact le_trans
    (prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
      mu model commitArm empMean hcommit_argmax)
    (prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
      mu model empMean)

/--
The wrong-commit event is bounded by a finite sum of abstract pairwise tail
bounds.

This keeps the current ETC probability layer free of concentration,
filtration, independence, and empirical-mean construction assumptions while
exposing the interface that future Hoeffding-style leaves can discharge.
-/
theorem prob_commitArm_ne_bestArm_le_sum_pairwise_tail
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
    (Finset.univ : Finset (Fin K)).sum tail := by
  calc
    mu {omega : Omega | commitArm omega = model.bestArm -> False}
        <=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            mu {omega : Omega | (a = model.bestArm -> False) /\
              empMean omega a >= empMean omega model.bestArm}) :=
        prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
          mu model commitArm empMean hcommit_argmax
    _ <=
        (Finset.univ : Finset (Fin K)).sum tail := by
      refine Finset.sum_le_sum ?_
      intro a _ha
      by_cases h : a = model.bestArm
      · have hempty :
            {omega : Omega | (a = model.bestArm -> False) /\
              empMean omega a >= empMean omega model.bestArm}
            = (∅ : Set Omega) := by
          ext omega
          simp [h]
        rw [hempty]
        simp
      · have hsubset :
            {omega : Omega | (a = model.bestArm -> False) /\
              empMean omega a >= empMean omega model.bestArm}
            ⊆
            {omega : Omega |
              empMean omega a >= empMean omega model.bestArm} := by
          intro omega homega
          exact homega.2
        exact le_trans (mu.mono hsubset) (hpair_tail a h)

/--
The oracle-selected wrong-commit event is bounded by a finite sum of abstract
pairwise tail bounds.

This is the `ETC-COMMIT-ORACLE-PROB-WRAPPER` project-local leaf. It
specializes the arbitrary-commit-arm pairwise-tail consumer to
`oracle.choose (empMean omega)` and derives the needed commit-arm argmax
contract from the abstract oracle certificate. It does not prove oracle
measurability, construct a concrete argmax oracle, prove concentration, add
filtration, or instantiate final ETC regret.
-/
theorem prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
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
    (Finset.univ : Finset (Fin K)).sum tail := by
  exact
    ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
      mu
      model
      (fun omega : Omega => oracle.choose (empMean omega))
      empMean
      tail
      (by
        intro omega a
        exact hchoose_argmax (empMean omega) a)
      hpair_tail

/--
The wrong-commit event is bounded by a finite sum of abstract pairwise tail
bounds with the selected best-arm summand forced to zero.

This is a sharper tail-consumer wrapper than
`prob_commitArm_ne_bestArm_le_sum_pairwise_tail`; it still avoids filtered-sum
normalization, empirical-mean construction, and concentration assumptions.
-/
theorem prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
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
      (fun a : Fin K => if a = model.bestArm then 0 else tail a) := by
  classical
  calc
    mu {omega : Omega | commitArm omega = model.bestArm -> False}
        <=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            mu {omega : Omega | (a = model.bestArm -> False) /\
              empMean omega a >= empMean omega model.bestArm}) :=
        prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
          mu model commitArm empMean hcommit_argmax
    _ <=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => if a = model.bestArm then 0 else tail a) := by
      refine Finset.sum_le_sum ?_
      intro a _ha
      by_cases h : a = model.bestArm
      · have hempty :
            {omega : Omega | (a = model.bestArm -> False) /\
              empMean omega a >= empMean omega model.bestArm}
            = (∅ : Set Omega) := by
          ext omega
          simp [h]
        rw [hempty]
        simp [h]
      · have hguard_le :
            mu {omega : Omega | (a = model.bestArm -> False) /\
              empMean omega a >= empMean omega model.bestArm} <= tail a := by
          have hsubset :
              {omega : Omega | (a = model.bestArm -> False) /\
                empMean omega a >= empMean omega model.bestArm}
              ⊆
              {omega : Omega |
                empMean omega a >= empMean omega model.bestArm} := by
            intro omega homega
            exact homega.2
          exact le_trans (mu.mono hsubset) (hpair_tail a h)
        simpa [h] using hguard_le

/--
The wrong-commit event is bounded by the filtered finite sum of abstract
non-best pairwise tail bounds.

This is a presentation-normalization wrapper around
`prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`: it replaces the
if-zeroed `Finset.univ` sum by an explicit filtered sum over non-best arms.
-/
theorem prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
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
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  classical
  have hbound :
      mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => if a = model.bestArm then 0 else tail a) :=
    prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
      mu model commitArm empMean tail hcommit_argmax hpair_tail
  have hsum :
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => if a = model.bestArm then 0 else tail a)
      =
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases h : a = model.bestArm
    · simp [h]
    · simp [h]
  simpa [hsum] using hbound

/--
The oracle-selected wrong-commit event is bounded by the filtered finite sum
of abstract non-best pairwise tail bounds.

This is the `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` project-local leaf.
It specializes the arbitrary-commit-arm filtered probability consumer to
`oracle.choose (empMean omega)` and derives the needed commit-arm argmax
contract from the abstract oracle certificate. It does not add oracle
measurability, a concrete argmax oracle, concentration, filtration, or final
ETC regret.
-/
theorem prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
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
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact
    ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
      mu
      model
      (fun omega : Omega => oracle.choose (empMean omega))
      empMean
      tail
      (by
        intro omega a
        exact hchoose_argmax (empMean omega) a)
      hpair_tail

/--
The oracle-selected wrong-commit event is bounded by the if-zeroed finite sum
of abstract non-best pairwise tail bounds.

This is the `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` project-local leaf. It
specializes the arbitrary-commit-arm if-zeroed probability consumer to
`oracle.choose (empMean omega)` and derives the needed commit-arm argmax
contract from the abstract oracle certificate. It does not add oracle
measurability, a concrete argmax oracle, concentration, filtration, or final
ETC regret.
-/
theorem prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail
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
      (fun a : Fin K => if a = model.bestArm then 0 else tail a) := by
  exact
    ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
      mu
      model
      (fun omega : Omega => oracle.choose (empMean omega))
      empMean
      tail
      (by
        intro omega a
        exact hchoose_argmax (empMean omega) a)
      hpair_tail

end ETC
end BanditRLProof
