import BanditRLProof.MeasurableLocalQuantities
import BanditRLProof.Algorithms.ETCEmpiricalMean
import BanditRLProof.RatMeasurability

/-!
# ETC empirical-mean measurability support

This module starts wiring the deterministic fixed-commit ETC empirical-mean
surface to stochastic reward traces. It proves numerator measurability and the
first full empirical-mean measurability wrapper under an explicit
division-by-constant measurability contract, then discharges that contract
using the local Rat measurable-singleton wrapper, plus a coordinate-shaped
wrapper for downstream event measurability. Argmax wiring, concentration, and
filtration remain separate leaves.
-/

namespace BanditRLProof
namespace ETC

/--
The selected-reward numerator of the fixed-commit ETC empirical mean is
measurable for stochastic reward traces with timewise measurable coordinates.

This is the `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION`
project-local leaf.
-/
theorem measurable_sumRewards_actionWithCommit_exploration
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
        (spec.explorationPulls * K)) := by
  have haction : forall t : Nat,
      Measurable (fun omega : Omega =>
        (ETC.actionWithCommit spec commitArm) t) := by
    intro _t
    exact measurable_const
  simpa using
    (measurable_sumRewards
      (action := fun _ : Omega => ETC.actionWithCommit spec commitArm)
      (reward := reward)
      haction hreward a (spec.explorationPulls * K))

/--
The fixed-commit ETC empirical mean is measurable under stochastic reward
traces once measurability of division by a constant Rat is supplied.

This is the
`ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
project-local leaf. It deliberately leaves the Mathlib import/wrapper decision
for Rat division measurability to a later leaf.
-/
theorem measurable_empMeanAtExploration_of_measurable_div_const
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
      ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  have hnum : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K)) :=
    ETC.measurable_sumRewards_actionWithCommit_exploration
      spec commitArm a reward hreward
  have hdiv : Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K) /
        (pullCount (ETC.actionWithCommit spec commitArm) a
          (spec.explorationPulls * K) : Rat)) := by
    exact (hdiv_const _).comp hnum
  simpa [ETC.empMeanAtExploration] using hdiv

/--
The fixed-commit ETC empirical mean is measurable under stochastic reward
traces, using the local Rat division-by-constant measurability wrapper.

This is the `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION`
project-local leaf. It removes the explicit `hdiv_const` argument from
`measurable_empMeanAtExploration_of_measurable_div_const` by requiring
measurable singletons on `Rat`.
-/
theorem measurable_empMeanAtExploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  exact
    ETC.measurable_empMeanAtExploration_of_measurable_div_const
      spec commitArm a reward hreward measurable_rat_div_const

/--
The fixed-commit ETC empirical-mean coordinates are measurable under
stochastic reward traces.

This is the `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES`
project-local leaf. It packages `measurable_empMeanAtExploration` in the
`forall a : Fin K, Measurable ...` shape used by empirical-mean event
measurability lemmas; it does not add argmax, concentration, or filtration
contracts.
-/
theorem measurable_empMeanAtExploration_coordinates
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
          ETC.empMeanAtExploration spec commitArm (reward omega) b) a) := by
  intro a
  simpa using
    (ETC.measurable_empMeanAtExploration
      spec commitArm a reward hreward)

end ETC
end BanditRLProof
