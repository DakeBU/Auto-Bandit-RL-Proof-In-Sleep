import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import BanditRLProof.Algorithms.ETCTraceCountLemmas
import BanditRLProof.MeasurablePullCountCast

/-!
# ETC expected pull counts

This module integrates the deterministic pull-count formula for an
`Omega`-indexed ETC commit selector.  It isolates the exact interface between
ETC counting and concentration: a later tail argument only has to bound the
commit-fiber probability `mu.real {omega | commit omega = a}`.
-/

universe u

open MeasureTheory

namespace BanditRLProof
namespace ETC

/--
The Real cast of a finite-horizon ETC pull count is integrable when the commit
selector is measurable and the ambient measure is finite.

This regularity adapter is independent of reward laws and concentration.  Its
proof uses timewise measurability of the finite-valued ETC action and the
deterministic bound `pullCount <= n`.
-/
theorem integrable_real_pullCount_actionWithCommit_choice_of_measurable_commit
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K) (commit : Omega -> Fin K)
    (a : Fin K) (n : Nat)
    (hmeas_commit : Measurable commit) :
    Integrable
      (fun omega : Omega =>
        ((pullCount (ETC.actionWithCommit spec (commit omega)) a n : Nat) :
          Real)) mu := by
  let action : Omega -> ActionTrace (Fin K) :=
    fun omega => ETC.actionWithCommit spec (commit omega)
  have haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t) := by
    intro t
    exact
      (measurable_of_countable
        (fun commitArm : Fin K => ETC.actionWithCommit spec commitArm t)).comp
        hmeas_commit
  have hmeas :
      Measurable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) :=
    measurable_natCast_pullCount action haction a n
  refine MeasureTheory.Integrable.of_bound
    hmeas.aestronglyMeasurable (n : Real) ?_
  filter_upwards [] with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast pullCount_le_time (action omega) a n

/--
At horizon `spec.explorationPulls * K + r`, the expected Real pull count of arm
`a` is exactly the exploration count plus `r` times the probability of
committing to `a`.

This is the direct Bochner/indicator integration of
`ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`.
-/
theorem integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_suffix_mul_commit_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (commit : Omega -> Fin K)
    (a : Fin K) (r : Nat)
    (hmeas_commit : Measurable commit) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pullCount (ETC.actionWithCommit spec (commit omega)) a
          (spec.explorationPulls * K + r) : Nat) : Real)) =
    (spec.explorationPulls : Real) +
      (r : Real) * mu.real {omega : Omega | commit omega = a} := by
  let commitSet : Set Omega := {omega : Omega | commit omega = a}
  let suffix : Omega -> Real :=
    commitSet.indicator (fun _omega : Omega => (r : Real))
  have hcommitSet : MeasurableSet commitSet := by
    change MeasurableSet (commit ⁻¹' {a})
    exact hmeas_commit (measurableSet_singleton a)
  have hsuffix : Integrable suffix mu :=
    (integrable_const (r : Real)).indicator hcommitSet
  have hpoint :
      (fun omega : Omega =>
        ((pullCount (ETC.actionWithCommit spec (commit omega)) a
          (spec.explorationPulls * K + r) : Nat) : Real)) =
      (fun omega : Omega => (spec.explorationPulls : Real) + suffix omega) := by
    funext omega
    rw [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq]
    by_cases h : commit omega = a
    · simp [suffix, commitSet, h]
    · simp [suffix, commitSet, h]
  rw [hpoint]
  rw [MeasureTheory.integral_add (integrable_const _) hsuffix]
  rw [MeasureTheory.integral_const]
  rw [show suffix = commitSet.indicator
      (fun _omega : Omega => (r : Real)) by rfl]
  rw [MeasureTheory.integral_indicator hcommitSet]
  rw [MeasureTheory.setIntegral_const]
  simp [commitSet, MeasureTheory.probReal_univ, smul_eq_mul, mul_comm]

/--
LML-shaped horizon form of the exact ETC expected pull-count identity.

The exploration condition is written as `K * explorationPulls <= n`, and the
suffix is `n - K * explorationPulls`, matching the exact ETC theorem-card
surface.  No concentration or reward-law assumption is used.
-/
theorem integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_remaining_mul_commit_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (commit : Omega -> Fin K)
    (a : Fin K) (n : Nat)
    (hn : K * spec.explorationPulls <= n)
    (hmeas_commit : Measurable commit) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pullCount (ETC.actionWithCommit spec (commit omega)) a n : Nat) :
          Real)) =
    (spec.explorationPulls : Real) +
      ((n - K * spec.explorationPulls : Nat) : Real) *
        mu.real {omega : Omega | commit omega = a} := by
  have hsplit :
      spec.explorationPulls * K + (n - K * spec.explorationPulls) = n := by
    rw [Nat.mul_comm spec.explorationPulls K]
    exact Nat.add_sub_of_le hn
  calc
    MeasureTheory.integral mu
        (fun omega : Omega =>
          ((pullCount (ETC.actionWithCommit spec (commit omega)) a n : Nat) :
            Real)) =
      MeasureTheory.integral mu
        (fun omega : Omega =>
          ((pullCount (ETC.actionWithCommit spec (commit omega)) a
            (spec.explorationPulls * K +
              (n - K * spec.explorationPulls)) : Nat) : Real)) := by
        congr 1
        funext omega
        rw [hsplit]
    _ = (spec.explorationPulls : Real) +
        ((n - K * spec.explorationPulls : Nat) : Real) *
          mu.real {omega : Omega | commit omega = a} := by
      exact
        integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_suffix_mul_commit_prob
          mu spec commit a (n - K * spec.explorationPulls) hmeas_commit

/--
Per-arm ETC expected pull-count bound from a commit-fiber probability bound.

This is the concentration consumer needed by the exact LML route: a later
empirical-mean tail theorem supplies only
`mu.real {omega | commit omega = a} <= p`; the counting and integration steps
are discharged here.
-/
theorem integral_real_pullCount_actionWithCommit_choice_le_exploration_add_remaining_mul_of_commit_prob_le
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (commit : Omega -> Fin K)
    (a : Fin K) (n : Nat) (p : Real)
    (hn : K * spec.explorationPulls <= n)
    (hmeas_commit : Measurable commit)
    (hprob : mu.real {omega : Omega | commit omega = a} <= p) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pullCount (ETC.actionWithCommit spec (commit omega)) a n : Nat) :
          Real)) <=
    (spec.explorationPulls : Real) +
      ((n - K * spec.explorationPulls : Nat) : Real) * p := by
  rw [integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_remaining_mul_commit_prob
    mu spec commit a n hn hmeas_commit]
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hprob (Nat.cast_nonneg _))

end ETC
end BanditRLProof
