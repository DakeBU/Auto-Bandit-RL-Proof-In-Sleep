import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Real
import BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly

/-!
# ETC lower-integral regret assembly

This module lifts the pointwise wrong-commit regret bridge to the project's
current expectation surface: an `ENNReal.ofReal` lower-integral surrogate.  It
does not introduce a Bochner/Rat-valued expected regret theorem, concentration,
filtrations, or a final ETC theorem.
-/

universe u

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof
namespace ETC

/--
Lower-integral assembly for an `Omega`-indexed ETC commit selector.

The theorem consumes a pointwise non-best gap bound and an abstract upper bound
`pWrong` on the wrong-commit event probability.  It is intentionally still an
`ENNReal.ofReal` lower-integral statement, matching the existing expectation
surface in the project.
-/
theorem lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat)
    (badGapBound : Rat) (pWrong : ENNReal)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (hmeas_wrong :
      MeasurableSet {omega : Omega | commit omega = model.bestArm -> False})
    (hprob_wrong :
      mu {omega : Omega | commit omega = model.bestArm -> False} <= pWrong) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec (commit omega))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * badGapBound : Rat) : Real))) * pWrong := by
  let wrongSet : Set Omega :=
    {omega : Omega | commit omega = model.bestArm -> False}
  let baseRat : Rat :=
    ((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat))
  let suffixRat : Omega -> Rat :=
    fun omega : Omega =>
      (((r : Nat) : Rat) *
        (if commit omega = model.bestArm then (0 : Rat) else badGapBound))
  let base : ENNReal :=
    ENNReal.ofReal (((baseRat : Rat) : Real))
  let suffix : ENNReal :=
    ENNReal.ofReal ((((((r : Nat) : Rat) * badGapBound : Rat) : Real)))
  have hpoint :
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec (commit omega))
              (spec.explorationPulls * K + r) : Rat) : Real)))
        <=
      (fun omega : Omega => base + wrongSet.indicator (fun _ => suffix) omega) := by
    intro omega
    have hrat :
        pseudoRegret model (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) <= baseRat + suffixRat omega := by
      simpa [baseRat, suffixRat] using
        ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap
          (spec := spec)
          (model := model)
          (commit := commit)
          (r := r)
          (badGapBound := badGapBound)
          (hbadGap := hbadGap)
          (omega := omega)
    have hreal :
        (((pseudoRegret model
            (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real)) <=
          (((baseRat + suffixRat omega : Rat) : Real)) := by
      exact_mod_cast hrat
    have hmain :
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec (commit omega))
              (spec.explorationPulls * K + r) : Rat) : Real)) <=
        ENNReal.ofReal (((baseRat + suffixRat omega : Rat) : Real)) :=
      ENNReal.ofReal_le_ofReal hreal
    have hadd :
        ENNReal.ofReal (((baseRat + suffixRat omega : Rat) : Real)) <=
        base +
          ENNReal.ofReal
            (((suffixRat omega : Rat) : Real)) := by
      simpa [base, Rat.cast_add] using
        (ENNReal.ofReal_add_le
          (p := (((baseRat : Rat) : Real)))
          (q := (((suffixRat omega : Rat) : Real))))
    have hsuffix :
        ENNReal.ofReal
          (((suffixRat omega : Rat) : Real)) <=
        wrongSet.indicator (fun _ => suffix) omega := by
      by_cases hcommit : commit omega = model.bestArm
      · simp [wrongSet, suffix, suffixRat, hcommit]
      · simp [wrongSet, suffix, suffixRat, hcommit]
    exact le_trans hmain (le_trans hadd (add_le_add (le_refl base) hsuffix))
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec (commit omega))
              (spec.explorationPulls * K + r) : Rat) : Real)))
        <=
      MeasureTheory.lintegral mu
        (fun omega : Omega => base + wrongSet.indicator (fun _ => suffix) omega) := by
          exact MeasureTheory.lintegral_mono hpoint
    _ =
      MeasureTheory.lintegral mu (fun _omega : Omega => base) +
      MeasureTheory.lintegral mu
        (fun omega : Omega => wrongSet.indicator (fun _ => suffix) omega) := by
          rw [MeasureTheory.lintegral_add_left measurable_const]
    _ = base * mu Set.univ + suffix * mu wrongSet := by
          rw [MeasureTheory.lintegral_const,
            MeasureTheory.lintegral_indicator_const
              (by simpa [wrongSet] using hmeas_wrong)]
    _ = base + suffix * mu wrongSet := by
          simp [base, suffix, MeasureTheory.IsProbabilityMeasure.measure_univ]
    _ <= base + suffix * pWrong := by
          exact
            add_le_add
              (le_refl base)
              (mul_le_mul_right
                (by simpa [wrongSet] using hprob_wrong)
                suffix)

/--
Bochner/Real expected-regret assembly for an `Omega`-indexed ETC commit
selector.

This is the Real-valued analogue of
`lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`.
It still consumes an abstract wrong-commit probability bound, but the
conclusion is an ordinary Bochner integral of the Real-cast pseudo-regret.
-/
theorem integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat)
    (badGapBound : Rat) (pWrong : Real)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (hbadGap_nonneg : (0 : Rat) <= badGapBound)
    (hmeas_wrong :
      MeasurableSet {omega : Omega | commit omega = model.bestArm -> False})
    (hprob_wrong :
      mu.real {omega : Omega | commit omega = model.bestArm -> False} <=
        pWrong)
    (hinteg : Integrable
      (fun omega : Omega =>
        (((pseudoRegret model (ETC.actionWithCommit spec (commit omega))
          (spec.explorationPulls * K + r) : Rat) : Real))) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ((((((r : Nat) : Rat) * badGapBound : Rat) : Real)) * pWrong) := by
  let wrongSet : Set Omega :=
    {omega : Omega | commit omega = model.bestArm -> False}
  let baseRat : Rat :=
    ((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat))
  let suffixRat : Omega -> Rat :=
    fun omega : Omega =>
      (((r : Nat) : Rat) *
        (if commit omega = model.bestArm then (0 : Rat) else badGapBound))
  let baseReal : Real := (((baseRat : Rat) : Real))
  let suffixReal : Real :=
    (((((r : Nat) : Rat) * badGapBound : Rat) : Real))
  let bound : Omega -> Real :=
    fun omega : Omega =>
      baseReal + wrongSet.indicator (fun _ => suffixReal) omega
  have hsuffix_nonneg : 0 <= suffixReal := by
    have hr_nonneg : (0 : Rat) <= (((r : Nat) : Rat)) := by
      exact_mod_cast Nat.zero_le r
    have hsuffix_rat_nonneg :
        (0 : Rat) <= (((r : Nat) : Rat) * badGapBound) :=
      mul_nonneg hr_nonneg hbadGap_nonneg
    have hsuffix_real_nonneg :
        (0 : Real) <=
          ((((r : Nat) : Rat) * badGapBound : Rat) : Real) := by
      exact_mod_cast hsuffix_rat_nonneg
    simpa [suffixReal] using hsuffix_real_nonneg
  have hpoint :
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <= bound := by
    intro omega
    have hrat :
        pseudoRegret model (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) <=
          baseRat + suffixRat omega := by
      simpa [baseRat, suffixRat] using
        ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap
          (spec := spec)
          (model := model)
          (commit := commit)
          (r := r)
          (badGapBound := badGapBound)
          (hbadGap := hbadGap)
          (omega := omega)
    have hreal :
        (((pseudoRegret model
            (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real)) <=
          (((baseRat + suffixRat omega : Rat) : Real)) := by
      exact_mod_cast hrat
    have hrhs :
        (((baseRat + suffixRat omega : Rat) : Real)) = bound omega := by
      by_cases hcommit : commit omega = model.bestArm
      · simp [bound, wrongSet, baseReal, suffixReal, suffixRat, hcommit,
          Rat.cast]
      · simp [bound, wrongSet, baseReal, suffixReal, suffixRat, hcommit,
          Rat.cast]
    simpa [hrhs]
      using hreal
  have hbound_integrable : Integrable bound mu := by
    have hconst : Integrable (fun _omega : Omega => baseReal) mu :=
      integrable_const baseReal
    have hsuffix :
        Integrable (wrongSet.indicator (fun _ : Omega => suffixReal)) mu :=
      (integrable_const suffixReal).indicator
        (by simpa [wrongSet] using hmeas_wrong)
    simpa [bound] using hconst.add hsuffix
  calc
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real)))
        <= MeasureTheory.integral mu bound := by
          exact MeasureTheory.integral_mono hinteg hbound_integrable hpoint
    _ =
        baseReal + suffixReal * mu.real wrongSet := by
          have hconst : Integrable (fun _omega : Omega => baseReal) mu :=
            integrable_const baseReal
          have hsuffix :
              Integrable
                (wrongSet.indicator (fun _ : Omega => suffixReal)) mu :=
            (integrable_const suffixReal).indicator
              (by simpa [wrongSet] using hmeas_wrong)
          rw [show bound =
              (fun omega : Omega =>
                (fun _omega : Omega => baseReal) omega +
                  wrongSet.indicator (fun _ : Omega => suffixReal) omega) by
                funext omega
                rfl]
          rw [MeasureTheory.integral_add hconst hsuffix]
          rw [MeasureTheory.integral_const]
          rw [MeasureTheory.integral_indicator
            (by simpa [wrongSet] using hmeas_wrong)]
          rw [MeasureTheory.setIntegral_const]
          simp [MeasureTheory.probReal_univ, mul_comm]
    _ <= baseReal + suffixReal * pWrong := by
          exact
            add_le_add
              (le_refl baseReal)
              (mul_le_mul_of_nonneg_left
                (by simpa [wrongSet] using hprob_wrong)
                hsuffix_nonneg)
    _ =
        (((((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) *
          (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
        ((((((r : Nat) : Rat) * badGapBound : Rat) : Real)) *
          pWrong) := by
          simp [baseReal, suffixReal, baseRat]

end ETC
end BanditRLProof
