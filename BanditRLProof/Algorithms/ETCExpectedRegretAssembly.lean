import Mathlib.MeasureTheory.Integral.Lebesgue.Add
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

end ETC
end BanditRLProof
