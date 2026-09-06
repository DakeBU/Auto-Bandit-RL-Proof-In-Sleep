import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Real
import BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly
import BanditRLProof.ExpectationBochnerSums

/-!
# ETC lower-integral and Bochner regret assembly

This module lifts the pointwise wrong-commit regret bridge to the project's
expectation surfaces: an `ENNReal.ofReal` lower-integral surrogate and an
ordinary Real-valued Bochner integral wrapper.  It does not introduce
concentration, filtrations, or a final ETC theorem.
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
Finite-arm `actionWithCommit` pseudo-regret has an integrable Real cast when
the selected commit arm is measurable and the ambient measure is finite.

The proof uses only the finite range of `commit : Omega -> Fin K`: the
integrand is a measurable finite-valued function, hence bounded by the finite
sum of the absolute values of its arm-indexed constants.
-/
theorem integrable_real_pseudoRegret_actionWithCommit_choice_of_measurable_commit
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat)
    (hmeas_commit : Measurable commit) :
    Integrable
      (fun omega : Omega =>
        (((pseudoRegret model (ETC.actionWithCommit spec (commit omega))
          (spec.explorationPulls * K + r) : Rat) : Real))) mu := by
  let c : Fin K -> Real :=
    fun a : Fin K =>
      (((pseudoRegret model (ETC.actionWithCommit spec a)
        (spec.explorationPulls * K + r) : Rat) : Real))
  have hc_meas : Measurable c := by
    exact measurable_of_countable c
  have hf_meas : Measurable (fun omega : Omega => c (commit omega)) :=
    hc_meas.comp hmeas_commit
  have hbound :
      exists C : Real, forall omega : Omega, norm (c (commit omega)) <= C := by
    let C : Real :=
      ((Finset.univ : Finset (Fin K)).sum (fun a : Fin K => norm (c a)))
    refine Exists.intro C ?_
    intro omega
    exact
      Finset.single_le_sum
        (fun a _ha => norm_nonneg (c a))
        (Finset.mem_univ (commit omega))
  cases hbound with
  | intro C hC =>
      change Integrable (fun omega : Omega => c (commit omega)) mu
      refine MeasureTheory.Integrable.of_bound
        hf_meas.aestronglyMeasurable C ?_
      exact Filter.Eventually.of_forall hC

/--
Bochner/Real expected-regret assembly with a separate probability charge for
each possible commit arm.

The suffix term is decomposed into the finite family of measurable events
`{omega | commit omega = a}`.  Unlike the coarser wrong-commit wrapper below,
this theorem preserves every arm gap and therefore exposes the per-arm RHS
needed by the LML ETC route.  It does not supply the armwise probability
bounds themselves.
-/
theorem integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat)
    (hmeas_commit : Measurable commit) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.actionWithCommit spec (commit omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
          mu.real {omega : Omega | commit omega = a}) := by
  let regret : Omega -> Real :=
    fun omega : Omega =>
      (((pseudoRegret model
          (ETC.actionWithCommit spec (commit omega))
          (spec.explorationPulls * K + r) : Rat) : Real))
  let baseRat : Rat :=
    ((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat))
  let baseReal : Real := ((baseRat : Rat) : Real)
  let suffixValue : Fin K -> Real :=
    fun a : Fin K =>
      (((((r : Nat) : Rat) * model.gap a : Rat) : Real))
  let commitSet : Fin K -> Set Omega :=
    fun a : Fin K => {omega : Omega | commit omega = a}
  let suffixTerm : Fin K -> Omega -> Real :=
    fun a : Fin K => (commitSet a).indicator (fun _ => suffixValue a)
  let suffix : Omega -> Real :=
    fun omega : Omega =>
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => suffixTerm a omega)
  let bound : Omega -> Real :=
    fun omega : Omega => baseReal + suffix omega
  have hcommitSet : forall a : Fin K, MeasurableSet (commitSet a) := by
    intro a
    change MeasurableSet (commit ⁻¹' {a})
    exact hmeas_commit (measurableSet_singleton a)
  have hterm : forall a : Fin K, Integrable (suffixTerm a) mu := by
    intro a
    exact (integrable_const (suffixValue a)).indicator (hcommitSet a)
  have hsuffix_integrable : Integrable suffix mu := by
    exact
      BanditRLProof.IntegrabilitySums.integrable_univ_sum
        (mu := mu) (f := suffixTerm) hterm
  have hbound_integrable : Integrable bound mu := by
    exact (integrable_const baseReal).add hsuffix_integrable
  have hregret_integrable : Integrable regret mu := by
    simpa [regret] using
      (ETC.integrable_real_pseudoRegret_actionWithCommit_choice_of_measurable_commit
        (mu := mu) (spec := spec) (model := model)
        (commit := commit) (r := r) hmeas_commit)
  have hsuffix_apply : forall omega : Omega,
      suffix omega = suffixValue (commit omega) := by
    intro omega
    rw [show suffix omega =
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => suffixTerm a omega) by rfl]
    rw [Finset.sum_eq_single (commit omega)]
    all_goals simp [suffixTerm, commitSet]
    aesop
  have hpoint : forall omega : Omega, regret omega <= bound omega := by
    intro omega
    have hrat :=
      ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
        (spec := spec) (model := model) (commitArm := commit omega) (r := r)
    have hreal :
        regret omega <= baseReal + suffixValue (commit omega) := by
      unfold regret baseReal baseRat suffixValue
      exact_mod_cast hrat
    simpa [bound, hsuffix_apply omega] using hreal
  have hintegral_suffix :
      MeasureTheory.integral mu suffix =
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            suffixValue a * mu.real (commitSet a)) := by
    rw [show suffix = fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => suffixTerm a omega) by rfl]
    rw [BanditRLProof.ExpectationBochnerSums.integral_univ_sum
      (mu := mu) (f := suffixTerm) hterm]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [show suffixTerm a =
        (commitSet a).indicator (fun _ : Omega => suffixValue a) by rfl]
    rw [MeasureTheory.integral_indicator (hcommitSet a)]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real, mul_comm]
  calc
    MeasureTheory.integral mu regret <=
        MeasureTheory.integral mu bound := by
      exact MeasureTheory.integral_mono
        hregret_integrable hbound_integrable hpoint
    _ = baseReal + MeasureTheory.integral mu suffix := by
      rw [show bound = fun omega : Omega =>
          (fun _omega : Omega => baseReal) omega + suffix omega by rfl]
      rw [MeasureTheory.integral_add
        (integrable_const baseReal) hsuffix_integrable]
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.probReal_univ]
    _ = baseReal +
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => suffixValue a * mu.real (commitSet a)) := by
      rw [hintegral_suffix]
    _ =
        (((((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) *
          (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
              mu.real {omega : Omega | commit omega = a}) := by
      rfl

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
