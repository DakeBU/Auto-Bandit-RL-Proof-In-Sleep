import BanditRLProof.Algorithms.CausalOptimalAllocation
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic

/-! Actual intervention/assignment rounds and their fixed-budget product law. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def GraphModel.roundLaw (g : GraphModel V n)
    (actions : A → Fin n → Option V) (eta : PMF A) : PMF (A × (Fin n → V)) :=
  eta.bind fun a => (joint (g.doModel (actions a)).table).map fun x => (a,x)

def GraphModel.observation (g : GraphModel V n) (rewardBit : V → Bool) (i : Fin n)
    (ax : A × (Fin n → V)) : g.ParentConfig i × Bool :=
  (g.parentConfig i (history ax.2 i), rewardBit (ax.2 i))

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem GraphModel.roundLaw_observation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none) :
    (g.roundLaw actions eta).map (g.observation rewardBit i) =
      pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i)) (fun z => (g.parentTable i z).map rewardBit) := by
  have h := congrArg (fun p : PMF (g.ParentConfig i × V) =>
    p.map (fun zy => (zy.1, rewardBit zy.2)))
    (g.mixture_parent_joint actions eta i hi)
  simpa only [roundLaw, PMF.map_bind, PMF.map_comp, observation, Function.comp_def,
    mixture, pairedLaw] using h

noncomputable def GraphModel.sampleLaw (g : GraphModel V n)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ) :
    Measure (Fin T → A × (Fin n → V)) :=
  Measure.pi fun _ : Fin T => (g.roundLaw actions eta).toMeasure

instance GraphModel.sampleLaw_isProbabilityMeasure (g : GraphModel V n)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ) :
    IsProbabilityMeasure (g.sampleLaw actions eta T) := by
  unfold sampleLaw
  infer_instance

theorem GraphModel.sampleLaw_observation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ)
    (i : Fin n) (hi : ∀ a, actions a i = none) (t : Fin T) :
    (g.sampleLaw actions eta T).map (fun w => g.observation rewardBit i (w t)) =
      (pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i))
        (fun z => (g.parentTable i z).map rewardBit)).toMeasure := by
  change Measure.map (g.observation rewardBit i ∘
    (fun w : Fin T → A × (Fin n → V) => w t)) _ = _
  have ho : Measurable (g.observation (A := A) rewardBit i) := Measurable.of_discrete
  rw [← Measure.map_map ho (measurable_pi_apply t)]
  unfold sampleLaw
  rw [(measurePreserving_eval (fun _ : Fin T => (g.roundLaw actions eta).toMeasure) t).map_eq]
  rw [PMF.toMeasure_map (g.observation rewardBit i) (g.roundLaw actions eta) ho,
    g.roundLaw_observation rewardBit actions eta i hi]

theorem GraphModel.integral_sample_observation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ)
    (i : Fin n) (hi : ∀ a, actions a i = none) (t : Fin T)
    (f : g.ParentConfig i × Bool → ℝ) :
    (∫ w, f (g.observation rewardBit i (w t)) ∂g.sampleLaw actions eta T) =
      ∫ zy, f zy ∂(pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i))
        (fun z => (g.parentTable i z).map rewardBit)).toMeasure := by
  rw [← g.sampleLaw_observation rewardBit actions eta T i hi t]
  exact (integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable).symm

noncomputable def GraphModel.sampleWeightedBit (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B : ℝ) {T : ℕ} (t : Fin T) (w : Fin T → A × (Fin n → V)) : ℝ :=
  weightedBit (g.parentLaw (actions a) i)
    (mixture eta (fun b => g.parentLaw (actions b) i)) B (g.observation rewardBit i (w t))

theorem GraphModel.sampleWeightedBit_independent (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B : ℝ) (T : ℕ) :
    iIndepFun (g.sampleWeightedBit rewardBit actions eta i a B (T := T))
      (g.sampleLaw actions eta T) := by
  exact iIndepFun_pi
    (μ := fun _ : Fin T => (g.roundLaw actions eta).toMeasure)
    (X := fun _ : Fin T => fun ax : A × (Fin n → V) =>
      weightedBit (g.parentLaw (actions a) i)
        (mixture eta (fun b => g.parentLaw (actions b) i)) B (g.observation rewardBit i ax))
    (fun _ => Measurable.of_discrete.aemeasurable)

theorem GraphModel.sampleWeightedBit_mean (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none) (a : A) (B : ℝ)
    (T : ℕ) (t : Fin T) :
    (∫ w, g.sampleWeightedBit rewardBit actions eta i a B t w ∂g.sampleLaw actions eta T) =
      truncatedMean (g.parentLaw (actions a) i)
        (mixture eta (fun b => g.parentLaw (actions b) i))
        (fun z => mass ((g.parentTable i z).map rewardBit) true) B := by
  unfold sampleWeightedBit
  rw [g.integral_sample_observation rewardBit actions eta T i hi t, PMF.integral_eq_sum]
  simpa only [Fintype.sum_prod_type, smul_eq_mul, mass] using
    weightedBit_mean (g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) (fun z => (g.parentTable i z).map rewardBit) B

theorem GraphModel.sampleWeightedBit_second_le (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (T : ℕ) (t : Fin T) :
    (∫ w, (g.sampleWeightedBit rewardBit actions eta i a B t w)^2 ∂g.sampleLaw actions eta T) ≤
      secondMoment (g.parentLaw (actions a) i)
        (mixture eta (fun b => g.parentLaw (actions b) i)) := by
  unfold sampleWeightedBit
  rw [g.integral_sample_observation rewardBit actions eta T i hi t
    (fun zy => (weightedBit (g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) B zy)^2), PMF.integral_eq_sum]
  simpa only [Fintype.sum_prod_type, smul_eq_mul, mass] using
    weightedBit_second_le (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) hc a (fun z => (g.parentTable i z).map rewardBit) B

end BanditRLProof.Causal
