import BanditRLProof.Algorithms.CausalAllocation
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Importance ratios and design cost under injective finite-state encoding. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory
set_option autoImplicit false

variable {A Z U : Type*}

theorem mass_map_injective (p : PMF Z) (e : Z → U) (he : Function.Injective e) (z : Z) :
    mass (p.map e) (e z) = mass p z := by
  unfold mass
  apply congrArg ENNReal.toReal
  rw [PMF.map_apply, tsum_eq_single z]
  · simp
  · intro b hb
    simp [he.eq_iff, Ne.symm hb]

theorem ratio_map_injective (p q : PMF Z) (e : Z → U) (he : Function.Injective e) (z : Z) :
    ratio (p.map e) (q.map e) (e z) = ratio p q z := by
  simp only [ratio, mass_map_injective _ e he]

theorem mixture_map (eta : PMF A) (p : A → PMF Z) (e : Z → U) :
    mixture eta (fun a => (p a).map e) = (mixture eta p).map e := by
  simp only [mixture, PMF.map_bind]

theorem covers_map_injective (p : A → PMF Z) (q : PMF Z) (hc : Covers p q)
    (e : Z → U) (he : Function.Injective e) :
    Covers (fun a => (p a).map e) (q.map e) := by
  intro a u hu
  have hsupport : u ∈ ((p a).map e).support := by
    change ((p a).map e) u ≠ 0
    intro hzero
    exact hu (by simp [mass, hzero])
  rw [PMF.mem_support_map_iff] at hsupport
  obtain ⟨z, _, rfl⟩ := hsupport
  rw [mass_map_injective _ e he] at hu ⊢
  exact hc a z hu

theorem weightedBit_map_injective (p q : PMF Z) (e : Z → U) (he : Function.Injective e)
    (B : ℝ) (z : Z) (y : Bool) :
    weightedBit (p.map e) (q.map e) B (e z,y) = weightedBit p q B (z,y) := by
  simp only [weightedBit, ratio_map_injective _ _ e he]

variable [Fintype Z] [Fintype U] [MeasurableSpace Z] [MeasurableSingletonClass Z]
variable [MeasurableSpace U] [MeasurableSingletonClass U]

theorem secondMoment_map_injective (p q : PMF Z) (e : Z → U) (he : Function.Injective e) :
    secondMoment (p.map e) (q.map e) = secondMoment p q := by
  have hi := integral_map (μ := p.toMeasure) (φ := e)
    (f := fun u => ratio (p.map e) (q.map e) u)
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable
  rw [PMF.toMeasure_map e p Measurable.of_discrete] at hi
  simp only [ratio_map_injective _ _ e he, PMF.integral_eq_sum, smul_eq_mul] at hi
  exact hi

variable [Fintype A] [Nonempty A]

theorem designCost_map_injective (p : A → PMF Z) (eta : PMF A)
    (e : Z → U) (he : Function.Injective e) :
    designCost (fun a => (p a).map e) eta = designCost p eta := by
  unfold designCost
  simp only [mixture_map, secondMoment_map_injective _ _ e he]

end BanditRLProof.Causal
