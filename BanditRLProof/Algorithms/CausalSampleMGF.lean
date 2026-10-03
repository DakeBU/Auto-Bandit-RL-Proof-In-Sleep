import BanditRLProof.Algorithms.CausalSampling
import BanditRLProof.HeavyTailFixedTilt

/-! Centered MGF and signed sum tails on actual causal intervention samples. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem GraphModel.sampleWeightedBit_signed_mgf (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (hB : 0 ≤ B) (T : ℕ) (t : Fin T)
    (sign tilt : ℝ) (hs : |sign| = 1) (hsmall : |tilt| * (2*B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun w => sign * (g.sampleWeightedBit rewardBit actions eta i a B t w -
        truncatedMean (g.parentLaw (actions a) i)
          (mixture eta (fun b => g.parentLaw (actions b) i))
          (fun z => mass ((g.parentTable i z).map rewardBit) true) B))
      tilt (tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta)
      (g.sampleLaw actions eta T) := by
  let W := g.sampleWeightedBit rewardBit actions eta i a B t
  have hbound : ∀ w, |sign * W w| ≤ B := by
    intro w
    have hb := weightedBit_bounds (g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) B hB (g.observation rewardBit i (w t))
    change 0 ≤ W w ∧ W w ≤ B at hb
    rw [abs_mul, hs, one_mul, abs_of_nonneg hb.1]
    exact hb.2
  have hs2 : sign^2 = 1 := by
    calc
      sign^2 = |sign|^2 := (sq_abs sign).symm
      _ = 1 := by rw [hs]; norm_num
  have hsecond : (∫ w, (sign * W w)^2 ∂g.sampleLaw actions eta T) ≤
      designCost (fun b => g.parentLaw (actions b) i) eta := by
    simp only [mul_pow, hs2, one_mul]
    change (∫ w, (g.sampleWeightedBit rewardBit actions eta i a B t w)^2
      ∂g.sampleLaw actions eta T) ≤ _
    exact (g.sampleWeightedBit_second_le rewardBit actions eta i hi hc a B T t).trans
      (secondMoment_le_designCost (fun b => g.parentLaw (actions b) i) eta a)
  have h := HeavyTail.bounded_centering_mgf (g.sampleLaw actions eta T)
    (fun w => sign * W w) B _ tilt Measurable.of_discrete hbound hsecond hsmall
  simpa only [integral_const_mul, W, g.sampleWeightedBit_mean rewardBit actions eta i hi a B T t,
    mul_sub] using h

theorem GraphModel.sampleWeightedBit_signed_sum_mgf (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (hB : 0 ≤ B) (T : ℕ)
    (sign tilt : ℝ) (hs : |sign| = 1) (hsmall : |tilt| * (2*B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun w => ∑ t : Fin T, sign * (g.sampleWeightedBit rewardBit actions eta i a B t w -
        truncatedMean (g.parentLaw (actions a) i)
          (mixture eta (fun b => g.parentLaw (actions b) i))
          (fun z => mass ((g.parentTable i z).map rewardBit) true) B))
      tilt ((T:ℝ) * (tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta))
      (g.sampleLaw actions eta T) := by
  let c := truncatedMean (g.parentLaw (actions a) i)
    (mixture eta (fun b => g.parentLaw (actions b) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) B
  let X := fun t : Fin T => fun w => sign * (g.sampleWeightedBit rewardBit actions eta i a B t w - c)
  have hind : iIndepFun X (g.sampleLaw actions eta T) :=
    (g.sampleWeightedBit_independent rewardBit actions eta i a B T).comp
      (fun _ x => sign * (x-c)) (fun _ => (measurable_id.sub measurable_const).const_mul sign)
  have h := HeavyTail.independent_sum_mgf (g.sampleLaw actions eta T) X Finset.univ tilt
    (fun _ => tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta)
    hind (fun _ => Measurable.of_discrete)
    (fun t _ => g.sampleWeightedBit_signed_mgf rewardBit actions eta i hi hc a B hB T t sign tilt hs hsmall)
  have hfun : (∑ t : Fin T, X t) = (fun w => ∑ t : Fin T, X t w) := by
    funext w
    simp only [Finset.sum_apply]
  rw [hfun] at h
  simpa only [X, c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

theorem GraphModel.sampleWeightedBit_signed_sum_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (hB : 0 ≤ B) (T : ℕ)
    (sign tilt r : ℝ) (hs : |sign| = 1) (ht : 0 ≤ tilt)
    (hsmall : |tilt| * (2*B) ≤ 1) :
    (g.sampleLaw actions eta T).real {w | r ≤
      ∑ t : Fin T, sign * (g.sampleWeightedBit rewardBit actions eta i a B t w -
        truncatedMean (g.parentLaw (actions a) i)
          (mixture eta (fun b => g.parentLaw (actions b) i))
          (fun z => mass ((g.parentTable i z).map rewardBit) true) B)} ≤
      Real.exp (-tilt*r + (T:ℝ) * (tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta)) :=
  (g.sampleWeightedBit_signed_sum_mgf rewardBit actions eta i hi hc a B hB T sign tilt hs hsmall).measure_ge_le_exp_add r ht

end BanditRLProof.Causal
