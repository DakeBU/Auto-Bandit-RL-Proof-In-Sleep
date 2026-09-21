import BanditRLProof.Algorithms.CausalExpectedRegret

/-! The actual learner under uniform and attained optimal covered allocations. -/
namespace BanditRLProof.Causal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

variable {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem GraphModel.expected_simpleRegret_uniform (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V)
    (i : Fin n) (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype A
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((Fintype.card A:ℝ)*L/T) + 1/(T:ℝ) := by
  have h := g.expected_simpleRegret_source_bound rewardBit actions
    (PMF.uniformOfFintype A) i hi (uniform_covers _) T hT
  dsimp only at h ⊢
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (uniform_designCost_le_card _)
    (sourceLog_pos T _ hT Fintype.card_pos).le

theorem GraphModel.expected_simpleRegret_optimal (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V)
    (i : Fin n) (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let p := fun a => g.parentLaw (actions a) i
    let eta := optimalAllocation p
    let m := designCost p eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T) + 1/(T:ℝ) :=
  g.expected_simpleRegret_source_bound rewardBit actions _ i hi
    (optimalAllocation_covers _) T hT

end BanditRLProof.Causal
