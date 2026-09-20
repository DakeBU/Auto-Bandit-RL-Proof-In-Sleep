import BanditRLProof.Algorithms.CausalRecommendation

/-! Expected simple regret of the actual intervention sampler and recommendation.
The finite-budget residual is retained explicitly. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem GraphModel.expected_simpleRegret_le_tuned (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      2*sourceRadius m T L + m/B + 1/(T:ℝ) := by
  dsimp only
  let m := designCost (fun a => g.parentLaw (actions a) i) eta
  let L := sourceLog T (Fintype.card A)
  let B := sourceThreshold m T L
  let eps := sourceRadius m T L
  let C := 2*eps+m/B
  let bad : Set (Fin T → A × (Fin n → V)) :=
    {w | ∃ a : A, eps ≤ |g.sampleEstimate rewardBit actions eta i a B w -
      g.estimateCenter rewardBit actions eta i a B|}
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one (designCost_ge_one _ eta hc)
  have ht : (0:ℝ) < T := by exact_mod_cast hT
  have hL : 0 < L := sourceLog_pos T _ hT Fintype.card_pos
  have hB : 0 < B := sourceThreshold_pos m T L hm ht hL
  have heps : 0 ≤ eps := by
    dsimp [eps, sourceRadius]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbad : MeasurableSet bad := Set.to_countable _ |>.measurableSet
  have hpoint (w : Fin T → A × (Fin n → V)) :
      g.simpleRegret rewardBit actions eta i B w ≤ C + bad.indicator (fun _ => (1:ℝ)) w := by
    by_cases hw : w ∈ bad
    · rw [Set.indicator_of_mem hw]
      exact (g.simpleRegret_bounds rewardBit actions eta i B w).2.trans (by linarith)
    · rw [Set.indicator_of_notMem hw, add_zero]
      apply g.simpleRegret_le_on_confidence rewardBit actions eta i hc B hB eps w
      intro a
      exact (lt_of_not_ge (fun ha => hw ⟨a,ha⟩)).le
  have h := integral_mono (μ := g.sampleLaw actions eta T)
    (Integrable.of_finite) (Integrable.of_finite) hpoint
  rw [integral_add (integrable_const C) (Integrable.of_finite),
    integral_const, integral_indicator_const (1:ℝ) hbad] at h
  simp only [probReal_univ, smul_eq_mul, mul_one, one_mul] at h
  have hp := g.sampleEstimate_source_confidence rewardBit actions eta i hi hc T hT
  change (g.sampleLaw actions eta T).real bad ≤ 1/(T:ℝ) at hp
  exact h.trans (add_le_add le_rfl hp)

theorem GraphModel.expected_simpleRegret_bounds (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (B : ℝ) (T : ℕ) :
    0 ≤ (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ∧
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤ 1 := by
  constructor
  · exact integral_nonneg fun w => (g.simpleRegret_bounds rewardBit actions eta i B w).1
  · have h := integral_mono (μ := g.sampleLaw actions eta T)
      (Integrable.of_finite) (integrable_const (1:ℝ))
      (fun w => (g.simpleRegret_bounds rewardBit actions eta i B w).2)
    simpa using h

theorem GraphModel.expected_simpleRegret_source_bound (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T) + 1/(T:ℝ) := by
  have hm : 0 < designCost (fun a => g.parentLaw (actions a) i) eta :=
    lt_of_lt_of_le zero_lt_one (designCost_ge_one _ eta hc)
  have h := g.expected_simpleRegret_le_tuned rewardBit actions eta i hi hc T hT
  dsimp only at h ⊢
  rw [sourceRegret_scale _ _ _ hm (by exact_mod_cast hT)
    (sourceLog_pos T _ hT Fintype.card_pos)] at h
  exact h

theorem GraphModel.expected_simpleRegret_explicit_rate (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (3*Real.sqrt 2+7)*Real.sqrt (m*L/T) := by
  have h := g.expected_simpleRegret_source_bound rewardBit actions eta i hi hc T hT
  have hr := sourceResidual_le_scale _ (designCost_ge_one _ eta hc)
    T (Fintype.card A) hT Fintype.card_pos
  dsimp only at h ⊢
  linarith

end BanditRLProof.Causal
