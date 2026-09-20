import BanditRLProof.Algorithms.CausalSampleMGF
import BanditRLProof.Algorithms.CausalTuning

/-! Source-tuned confidence for the actual fixed-budget intervention estimator. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def GraphModel.sampleEstimate (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) : ℝ :=
  (∑ t : Fin T, g.sampleWeightedBit rewardBit actions eta i a B t w) / T

noncomputable def GraphModel.estimateCenter (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n) (a : A) (B : ℝ) : ℝ :=
  truncatedMean (g.parentLaw (actions a) i)
    (mixture eta (fun b => g.parentLaw (actions b) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) B

omit [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem GraphModel.sampleEstimate_centered_sum (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B c sign : ℝ) (T : ℕ) (hT : 0 < T)
    (w : Fin T → A × (Fin n → V)) :
    (∑ t : Fin T, sign*(g.sampleWeightedBit rewardBit actions eta i a B t w-c)) =
      (T:ℝ) * (sign*(g.sampleEstimate rewardBit actions eta i a B w-c)) := by
  have hT' : (T:ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sampleEstimate]
  field_simp

theorem GraphModel.sampleEstimate_signed_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (T : ℕ) (hT : 0 < T) (L : ℝ) (hL : 0 < L)
    (sign : ℝ) (hs : |sign| = 1) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤
      sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B)} ≤
      Real.exp (-L) := by
  dsimp only
  let m := designCost (fun b => g.parentLaw (actions b) i) eta
  let B := sourceThreshold m T L
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one (designCost_ge_one _ eta hc)
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hB : 0 < B := sourceThreshold_pos m T L hm hT' hL
  have h := g.sampleWeightedBit_signed_sum_tail rewardBit actions eta i hi hc a B hB.le T
    sign (1/(2*B)) ((T:ℝ)*sourceRadius m T L) hs (by positivity)
    (sourceTilt_admissible m T L hm hT' hL)
  simp_rw [g.sampleEstimate_centered_sum rewardBit actions eta i a B _ sign T hT] at h
  have hevent : {w : Fin T → A × (Fin n → V) | (T:ℝ)*sourceRadius m T L ≤
      (T:ℝ)*(sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B))} =
      {w | sourceRadius m T L ≤
        sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B)} := by
    ext w
    simp only [Set.mem_setOf_eq, mul_le_mul_iff_right₀ hT']
  change (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤
    sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B)} ≤ _
  change (g.sampleLaw actions eta T).real {w | (T:ℝ)*sourceRadius m T L ≤
    (T:ℝ)*(sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B))} ≤ _ at h
  rw [hevent] at h
  exact h.trans (Real.exp_le_exp.mpr (sourceTilt_exponent_le m T L hm hT' hL))

theorem GraphModel.sampleEstimate_abs_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (T : ℕ) (hT : 0 < T) (L : ℝ) (hL : 0 < L) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤
      |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B|} ≤
      2*Real.exp (-L) := by
  dsimp only
  let m := designCost (fun b => g.parentLaw (actions b) i) eta
  let B := sourceThreshold m T L
  let X := fun w : Fin T → A × (Fin n → V) =>
    g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B
  have hp := g.sampleEstimate_signed_tail rewardBit actions eta i hi hc a T hT L hL 1 (by norm_num)
  have hn := g.sampleEstimate_signed_tail rewardBit actions eta i hi hc a T hT L hL (-1) (by norm_num)
  change (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤ |X w|} ≤ _
  calc
    _ ≤ (g.sampleLaw actions eta T).real
      ({w | sourceRadius m T L ≤ X w} ∪ {w | sourceRadius m T L ≤ -X w}) := by
      apply measureReal_mono _ (by finiteness)
      intro w hw
      rcases le_total (X w) 0 with hx | hx
      · exact Or.inr (by simpa only [Set.mem_setOf_eq, abs_of_nonpos hx] using hw)
      · exact Or.inl (by simpa only [Set.mem_setOf_eq, abs_of_nonneg hx] using hw)
    _ ≤ (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤ X w} +
      (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤ -X w} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-L) := by
      simp only [one_mul, neg_one_mul] at hp hn
      linarith

theorem GraphModel.sampleEstimate_simultaneous_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) (L : ℝ) (hL : 0 < L) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | ∃ a : A, sourceRadius m T L ≤
      |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B|} ≤
      (Fintype.card A:ℝ) * (2*Real.exp (-L)) := by
  dsimp only
  rw [show {w | ∃ a : A, sourceRadius (designCost (fun b => g.parentLaw (actions b) i) eta) T L ≤
      |g.sampleEstimate rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L) w-
       g.estimateCenter rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L)|} =
    ⋃ a : A, {w | sourceRadius (designCost (fun b => g.parentLaw (actions b) i) eta) T L ≤
      |g.sampleEstimate rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L) w-
       g.estimateCenter rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L)|}
    by ext w; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    _ ≤ ∑ _a : A, 2*Real.exp (-L) := Finset.sum_le_sum fun a _ =>
      g.sampleEstimate_abs_tail rewardBit actions eta i hi hc a T hT L hL
    _ = _ := by simp [nsmul_eq_mul]

theorem GraphModel.sampleEstimate_source_confidence (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | ∃ a : A, sourceRadius m T L ≤
      |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B|} ≤
      1/(T:ℝ) := by
  have h := g.sampleEstimate_simultaneous_tail rewardBit actions eta i hi hc T hT
    (sourceLog T (Fintype.card A)) (sourceLog_pos T _ hT Fintype.card_pos)
  simpa only [sourceLog_union_budget T _ hT Fintype.card_pos] using h

end BanditRLProof.Causal
