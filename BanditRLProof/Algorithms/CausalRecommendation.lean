import BanditRLProof.Algorithms.CausalConfidence
import BanditRLProof.FiniteRealArgmax

/-! A fixed-order recommendation from observed estimates and its pathwise regret bound. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def maximizingActions (score : A → ℝ) : Finset A :=
  Finset.univ.filter (fun a => score a = score (FiniteRealArgmax.choose score))

theorem maximizingActions_nonempty (score : A → ℝ) : (maximizingActions score).Nonempty := by
  refine ⟨FiniteRealArgmax.choose score, ?_⟩
  simp [maximizingActions]

noncomputable def orderedArgmax (score : A → ℝ) : A :=
  (maximizingActions score).min' (maximizingActions_nonempty score)

theorem score_le_orderedArgmax (score : A → ℝ) (a : A) :
    score a ≤ score (orderedArgmax score) := by
  have h := Finset.min'_mem (maximizingActions score) (maximizingActions_nonempty score)
  have heq : score (orderedArgmax score) = score (FiniteRealArgmax.choose score) := by
    simpa only [maximizingActions, Finset.mem_filter, Finset.mem_univ, true_and] using h
  rw [heq]
  exact FiniteRealArgmax.score_le_choose score a

theorem orderedArgmax_le_of_maximal (score : A → ℝ) (a : A)
    (ha : ∀ b, score b ≤ score a) : orderedArgmax score ≤ a := by
  apply Finset.min'_le
  simp only [maximizingActions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_antisymm (FiniteRealArgmax.score_le_choose score a) (ha _)

noncomputable def GraphModel.rewardMean (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (i : Fin n) (a : A) : ℝ :=
  ∑ z, mass (g.parentLaw (actions a) i) z * mass ((g.parentTable i z).map rewardBit) true

theorem GraphModel.rewardMean_eq_integral (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (i : Fin n) (a : A) (hi : actions a i = none) :
    g.rewardMean rewardBit actions i a =
      ∫ x, (if rewardBit (x i) then (1:ℝ) else 0) ∂(joint (g.doModel (actions a)).table).toMeasure := by
  let proj := fun x : Fin n → V => (g.parentConfig i (history x i), rewardBit (x i))
  let f := fun zy : g.ParentConfig i × Bool => if zy.2 then (1:ℝ) else 0
  have hmap : (joint (g.doModel (actions a)).table).toMeasure.map proj =
      (pairedLaw (g.parentLaw (actions a) i) (fun z => (g.parentTable i z).map rewardBit)).toMeasure := by
    rw [PMF.toMeasure_map proj _ Measurable.of_discrete]
    apply congrArg PMF.toMeasure
    have h := congrArg (fun p : PMF (g.ParentConfig i × V) =>
      p.map (fun zy => (zy.1, rewardBit zy.2)))
      (g.intervention_parent_joint (actions a) i hi)
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, pairedLaw, proj] using h
  have hint := integral_map (μ := (joint (g.doModel (actions a)).table).toMeasure)
    (φ := proj) (f := f) Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable
  rw [hmap, PMF.integral_eq_sum] at hint
  have hsum : (∑ zy, ((pairedLaw (g.parentLaw (actions a) i) (fun z => (g.parentTable i z).map rewardBit)) zy).toReal • f zy) =
      g.rewardMean rewardBit actions i a := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, f, Bool.false_eq_true,
      if_false, Bool.true_eq, if_true, smul_eq_mul, mul_one, mul_zero, add_zero]
    change (∑ z, mass (pairedLaw (g.parentLaw (actions a) i) (fun z => (g.parentTable i z).map rewardBit)) (z,true)) = _
    simp only [pairedLaw_mass, rewardMean]
  rw [hsum] at hint
  exact hint

theorem GraphModel.rewardMean_bounds (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (i : Fin n) (a : A) :
    0 ≤ g.rewardMean rewardBit actions i a ∧ g.rewardMean rewardBit actions i a ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun z _ => mul_nonneg (mass_nonneg _ _) (mass_nonneg _ _)
  · calc
      _ ≤ ∑ z, mass (g.parentLaw (actions a) i) z := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_of_le_one_right (mass_nonneg _ _) (mass_le_one _ _)
      _ = 1 := sum_mass _

noncomputable def GraphModel.sampleRecommendation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) : A :=
  orderedArgmax (fun a => g.sampleEstimate rewardBit actions eta i a B w)

noncomputable def GraphModel.simpleRegret (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) : ℝ :=
  g.rewardMean rewardBit actions i (FiniteRealArgmax.choose (g.rewardMean rewardBit actions i)) -
    g.rewardMean rewardBit actions i (g.sampleRecommendation rewardBit actions eta i B w)

theorem GraphModel.simpleRegret_bounds (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) :
    0 ≤ g.simpleRegret rewardBit actions eta i B w ∧ g.simpleRegret rewardBit actions eta i B w ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (FiniteRealArgmax.score_le_choose (g.rewardMean rewardBit actions i) _)
  · have hb := g.rewardMean_bounds rewardBit actions i (FiniteRealArgmax.choose (g.rewardMean rewardBit actions i))
    have hr := g.rewardMean_bounds rewardBit actions i (g.sampleRecommendation rewardBit actions eta i B w)
    unfold simpleRegret
    linarith

theorem GraphModel.simpleRegret_le_on_confidence (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (B : ℝ) (hB : 0 < B) (epsilon : ℝ) {T : ℕ}
    (w : Fin T → A × (Fin n → V))
    (hw : ∀ a, |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B| ≤ epsilon) :
    g.simpleRegret rewardBit actions eta i B w ≤
      2*epsilon + designCost (fun a => g.parentLaw (actions a) i) eta / B := by
  let best := FiniteRealArgmax.choose (g.rewardMean rewardBit actions i)
  let chosen := g.sampleRecommendation rewardBit actions eta i B w
  have hbest := (abs_le.mp (hw best)).1
  have hrec := (abs_le.mp (hw chosen)).2
  have hmax : g.sampleEstimate rewardBit actions eta i best B w ≤ g.sampleEstimate rewardBit actions eta i chosen B w :=
    score_le_orderedArgmax (fun a => g.sampleEstimate rewardBit actions eta i a B w) best
  have hmean (a : A) : g.estimateCenter rewardBit actions eta i a B +
      truncationBias (g.parentLaw (actions a) i)
        (mixture eta (fun a => g.parentLaw (actions a) i))
        (fun z => mass ((g.parentTable i z).map rewardBit) true) B = g.rewardMean rewardBit actions i a :=
    truncatedMean_add_bias (fun a => g.parentLaw (actions a) i) _ hc a _ B
  have hb0 := truncationBias_nonneg (g.parentLaw (actions chosen) i)
    (mixture eta (fun a => g.parentLaw (actions a) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) (fun z => mass_nonneg _ _) B
  have hb := (truncationBias_le (g.parentLaw (actions best) i)
    (mixture eta (fun a => g.parentLaw (actions a) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) (fun z => mass_le_one _ _) B hB).trans
    (div_le_div_of_nonneg_right
      (secondMoment_le_designCost (fun a => g.parentLaw (actions a) i) eta best) hB.le)
  have hmb := hmean best
  have hmr := hmean chosen
  change g.rewardMean rewardBit actions i best - g.rewardMean rewardBit actions i chosen ≤ _
  linarith

end BanditRLProof.Causal
