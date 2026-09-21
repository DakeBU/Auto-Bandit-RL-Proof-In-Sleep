import BanditRLProof.Algorithms.CausalHeterogeneousSampling

/-! Actual expected simple regret on native heterogeneous finite DAGs. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {n : ℕ} {V : Fin n → Type*} {W A : Type*}
variable [∀ i, Fintype (V i)] [∀ i, Inhabited (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]
variable [Fintype W] [Inhabited W] [MeasurableSpace W] [MeasurableSingletonClass W]
variable [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def NodeGraphModel.rewardMean (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool) (a : A) : ℝ :=
  ∫ x, (if rewardBit (x i) then (1:ℝ) else 0) ∂(nodeJoint (nodeIntervene g.table (actions a))).toMeasure

theorem NodeGraphModel.rewardMean_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool)
    (a : A) (hi : actions a i = none) :
    (g.encodeGraph c).rewardMean (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) i a = g.rewardMean actions i rewardBit a := by
  rw [GraphModel.rewardMean_eq_integral _ _ _ _ _ (by simp [NodeCodec.encodeAction, hi]),
    g.intervention_joint_encoded,
    ← PMF.toMeasure_map c.encodeAssignment _ Measurable.of_discrete]
  rw [integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  simp only [NodeCodec.encodeAssignment, c.decode_encode]
  rfl

noncomputable def NodeGraphModel.sampleRecommendation (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((j : Fin n) → V j)) : A :=
  orderedArgmax (fun a => g.sampleEstimate actions eta i rewardBit a B w)

noncomputable def NodeGraphModel.simpleRegret (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((j : Fin n) → V j)) : ℝ :=
  g.rewardMean actions i rewardBit (FiniteRealArgmax.choose (g.rewardMean actions i rewardBit)) -
    g.rewardMean actions i rewardBit (g.sampleRecommendation actions eta i rewardBit B w)

theorem NodeGraphModel.sampleRecommendation_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((j : Fin n) → V j)) :
    (g.encodeGraph c).sampleRecommendation (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) eta i B (c.encodeSamples w) =
      g.sampleRecommendation actions eta i rewardBit B w := by
  simp only [GraphModel.sampleRecommendation, sampleRecommendation, g.sampleEstimate_encoded]

theorem NodeGraphModel.simpleRegret_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none)
    (B : ℝ) {T : ℕ} (w : Fin T → A × ((j : Fin n) → V j)) :
    (g.encodeGraph c).simpleRegret (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) eta i B (c.encodeSamples w) =
      g.simpleRegret actions eta i rewardBit B w := by
  have hm : (g.encodeGraph c).rewardMean (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) i = g.rewardMean actions i rewardBit :=
    funext fun a => g.rewardMean_encoded c actions i rewardBit a (hi a)
  simp only [GraphModel.simpleRegret, simpleRegret, hm, g.sampleRecommendation_encoded]

theorem NodeGraphModel.expected_simpleRegret_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none) (B : ℝ) (T : ℕ) :
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) =
      ∫ w, (g.encodeGraph c).simpleRegret (fun v => rewardBit (c.decode i v))
        (fun a => c.encodeAction (actions a)) eta i B w
        ∂(g.encodeGraph c).sampleLaw (fun a => c.encodeAction (actions a)) eta T := by
  rw [← g.sampleLaw_encoded c actions eta T,
    integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  simp only [g.simpleRegret_encoded c actions eta i rewardBit hi]

theorem NodeGraphModel.covers_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A) (i : Fin n)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i))) :
    Covers (fun a => (g.encodeGraph c).parentLaw (c.encodeAction (actions a)) i)
      (mixture eta (fun a => (g.encodeGraph c).parentLaw (c.encodeAction (actions a)) i)) := by
  simp only [g.parentLaw_encoded, mixture_map]
  exact covers_map_injective _ _ hc _ (Function.LeftInverse.injective (g.decode_encodeParent c i))

/-- Native finite-node theorem: no codec or common-alphabet premise is required. -/
theorem NodeGraphModel.expected_simpleRegret_source_bound (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i))) (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T)+1/(T:ℝ) := by
  let c := productNodeCodec V
  have hi' : ∀ a, c.encodeAction (actions a) i = none := by
    intro a
    simp [NodeCodec.encodeAction, hi a]
  have h := (g.encodeGraph c).expected_simpleRegret_source_bound
    (fun v => rewardBit (c.decode i v)) (fun a => c.encodeAction (actions a)) eta i hi'
    (g.covers_encoded c actions eta i hc) T hT
  dsimp only at h ⊢
  rw [g.designCost_encoded] at h
  rw [g.expected_simpleRegret_encoded c actions eta i rewardBit hi]
  exact h

theorem NodeGraphModel.expected_simpleRegret_bounds (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none) (B : ℝ) (T : ℕ) :
    0 ≤ (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ∧
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤ 1 := by
  let c := productNodeCodec V
  rw [g.expected_simpleRegret_encoded c actions eta i rewardBit hi]
  exact (g.encodeGraph c).expected_simpleRegret_bounds _ _ _ _ _ _

theorem NodeGraphModel.expected_simpleRegret_explicit_rate (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i))) (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (3*Real.sqrt 2+7)*Real.sqrt (m*L/T) := by
  have h := g.expected_simpleRegret_source_bound actions eta i rewardBit hi hc T hT
  have hr := sourceResidual_le_scale _ (designCost_ge_one _ eta hc)
    T (Fintype.card A) hT Fintype.card_pos
  dsimp only at h ⊢
  linarith

theorem NodeGraphModel.expected_simpleRegret_uniform (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool)
    (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype A
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((Fintype.card A:ℝ)*L/T)+1/(T:ℝ) := by
  have h := g.expected_simpleRegret_source_bound actions (PMF.uniformOfFintype A)
    i rewardBit hi (uniform_covers _) T hT
  dsimp only at h ⊢
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (uniform_designCost_le_card _)
    (sourceLog_pos T _ hT Fintype.card_pos).le

theorem NodeGraphModel.expected_simpleRegret_optimal (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool)
    (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let p := fun a => g.parentLaw (actions a) i
    let eta := optimalAllocation p
    let m := designCost p eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T)+1/(T:ℝ) :=
  g.expected_simpleRegret_source_bound actions _ i rewardBit hi (optimalAllocation_covers _) T hT

end BanditRLProof.Causal
