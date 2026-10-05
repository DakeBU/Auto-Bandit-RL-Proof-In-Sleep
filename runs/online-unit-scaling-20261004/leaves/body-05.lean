import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineHuber
import BanditRLProof.OnlineAffineSubgradient
import BanditRLProof.OnlineOptimalStep
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineSubgradientPolicy
open scoped InnerProductSpace
namespace BanditRL.OnlineUnitScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

abbrev V : Domain (E := E) := BanditRL.OnlineHuber.fullSpace
def scaledLoss (c : ℝ) (f : E → EReal) : E → EReal := fun y => f (c • y)
def scaledEta (c : ℝ) (η : ℕ → ℝ) : ℕ → ℝ := fun t => η t / c ^ 2
def scaledPolicy (c : ℝ) (p : SupportPolicy (E := E)) : SupportPolicy (E := E) :=
  fun t past h f => c • p t (fun i => scaledLoss c⁻¹ (past i))
    (fun i => c • h i) (scaledLoss c⁻¹ f)

theorem unit_exponents {D : Type*} [AddCommGroup D] (X L H : D) (h : H + (L - X) = X) :
    H = X + X - L := by
  calc
    H = (H + (L - X)) - (L - X) := by abel
    _ = X - (L - X) := by rw [h]
    _ = X + X - L := by abel

theorem regret_unit_exponents {D : Type*} [AddCommGroup D] (X L : D) :
    (X + X - (X + X - L) = L) ∧ ((X + X - L) + (L - X) + (L - X) = L) := by
  constructor <;> abel

theorem inverse_loss (c : ℝ) (hc : 0 < c) (f : E → EReal) :
    scaledLoss c⁻¹ (scaledLoss c f) = f := by
  funext y
  simp only [scaledLoss, smul_inv_smul₀ hc.ne']

theorem proper_scaled_loss (c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : SourceProper f) :
    SourceProper (scaledLoss c f) := by
  rcases hf with ⟨hbot, x, r, hr⟩
  constructor
  · intro y
    exact hbot (c • y)
  · refine ⟨c⁻¹ • x, r, ?_⟩
    simpa only [scaledLoss, smul_inv_smul₀ hc.ne'] using hr

theorem subgradient_scaled (c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : SourceProper f) (y g : E) (hg : g ∈ SourceSubdifferential f (c • y)) :
    c • g ∈ SourceSubdifferential (scaledLoss c f) y := by
  let A : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  have ha : A.adjoint g = c • g := by
    apply ext_inner_right ℝ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right]
  have hs := theorem_2_28 f hf A 0 y
    (show c • g ∈ A.adjoint '' SourceSubdifferential f (A y + 0) from
      ⟨g, by simpa only [A, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, add_zero] using hg, ha⟩)
  simpa only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    add_zero, scaledLoss] using hs

theorem subdifferentiable_scaled (c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f) :
    BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (scaledLoss c f) := by
  refine ⟨proper_scaled_loss c hc f hf.1, ?_⟩
  intro y hy
  obtain ⟨g, hg⟩ := hf.2 (c • y) (show c • y ∈ V.carrier from Set.mem_univ _)
  exact ⟨c • g, subgradient_scaled c hc f hf.1 y g hg⟩

theorem hasGradientAt_scaled (c : ℝ) (f : E → ℝ) (y g : E) (hf : HasGradientAt f g (c • y)) :
    HasGradientAt (fun z => f (c • z)) (c • g) y := by
  let A : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  have hd : HasFDerivAt (fun z => f (c • z))
      ((InnerProductSpace.toDual ℝ E g).comp A) y := by
    simpa only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using
      hf.hasFDerivAt.comp y A.hasFDerivAt
  have he : InnerProductSpace.toDual ℝ E (c • g) =
      (InnerProductSpace.toDual ℝ E g).comp A := by
    ext z
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
      A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right]
  rw [hasGradientAt_iff_hasFDerivAt, he]
  exact hd

theorem gradient_scaled (c : ℝ) (f : E → ℝ) (y : E) (hf : DifferentiableAt ℝ f (c • y)) :
    gradient (fun z => f (c • z)) y = c • gradient f (c • y) := by
  exact (hasGradientAt_scaled c f y (gradient f (c • y))
    hf.hasGradientAt).gradient

theorem step_scaling (c : ℝ) (hc : 0 < c) (η : ℝ) (x g : E) :
    c⁻¹ • (x - η • g) = c⁻¹ • x - (η / c ^ 2) • (c • g) := by
  have hs : c⁻¹ * η = (η / c ^ 2) * c := by
    field_simp
    <;> ring
  simp only [smul_sub, smul_smul, hs]

theorem wrong_step_scaling (c : ℝ) (hc : 0 < c) (η : ℝ) (x g : E) :
    c • (c⁻¹ • x - η • (c • g)) = x - (c ^ 2 * η) • g := by
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  congr 1
  congr 1
  ring

theorem scaled_eta_positive (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (t : ℕ) (hη : 0 < η t) :
    0 < scaledEta c η t := by
  exact div_pos hη (sq_pos_of_pos hc)

theorem history_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    history V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t = fun i => c⁻¹ • history V η loss x₁ p t i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [history_succ, history_succ]
    simp only [output, selected, ih, scaledPolicy, inverse_loss c hc,
      smul_inv_smul₀ hc.ne', V, BanditRL.OnlineHuber.project_fullSpace, scaledEta]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      simpa only [output, selected] using
        (step_scaling c hc (η t) (output V η loss x₁ p t)
          (selected V η loss x₁ p t)).symm
    · simp only [Fin.snoc_castSucc]

theorem output_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    output V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t = c⁻¹ • output V η loss x₁ p t := by
  exact congrArg (fun h : Fin (t + 1) → E => h (Fin.last t))
    (history_scaling c hc η loss x₁ p t)

theorem selected_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    selected V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t = c • selected V η loss x₁ p t := by
  simp only [selected, scaledPolicy, history_scaling c hc,
    inverse_loss c hc, smul_inv_smul₀ hc.ne']

theorem legal_feedback_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) (hproper : ∀ t < T, SourceProper (loss t)) (hlegal : LegalFeedback V η loss x₁ p T) :
    LegalFeedback V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) T := by
  intro t ht
  rw [selected_scaling c hc]
  apply subgradient_scaled c hc (loss t) (hproper t ht)
  simpa only [output_scaling c hc, smul_inv_smul₀ hc.ne'] using hlegal t ht

theorem loss_value_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    scaledLoss c (loss t) (output V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t) = loss t (output V η loss x₁ p t) := by
  simp only [scaledLoss, output_scaling c hc, smul_inv_smul₀ hc.ne']

theorem regret_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (u : E) (T : ℕ) :
    regret V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) (c⁻¹ • u) T = regret V η loss x₁ p u T := by
  unfold regret
  apply sum_congr rfl
  intro t ht
  rw [loss_value_scaling c hc]
  simp only [scaledLoss, smul_inv_smul₀ hc.ne']

theorem wrong_step_output (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    c • output V η (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t = output V (fun s => c ^ 2 * η s) loss x₁ p t := by
  have hη : scaledEta c (fun s => c ^ 2 * η s) = η := by
    funext s
    apply (div_eq_iff (pow_ne_zero 2 hc.ne')).mpr
    ring
  have ho := output_scaling c hc (fun s => c ^ 2 * η s) loss x₁ p t
  rw [hη] at ho
  rw [ho, smul_inv_smul₀ hc.ne']

theorem distance_square_scaling (c : ℝ) (hc : 0 < c) (x u : E) :
    ‖c⁻¹ • x - c⁻¹ • u‖ ^ 2 = ‖x - u‖ ^ 2 / c ^ 2 := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), mul_pow]
  simp only [inv_pow, div_eq_mul_inv]
  ring

theorem energy_scaling (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) :
    (∑ t ∈ range T, ‖selected V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t‖ ^ 2) = c ^ 2 * (∑ t ∈ range T, ‖selected V η loss x₁ p t‖ ^ 2) := by
  simp only [selected_scaling c hc, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, mul_pow]
  rw [mul_sum]

theorem upper_bound_scaling (c : ℝ) (hc : 0 < c) (A B η : ℝ) (hη : 0 < η) :
    BanditRL.OnlineOptimalStep.upperBound (A / c ^ 2) (c ^ 2 * B) (η / c ^ 2) = BanditRL.OnlineOptimalStep.upperBound A B η := by
  unfold BanditRL.OnlineOptimalStep.upperBound
  field_simp
  <;> ring

theorem regret_fixed_scaled (c : ℝ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) :
    regret V (scaledEta c (fun _ => η)) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) (c⁻¹ • u) T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) - ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η) := by
  rw [regret_scaling c hc]
  exact BanditRL.OnlineSubgradientPolicy.regret_fixed V η hη loss x₁ p
    (Set.mem_univ _) T hloss hlegal u (Set.mem_univ _)

end BanditRL.OnlineUnitScaling
