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

end BanditRL.OnlineUnitScaling
