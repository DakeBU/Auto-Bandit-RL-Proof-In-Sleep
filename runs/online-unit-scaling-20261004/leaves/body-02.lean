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

end BanditRL.OnlineUnitScaling
