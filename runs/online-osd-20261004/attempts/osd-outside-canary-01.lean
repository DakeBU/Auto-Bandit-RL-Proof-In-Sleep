import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineGradientDescentVariable
import BanditRLProof.OnlineLipschitzSubgradient
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineSubgradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
/-- Source Definition2.20 properness precedes its subdifferentiability convention. -/
def SubdifferentiableOn (V : Domain (E := E)) (f : E → EReal) : Prop :=
  SourceProper f ∧ ∀ x ∈ V.carrier, (SourceSubdifferential f x).Nonempty
/-- Current function/point only; no comparator, horizon or future losses. -/
def currentSubgradient (f : E → EReal) (x : E) : E :=
  by
    classical
    exact if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)
theorem lemma_2_31 (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x) :
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hxdom : x ∈ effectiveDomain f := subgradient_point_finite f hf.1 x g hg
  obtain ⟨gu, hgu⟩ := hf.2 u hu
  have hudom : u ∈ effectiveDomain f := subgradient_point_finite f hf.1 u gu hgu
  have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hf.1.1 x)
  have huv := EReal.coe_toReal (ne_of_lt hudom) (hf.1.1 u)
  have hsupport := hg u
  rw [← hxv, ← huv, ← EReal.coe_add] at hsupport
  have hsupportR := EReal.coe_le_coe_iff.mp hsupport
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hsupportR
  have hgap : (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u) := by linarith
  refine ⟨mul_le_mul_of_nonneg_left hgap hη.le, ?_⟩
  have hp := BanditRL.OnlineGradientDescent.proposition_2_11 V (x - η • g) u hu
  have he : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 -
      2 * η * inner ℝ g (x - u) + η ^ 2 * ‖g‖ ^ 2 := by
    rw [show x - η • g - u = (x - u) - η • g by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (x - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hs : ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 ≤
      ‖x - η • g - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  nlinarith

#print axioms lemma_2_31
end BanditRL.OnlineSubgradientDescent

namespace OSDOutsideProbe
open Set BanditRL.OnlineConvex BanditRL.OnlineSubgradientDescent
def interval : BanditRL.OnlineGradientDescent.Domain ℝ where
  carrier := Icc (-1) 1
  nonempty := ⟨0, by norm_num⟩
  closed := isClosed_Icc
  convex := convex_Icc (-1) 1
def linearLoss (x : ℝ) : EReal := ((inner ℝ (3 : ℝ) x + 0 : ℝ) : EReal)
theorem linear_on : SubdifferentiableOn interval linearLoss := by
  refine ⟨affine_proper (3 : ℝ) 0, ?_⟩
  intro x hx
  refine ⟨3, ?_⟩
  change (3 : ℝ) ∈ SourceSubdifferential (fun y => ((inner ℝ (3 : ℝ) y + 0 : ℝ) : EReal)) x
  rw [affine_subdifferential]
  exact mem_singleton _
theorem support_at_two : (3 : ℝ) ∈ SourceSubdifferential linearLoss 2 := by
  change (3 : ℝ) ∈ SourceSubdifferential (fun y => ((inner ℝ (3 : ℝ) y + 0 : ℝ) : EReal)) 2
  rw [affine_subdifferential]
  exact mem_singleton _
theorem project_neg_four : BanditRL.OnlineGradientDescent.project interval (-4) = -1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval (-4) (-1) (by norm_num [interval])
  intro w hw
  change w ∈ Icc (-1 : ℝ) 1 at hw
  change (w + 1) * (-4 + 1) ≤ 0
  nlinarith [hw.1]
theorem arbitrary_current_and_actual_clipping :
    (2 : ℝ) ∉ interval.carrier ∧
    BanditRL.OnlineGradientDescent.project interval ((2 : ℝ) - 2 • (3 : ℝ)) = -1 ∧
    (2 * ((linearLoss 2).toReal - (linearLoss 0).toReal) ≤
      2 * inner ℝ (3 : ℝ) ((2 : ℝ) - 0) ∧
    2 * inner ℝ (3 : ℝ) ((2 : ℝ) - 0) ≤
      ‖(2 : ℝ) - 0‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project interval ((2 : ℝ) - 2 • (3 : ℝ)) - 0‖ ^ 2 / 2 +
      (2 : ℝ) ^ 2 / 2 * ‖(3 : ℝ)‖ ^ 2) := by
  refine ⟨by norm_num [interval], ?_, ?_⟩
  · simpa using project_neg_four
  · exact lemma_2_31 interval linearLoss linear_on 2 (by norm_num) 2 0
      (by norm_num [interval]) 3 support_at_two
#print axioms arbitrary_current_and_actual_clipping
end OSDOutsideProbe
