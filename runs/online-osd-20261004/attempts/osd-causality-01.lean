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


theorem currentSubgradient_mem (V : Domain (E := E)) (f : E → EReal)
    (hf : SubdifferentiableOn V f) (x : E) (hx : x ∈ V.carrier) :
    currentSubgradient f x ∈ SourceSubdifferential f x := by
  classical
  have hs := hf.2 x hx
  unfold currentSubgradient
  rw [dif_pos hs]
  exact Classical.choose_spec hs

theorem finite_loss (V : Domain (E := E)) (f : E → EReal)
    (hf : SubdifferentiableOn V f) (x : E) (hx : x ∈ V.carrier) :
    f x = ((f x).toReal : EReal) := by
  have hg := currentSubgradient_mem V f hf x hx
  have hd := subgradient_point_finite f hf.1 x (currentSubgradient f x) hg
  exact (EReal.coe_toReal (ne_of_lt hd) (hf.1.1 x)).symm

theorem iterate_mem (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) :
    iterate V η loss x₁ t ∈ V.carrier := by
  cases t with
  | zero => exact hx₁
  | succ t => exact (BanditRL.OnlineGradientDescent.project_spec V _).1

theorem iterate_prefix (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    iterate V η loss x₁ t = iterate V η' loss' x₁ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iterate, hη t (Nat.lt_succ_self t), hloss t (Nat.lt_succ_self t),
      ih (fun s hs => hη s (Nat.lt_succ_of_lt hs))
        (fun s hs => hloss s (Nat.lt_succ_of_lt hs))]

theorem iterate_support (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : SubdifferentiableOn V (loss t)) :
    currentSubgradient (loss t) (iterate V η loss x₁ t) ∈
      SourceSubdifferential (loss t) (iterate V η loss x₁ t) := by
  exact currentSubgradient_mem V (loss t) hloss _ (iterate_mem V η loss x₁ hx₁ t)

theorem iterate_finite_loss (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    loss t (iterate V η loss x₁ t) = ((loss t (iterate V η loss x₁ t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal) := by
  exact ⟨finite_loss V (loss t) hloss _ (iterate_mem V η loss x₁ hx₁ t),
    finite_loss V (loss t) hloss u hu⟩

theorem one_step_chain (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hη : 0 < η t) (hloss : SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier) :
    η t * ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal) ≤
      η t * inner ℝ (currentSubgradient (loss t) (iterate V η loss x₁ t))
        (iterate V η loss x₁ t - u) ∧
    η t * inner ℝ (currentSubgradient (loss t) (iterate V η loss x₁ t))
        (iterate V η loss x₁ t - u) ≤
      ‖iterate V η loss x₁ t - u‖ ^ 2 / 2 -
      ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2 / 2 +
      (η t) ^ 2 / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2 := by
  simpa only [iterate, step] using lemma_2_31 V (loss t) hloss (η t) hη
    (iterate V η loss x₁ t) u hu
    (currentSubgradient (loss t) (iterate V η loss x₁ t))
    (iterate_support V η loss x₁ hx₁ t hloss)

theorem one_step (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hη : 0 < η t) (hloss : SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier) :
    (loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal ≤
      (‖iterate V η loss x₁ t - u‖ ^ 2 -
        ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2 := by
  have hs := one_step_chain V η loss x₁ hx₁ t hη hloss u hu
  apply le_of_mul_le_mul_left (a := η t) _ hη
  calc
    η t * ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal) ≤
        ‖iterate V η loss x₁ t - u‖ ^ 2 / 2 -
        ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2 / 2 +
        (η t) ^ 2 / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2 :=
      hs.1.trans hs.2
    _ = η t * ((‖iterate V η loss x₁ t - u‖ ^ 2 -
        ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
        η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) := by
      field_simp

#print axioms lemma_2_31
#print axioms currentSubgradient_mem
#print axioms finite_loss
#print axioms iterate_mem
#print axioms iterate_prefix
#print axioms iterate_support
#print axioms iterate_finite_loss
#print axioms one_step_chain
#print axioms one_step
end BanditRL.OnlineSubgradientDescent
