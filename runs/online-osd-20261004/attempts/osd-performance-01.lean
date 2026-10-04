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


theorem regret_fixed (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    regret V (fun _ => η) loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2) -
      ‖iterate V (fun _ => η) loss x₁ T - u‖ ^ 2 / (2 * η) := by
  have hscaled : η * regret V (fun _ => η) loss x₁ u T ≤
      ‖x₁ - u‖ ^ 2 / 2 - ‖iterate V (fun _ => η) loss x₁ T - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2) := by
    induction T with
    | zero => simp [regret, iterate]
    | succ T ih =>
      have hi := ih (fun t ht => hloss t (Nat.lt_succ_of_lt ht))
      have hs := one_step_chain V (fun _ => η) loss x₁ hx₁ T hη
        (hloss T (Nat.lt_succ_self T)) u hu
      simp only [regret, sum_range_succ, mul_add] at hi ⊢
      nlinarith [hs.1.trans hs.2]
  apply le_of_mul_le_mul_left (a := η) _ hη
  calc
    η * regret V (fun _ => η) loss x₁ u T ≤ _ := hscaled
    _ = η * (‖x₁ - u‖ ^ 2 / (2 * η) +
        η / 2 * (∑ t ∈ range T,
          ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2) -
        ‖iterate V (fun _ => η) loss x₁ T - u‖ ^ 2 / (2 * η)) := by field_simp; ring

theorem regret_fixed_coarse (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    regret V (fun _ => η) loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2) := by
  have hb := regret_fixed V η hη loss x₁ hx₁ T hloss u hu
  have ht : 0 ≤ ‖iterate V (fun _ => η) loss x₁ T - u‖ ^ 2 / (2 * η) := by positivity
  linarith

theorem regret_variable_bound (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  have hp := BanditRL.OnlineGradientDescent.weighted_potential_sum
    (fun t => ‖iterate V η loss x₁ t - u‖ ^ 2) η (D ^ 2) T hT hη hmono
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _)
      (hdiam _ (iterate_mem V η loss x₁ hx₁ t) u hu) 2)
  have hs := Finset.sum_le_sum (s := range T) (fun t ht =>
    one_step V η loss x₁ hx₁ t (hη t (mem_range.mp ht))
      (hloss t (mem_range.mp ht)) u hu)
  rw [sum_add_distrib] at hs
  change regret V η loss x₁ u T ≤ _ at hs
  linarith

theorem regret_variable (V : Domain (E := E)) (hV : Bornology.IsBounded V.carrier)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  apply regret_variable_bound V η loss x₁ hx₁ T hT hη hmono hloss
    (Metric.diam V.carrier) ?_ u hu
  intro x hx y hy
  simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hV hx hy

theorem regret_tuned_distance (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T, ‖currentSubgradient (loss t)
      (iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) :
    regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T := by
  have hTreal : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTreal
  have hη : 0 < D / (G * Real.sqrt T) := div_pos hD (mul_pos hG hsqrt)
  have hb := regret_fixed V (D / (G * Real.sqrt T)) hη loss x₁ hx₁ T hloss u hu
  have hdist2 : ‖x₁ - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hsum : (∑ t ∈ range T,
      ‖currentSubgradient (loss t)
        (iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ t)‖ ^ 2) ≤
      (T : ℝ) * G ^ 2 := by
    calc
      _ ≤ ∑ _t ∈ range T, G ^ 2 := sum_le_sum fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _) (hgrad t (mem_range.mp ht)) 2
      _ = _ := by simp
  have hinit := div_le_div_of_nonneg_right hdist2 (by positivity :
    0 ≤ 2 * (D / (G * Real.sqrt T)))
  have henergy := mul_le_mul_of_nonneg_left hsum (by positivity :
    0 ≤ (D / (G * Real.sqrt T)) / 2)
  have hterminal : 0 ≤ ‖iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ T - u‖ ^ 2 /
      (2 * (D / (G * Real.sqrt T))) := by positivity
  have htune : D ^ 2 / (2 * (D / (G * Real.sqrt T))) +
      (D / (G * Real.sqrt T)) / 2 * ((T : ℝ) * G ^ 2) = D * G * Real.sqrt T := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg T)
    field_simp
    nlinarith
  linarith

theorem regret_tuned (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t))
    (hgrad : ∀ t < T, ‖currentSubgradient (loss t)
      (iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) :
    ∀ u ∈ V.carrier,
      regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T := by
  intro u hu
  exact regret_tuned_distance V loss x₁ hx₁ T hT D G hD hG hloss u hu
    (hdiam x₁ hx₁ u hu) hgrad

#print axioms lemma_2_31
#print axioms currentSubgradient_mem
#print axioms finite_loss
#print axioms iterate_mem
#print axioms iterate_prefix
#print axioms iterate_support
#print axioms iterate_finite_loss
#print axioms one_step_chain
#print axioms one_step
#print axioms regret_fixed
#print axioms regret_fixed_coarse
#print axioms regret_variable_bound
#print axioms regret_variable
#print axioms regret_tuned_distance
#print axioms regret_tuned
end BanditRL.OnlineSubgradientDescent
