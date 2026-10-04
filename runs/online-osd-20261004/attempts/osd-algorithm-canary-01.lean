import BanditRLProof.OnlineSubgradientAbsolute
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
  change (w - (-1)) * ((-4 : ℝ) - (-1)) ≤ 0
  nlinarith [hw.1]
theorem arbitrary_current_and_actual_clipping :
    (2 : ℝ) ∉ interval.carrier ∧
    BanditRL.OnlineGradientDescent.project interval ((2 : ℝ) - (2 : ℝ) • (3 : ℝ)) = -1 ∧
    (2 * ((linearLoss 2).toReal - (linearLoss 0).toReal) ≤
      2 * inner ℝ (3 : ℝ) ((2 : ℝ) - 0) ∧
    2 * inner ℝ (3 : ℝ) ((2 : ℝ) - 0) ≤
      ‖(2 : ℝ) - 0‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project interval ((2 : ℝ) - (2 : ℝ) • (3 : ℝ)) - 0‖ ^ 2 / 2 +
      (2 : ℝ) ^ 2 / 2 * ‖(3 : ℝ)‖ ^ 2) := by
  refine ⟨by norm_num [interval], ?_, ?_⟩
  · simpa only [smul_eq_mul, show (2 : ℝ) - 2 * 3 = -4 by norm_num] using project_neg_four
  · exact lemma_2_31 interval linearLoss linear_on 2 (by norm_num) 2 0
      (by norm_num [interval]) 3 support_at_two
#print axioms arbitrary_current_and_actual_clipping
end OSDOutsideProbe

namespace OSDAlgorithmProbe
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineSubgradientDescent
open scoped InnerProductSpace
abbrev interval := OSDOutsideProbe.interval
def absoluteLoss (x : ℝ) : EReal := ((|x| : ℝ) : EReal)
def losses : ℕ → ℝ → EReal := fun _ => absoluteLoss

theorem absolute_on : SubdifferentiableOn interval absoluteLoss := by
  refine ⟨⟨fun _ => EReal.coe_ne_bot _, 0, 0, by simp [absoluteLoss]⟩, ?_⟩
  intro x hx
  change (SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) x).Nonempty
  by_cases hp : 0 < x
  · rw [abs_subgradient_positive x hp]
    exact singleton_nonempty 1
  · by_cases hz : x = 0
    · subst x
      rw [abs_subgradient_zero]
      exact ⟨0, by norm_num⟩
    · rw [abs_subgradient_negative x (lt_of_le_of_ne (le_of_not_gt hp) hz)]
      exact singleton_nonempty (-1)

theorem chosen_positive : currentSubgradient absoluteLoss (1 : ℝ) = 1 := by
  have hg := currentSubgradient_mem interval absoluteLoss absolute_on 1 (by norm_num [interval, OSDOutsideProbe.interval])
  change currentSubgradient absoluteLoss 1 ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) 1 at hg
  rw [abs_subgradient_positive 1 (by norm_num)] at hg
  exact hg

theorem chosen_negative : currentSubgradient absoluteLoss (-1 : ℝ) = -1 := by
  have hg := currentSubgradient_mem interval absoluteLoss absolute_on (-1) (by norm_num [interval, OSDOutsideProbe.interval])
  change currentSubgradient absoluteLoss (-1) ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) (-1) at hg
  rw [abs_subgradient_negative (-1) (by norm_num)] at hg
  exact hg

theorem chosen_norm (x : ℝ) (hx : x ∈ interval.carrier) :
    ‖currentSubgradient absoluteLoss x‖ ≤ 1 := by
  have hg := currentSubgradient_mem interval absoluteLoss absolute_on x hx
  change currentSubgradient absoluteLoss x ∈ SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) x at hg
  by_cases hp : 0 < x
  · rw [abs_subgradient_positive x hp] at hg
    have he : currentSubgradient absoluteLoss x = 1 := hg
    rw [he]; norm_num
  · by_cases hz : x = 0
    · subst x
      rw [abs_subgradient_zero] at hg
      change |currentSubgradient absoluteLoss 0| ≤ 1
      exact abs_le.mpr hg
    · rw [abs_subgradient_negative x (lt_of_le_of_ne (le_of_not_gt hp) hz)] at hg
      have he : currentSubgradient absoluteLoss x = -1 := hg
      rw [he]; norm_num

theorem project_neg_two : BanditRL.OnlineGradientDescent.project interval (-2 : ℝ) = -1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval (-2) (-1) (by norm_num [interval, OSDOutsideProbe.interval])
  intro w hw
  change w ∈ Icc (-1 : ℝ) 1 at hw
  change (w - (-1)) * ((-2 : ℝ) - (-1)) ≤ 0
  nlinarith [hw.1]

theorem project_two : BanditRL.OnlineGradientDescent.project interval (2 : ℝ) = 1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval 2 1 (by norm_num [interval, OSDOutsideProbe.interval])
  intro w hw
  change w ∈ Icc (-1 : ℝ) 1 at hw
  change (w - 1) * ((2 : ℝ) - 1) ≤ 0
  nlinarith [hw.2]

theorem project_one : BanditRL.OnlineGradientDescent.project interval (1 : ℝ) = 1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval 1 1 (by norm_num [interval, OSDOutsideProbe.interval])
  intro w hw
  simp

theorem fixed_first : iterate interval (fun _ => (3 : ℝ)) losses 1 1 = -1 := by
  change BanditRL.OnlineGradientDescent.project interval (1 - (3 : ℝ) • currentSubgradient absoluteLoss 1) = -1
  rw [chosen_positive]
  simpa only [smul_eq_mul, show (1 : ℝ) - 3 * 1 = -2 by norm_num] using project_neg_two

theorem fixed_second : iterate interval (fun _ => (3 : ℝ)) losses 1 2 = 1 := by
  change step interval 3 absoluteLoss (iterate interval (fun _ => (3 : ℝ)) losses 1 1) = 1
  rw [fixed_first]
  unfold step
  rw [chosen_negative]
  simpa only [smul_eq_mul, show (-1 : ℝ) - 3 * (-1) = 2 by norm_num] using project_two

theorem fixed_clipped_two_round :
    iterate interval (fun _ => (3 : ℝ)) losses 1 0 = 1 ∧
    iterate interval (fun _ => (3 : ℝ)) losses 1 1 = -1 ∧
    iterate interval (fun _ => (3 : ℝ)) losses 1 2 = 1 ∧
    regret interval (fun _ => (3 : ℝ)) losses 1 0 2 = 2 ∧
    (1 : ℝ) - (3 : ℝ) • currentSubgradient absoluteLoss 1 = -2 ∧
    (-1 : ℝ) - (3 : ℝ) • currentSubgradient absoluteLoss (-1) = 2 := by
  refine ⟨rfl, fixed_first, fixed_second, ?_, ?_, ?_⟩
  · norm_num [regret, sum_range_succ, fixed_first, iterate, losses, absoluteLoss]
  · rw [chosen_positive]; norm_num
  · rw [chosen_negative]; norm_num

theorem fixed_bound_with_terminal :
    regret interval (fun _ => (3 : ℝ)) losses 1 0 2 ≤
      ‖(1 : ℝ) - 0‖ ^ 2 / (2 * 3) +
      (3 : ℝ) / 2 * (∑ t ∈ range 2,
        ‖currentSubgradient (losses t) (iterate interval (fun _ => (3 : ℝ)) losses 1 t)‖ ^ 2) -
      ‖iterate interval (fun _ => (3 : ℝ)) losses 1 2 - 0‖ ^ 2 / (2 * 3) := by
  exact regret_fixed interval 3 (by norm_num) losses 1
    (by norm_num [interval, OSDOutsideProbe.interval]) 2 (fun t ht => absolute_on) 0
    (by norm_num [interval, OSDOutsideProbe.interval])

theorem fixed_terminal_positive :
    ‖iterate interval (fun _ => (3 : ℝ)) losses 1 2 - 0‖ ^ 2 / (2 * 3) = (1 : ℝ) / 6 := by
  rw [fixed_second]; norm_num

def variableEta (t : ℕ) : ℝ := if t = 0 then 3 else 2

theorem variable_first : iterate interval variableEta losses 1 1 = -1 := by
  change step interval (variableEta 0) absoluteLoss 1 = -1
  simpa only [iterate, losses, variableEta, if_pos rfl] using fixed_first

theorem variable_second : iterate interval variableEta losses 1 2 = 1 := by
  change step interval (variableEta 1) absoluteLoss (iterate interval variableEta losses 1 1) = 1
  rw [variable_first]
  simp only [variableEta, if_neg (by omega : (1 : ℕ) ≠ 0), step, chosen_negative, smul_eq_mul]
  convert project_one using 1 <;> norm_num

theorem diameter_two : ∀ x ∈ interval.carrier, ∀ y ∈ interval.carrier, ‖x - y‖ ≤ (2 : ℝ) := by
  intro x hx y hy
  change x ∈ Icc (-1 : ℝ) 1 at hx
  change y ∈ Icc (-1 : ℝ) 1 at hy
  change |x - y| ≤ 2
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

theorem variable_bound_with_terminal :
    regret interval variableEta losses 1 0 2 ≤ (2 : ℝ) ^ 2 / (2 * variableEta (2 - 1)) +
      (∑ t ∈ range 2, variableEta t / 2 *
        ‖currentSubgradient (losses t) (iterate interval variableEta losses 1 t)‖ ^ 2) -
      ‖iterate interval variableEta losses 1 2 - 0‖ ^ 2 / (2 * variableEta (2 - 1)) := by
  apply regret_variable_bound interval variableEta losses 1
    (by norm_num [interval, OSDOutsideProbe.interval]) 2 (by omega)
    (fun t ht => by unfold variableEta; split_ifs <;> norm_num)
    (fun t ht => by have he : t = 0 := by omega; subst t; norm_num [variableEta])
    (fun t ht => absolute_on) 2 diameter_two 0 (by norm_num [interval, OSDOutsideProbe.interval])

theorem variable_nonconstant_and_terminal :
    variableEta 0 = 3 ∧ variableEta 1 = 2 ∧
    iterate interval variableEta losses 1 1 = -1 ∧
    iterate interval variableEta losses 1 2 = 1 ∧
    ‖iterate interval variableEta losses 1 2 - 0‖ ^ 2 / (2 * variableEta (2 - 1)) = (1 : ℝ) / 4 := by
  refine ⟨by norm_num [variableEta], by norm_num [variableEta], variable_first, variable_second, ?_⟩
  rw [variable_second]; norm_num [variableEta]

theorem tuned_all_comparators (T : ℕ) (hT : 0 < T) :
    ∀ u ∈ interval.carrier,
      regret interval (fun _ => (2 : ℝ) / (1 * Real.sqrt T)) losses 1 u T ≤
        2 * 1 * Real.sqrt T := by
  apply regret_tuned interval losses 1 (by norm_num [interval, OSDOutsideProbe.interval])
    T hT 2 1 (by norm_num) (by norm_num) diameter_two (fun t ht => absolute_on)
  intro t ht
  exact chosen_norm _ (iterate_mem interval _ losses 1 (by norm_num [interval, OSDOutsideProbe.interval]) t)

def futureEta (s : ℕ) : ℝ := if s < 2 then 3 else -99
def futureLoss (s : ℕ) : ℝ → EReal := if s < 2 then absoluteLoss else fun _ => ⊤

theorem future_inputs_do_not_change_output : iterate interval futureEta futureLoss 1 2 = 1 := by
  have he := iterate_prefix interval (fun _ => (3 : ℝ)) futureEta losses futureLoss 1 2
    (fun s hs => by simp [futureEta, hs]) (fun s hs => by simp [futureLoss, losses, hs])
  rw [← he]
  exact fixed_second

theorem zero_horizon : regret interval (fun _ => (3 : ℝ)) losses 1 0 0 = 0 ∧
    regret interval (fun _ => (3 : ℝ)) losses 1 0 0 ≤
      ‖(1 : ℝ) - 0‖ ^ 2 / (2 * 3) + (3 : ℝ) / 2 *
        (∑ t ∈ range 0, ‖currentSubgradient (losses t) (iterate interval (fun _ => (3 : ℝ)) losses 1 t)‖ ^ 2) -
      ‖iterate interval (fun _ => (3 : ℝ)) losses 1 0 - 0‖ ^ 2 / (2 * 3) := by
  refine ⟨by simp [regret], ?_⟩
  exact regret_fixed interval 3 (by norm_num) losses 1
    (by norm_num [interval, OSDOutsideProbe.interval]) 0 (fun t ht => by omega) 0
    (by norm_num [interval, OSDOutsideProbe.interval])

#print axioms absolute_on
#print axioms chosen_norm
#print axioms fixed_clipped_two_round
#print axioms fixed_bound_with_terminal
#print axioms fixed_terminal_positive
#print axioms variable_bound_with_terminal
#print axioms variable_nonconstant_and_terminal
#print axioms tuned_all_comparators
#print axioms future_inputs_do_not_change_output
#print axioms zero_horizon
end OSDAlgorithmProbe
