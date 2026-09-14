import BanditRLProof.OnlineGradientDescent
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section
open Set Finset
open scoped InnerProductSpace

namespace BanditRL.OnlineGradientDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algorithm 2.1 with a prescribed schedule: source round t+1 is Lean t. -/
def iterateVariable (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterateVariable V η loss x₁ t)

/-- Regret uses exactly the variable-step trajectory, with no comparator input to the policy. -/
def regretVariable (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ)
    (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, (loss t (iterateVariable V η loss x₁ t) - loss t u)

theorem iterateVariable_mem (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) : iterateVariable V η loss x₁ t ∈ V.carrier := by
  cases t with
  | zero => exact hx₁
  | succ t => exact (project_spec V _).1

theorem iterateVariable_prefix (V : Domain E) (η : ℕ → ℝ) (loss loss' : ℕ → E → ℝ)
    (x₁ : E) (t : ℕ) (h : ∀ s < t, loss s = loss' s) :
    iterateVariable V η loss x₁ t = iterateVariable V η loss' x₁ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iterateVariable, h t (Nat.lt_succ_self t),
      ih (fun s hs => h s (Nat.lt_succ_of_lt hs))]

theorem variable_one_step (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (hη : 0 < η t)
    (hloss : RegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    loss t (iterateVariable V η loss x₁ t) - loss t u ≤
      (‖iterateVariable V η loss x₁ t - u‖ ^ 2 -
        ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2 := by
  have hs := lemma_2_12 V (loss t) hloss (η t) hη
    (iterateVariable V η loss x₁ t) u (iterateVariable_mem V η loss x₁ hx₁ t) hu
  apply le_of_mul_le_mul_left (a := η t) _ hη
  calc
    η t * (loss t (iterateVariable V η loss x₁ t) - loss t u) ≤
        ‖iterateVariable V η loss x₁ t - u‖ ^ 2 / 2 -
        ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2 / 2 +
        (η t) ^ 2 / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2 :=
      hs.1.trans hs.2
    _ = η t * ((‖iterateVariable V η loss x₁ t - u‖ ^ 2 -
        ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
        η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) := by
      field_simp

theorem weighted_potential_sum (a η : ℕ → ℝ) (C : ℝ) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hbound : ∀ t < T, a t ≤ C) :
    (∑ t ∈ range T, (a t - a (t + 1)) / (2 * η t)) ≤
      C / (2 * η (T - 1)) - a T / (2 * η (T - 1)) := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases hz : T = 0
    · subst T
      have hpos := hη 0 (by omega)
      simpa [sub_div] using div_le_div_of_nonneg_right
        (sub_le_sub_right (hbound 0 (by omega)) (a 1))
        (by positivity : 0 ≤ 2 * η 0)
    · have hTpos : 0 < T := Nat.pos_of_ne_zero hz
      have hi := ih hTpos (fun t ht => hη t (Nat.lt_succ_of_lt ht))
        (fun t ht => hmono t (Nat.lt_succ_of_lt ht))
        (fun t ht => hbound t (Nat.lt_succ_of_lt ht))
      have hprev : T - 1 + 1 = T := Nat.sub_add_cancel hTpos
      have hm : η T ≤ η (T - 1) := by
        simpa only [hprev] using hmono (T - 1) (by omega)
      have hpos := hη T (by omega)
      have hd := div_le_div_of_nonneg_left
        (sub_nonneg.mpr (hbound T (by omega)))
        (by positivity : 0 < 2 * η T)
        (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2))
      rw [sum_range_succ]
      simp only [Nat.add_sub_cancel]
      simp only [sub_div] at hd
      calc
        _ ≤ (C / (2 * η (T - 1)) - a T / (2 * η (T - 1))) +
            (a T - a (T + 1)) / (2 * η T) := by linarith
        _ ≤ (C / (2 * η T) - a T / (2 * η T)) +
            (a T - a (T + 1)) / (2 * η T) := by linarith
        _ = _ := by rw [sub_div]; ring

theorem theorem_2_13_variable_bound (V : Domain E) (η : ℕ → ℝ)
    (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, RegularLoss V (loss t)) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier) :
    regretVariable V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) -
      ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  have hp := weighted_potential_sum
    (fun t => ‖iterateVariable V η loss x₁ t - u‖ ^ 2) η (D ^ 2) T hT hη hmono
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _)
      (hdiam _ (iterateVariable_mem V η loss x₁ hx₁ t) u hu) 2)
  have hs := Finset.sum_le_sum (s := range T) (fun t ht =>
    variable_one_step V η loss x₁ hx₁ t (hη t (mem_range.mp ht))
      (hloss t (mem_range.mp ht)) u hu)
  rw [sum_add_distrib] at hs
  change regretVariable V η loss x₁ u T ≤ _ at hs
  linarith

theorem theorem_2_13_variable (V : Domain E) (hV : Bornology.IsBounded V.carrier)
    (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, RegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    regretVariable V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) -
      ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1)) := by
  apply theorem_2_13_variable_bound V η loss x₁ hx₁ T hT hη hmono hloss
    (Metric.diam V.carrier) ?_ u hu
  intro x hx y hy
  simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hV hx hy

end BanditRL.OnlineGradientDescent
