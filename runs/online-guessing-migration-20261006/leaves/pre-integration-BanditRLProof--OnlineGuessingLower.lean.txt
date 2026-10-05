import BanditRLProof.OnlineGuessingOGD

noncomputable section
open Set Finset
namespace BanditRL.OnlineGradientDescent

theorem guessing_zero_trajectory (n : ℕ) (hn : 0 < n) (t : ℕ) :
    iterate unitInterval (1/(4*(n:ℝ))) (fun _ x => (x-0)^2) 1 t =
      (1 - 1/(2*(n:ℝ)))^t := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hr0 : 0 ≤ 1 - 1/(2*(n:ℝ)) := by
    have hh : 1/(2*(n:ℝ)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hr1 : 1 - 1/(2*(n:ℝ)) ≤ 1 := by
    have hp : (0:ℝ) ≤ 1/(2*(n:ℝ)) := by positivity
    linarith
  induction t with
  | zero => simp [iterate]
  | succ t ih =>
    change step unitInterval (1/(4*(n:ℝ))) (fun x : ℝ => (x-0)^2)
      (iterate unitInterval (1/(4*(n:ℝ))) (fun _ x => (x-0)^2) 1 t) = _
    rw [ih, square_step_clamp]
    have he : (1-1/(2*(n:ℝ)))^t - 2*(1/(4*(n:ℝ)))*((1-1/(2*(n:ℝ)))^t-0) =
        (1-1/(2*(n:ℝ)))^(t+1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [he, max_eq_left (pow_nonneg hr0 _), min_eq_left (pow_le_one₀ hr0 hr1)]

theorem guessing_tuned_eta_square (n : ℕ) :
    1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)) = 1/(4*(n:ℝ)) := by
  push_cast
  rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2*(n:ℝ))]
  ring

theorem guessing_squared_horizon_lower (n : ℕ) (hn : 0 < n) :
    (n:ℝ)/4 ≤ regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
      (fun _ x => (x-0)^2) 1 0 ((2*n)^2) := by
  rw [guessing_tuned_eta_square]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2*(n:ℝ) := by positivity
  have hpow (t : ℕ) (ht : t < n) : (1:ℝ)/2 ≤ (1-1/(2*(n:ℝ)))^t := by
    have hlo : (-2:ℝ) ≤ -(1/(2*(n:ℝ))) := by
      have hh : 1/(2*(n:ℝ)) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
      linarith
    have hb := one_add_mul_le_pow hlo t
    have htR : (t:ℝ) ≤ n := by exact_mod_cast ht.le
    have hfrac : (t:ℝ)/(2*(n:ℝ)) ≤ 1/2 := (div_le_iff₀ hden).mpr (by linarith)
    have he : (t:ℝ) * -(1/(2*(n:ℝ))) = -(t/(2*(n:ℝ))) := by ring
    rw [he] at hb
    change 1 - (t:ℝ)/(2*(n:ℝ)) ≤ (1-1/(2*(n:ℝ)))^t at hb
    linarith
  have hsub : range n ⊆ range ((2*n)^2) := by
    apply range_mono
    nlinarith
  calc
    (n:ℝ)/4 = ∑ _t ∈ range n, (1/4:ℝ) := by simp; ring
    _ ≤ ∑ t ∈ range n, (iterate unitInterval (1/(4*(n:ℝ))) (fun _ x => (x-0)^2) 1 t)^2 := by
      apply sum_le_sum
      intro t ht
      rw [guessing_zero_trajectory n hn t]
      have hb := hpow t (mem_range.mp ht)
      nlinarith
    _ ≤ ∑ t ∈ range ((2*n)^2), (iterate unitInterval (1/(4*(n:ℝ))) (fun _ x => (x-0)^2) 1 t)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t ht ht' => sq_nonneg _)
    _ = _ := by simp [regret]
end BanditRL.OnlineGradientDescent
