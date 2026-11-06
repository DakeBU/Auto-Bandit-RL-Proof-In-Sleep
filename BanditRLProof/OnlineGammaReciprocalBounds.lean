import BanditRLProof.OnlineGammaDerivatives
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory
namespace BanditRL.OnlineGamma

private theorem reciprocal_cell_log_bounds (u : ℝ) (hu : 0 < u) :
    1 / (u + 1) ≤ Real.log (u + 1) - Real.log u ∧
    Real.log (u + 1) - Real.log u ≤ (1 / u + 1 / (u + 1)) / 2 := by
  have hu1 : 0 < u + 1 := by linarith
  have hab : u ≤ u + 1 := by linarith
  have hf : IntervalIntegrable (fun t : ℝ => 1 / t) volume u (u + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_const.div continuousOn_id (fun t ht => (hu.trans_le ht.1).ne')
  let g : ℝ → ℝ := fun t => (u + 1 - t) / u + (t - u) / (u + 1)
  have hl : IntervalIntegrable (fun t : ℝ => (u + 1 - t) / u) volume u (u + 1) :=
    ((continuous_const.sub continuous_id).div_const u).intervalIntegrable _ _
  have hr : IntervalIntegrable (fun t : ℝ => (t - u) / (u + 1)) volume u (u + 1) :=
    ((continuous_id.sub continuous_const).div_const (u + 1)).intervalIntegrable _ _
  have hg : IntervalIntegrable g volume u (u + 1) := hl.add hr
  have hchord (t : ℝ) (ht : t ∈ Set.Icc u (u + 1)) : 1 / t ≤ g t := by
    have htpos : 0 < t := hu.trans_le ht.1
    have hid : g t - 1 / t = (t - u) * (u + 1 - t) / (u * (u + 1) * t) := by
      dsimp [g]
      field_simp [hu.ne', hu1.ne', htpos.ne']
      <;> ring
    have hn : 0 ≤ (t - u) * (u + 1 - t) / (u * (u + 1) * t) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2))
        (mul_pos (mul_pos hu hu1) htpos).le
    linarith
  have hlow := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / (u + 1)) volume u (u + 1)) hf
    (fun t ht => one_div_le_one_div_of_le (hu.trans_le ht.1) ht.2)
  have hupp := intervalIntegral.integral_mono_on hab hf hg hchord
  have hlog : (∫ t in u..u + 1, (1 : ℝ) / t) = Real.log (u + 1) - Real.log u := by
    rw [integral_one_div_of_pos hu hu1, Real.log_div hu1.ne' hu.ne']
  have hgintegral : (∫ t in u..u + 1, g t) = (1 / u + 1 / (u + 1)) / 2 := by
    dsimp [g]
    rw [intervalIntegral.integral_add hl hr, intervalIntegral.integral_div,
      intervalIntegral.integral_div,
      intervalIntegral.integral_sub (f := fun _ : ℝ => u + 1) (g := fun t : ℝ => t)
        intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => u)
        (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
    field_simp [hu.ne', hu1.ne']
    <;> ring
  rw [hlog] at hlow hupp
  rw [hgintegral] at hupp
  have hconstant : (∫ _ : ℝ in u..u + 1, 1 / (u + 1)) = 1 / (u + 1) := by simp
  rw [hconstant] at hlow
  exact ⟨hlow, hupp⟩

theorem reciprocal_prefix_log_bounds :
  ∀ (x : ℝ) (N : ℕ), 0 < x →
    Real.log (x + (N : ℝ)) - Real.log x +
        (1 / x - 1 / (x + (N : ℝ))) / 2 ≤
      ∑ k ∈ Finset.range N, 1 / (x + (k : ℝ)) ∧
    (∑ k ∈ Finset.range N, 1 / (x + (k : ℝ))) ≤
      Real.log (x + (N : ℝ)) - Real.log x + 1 / x - 1 / (x + (N : ℝ)) := by
  intro x N hx
  induction N with
  | zero => simp
  | succ N ih =>
    have hu : 0 < x + (N : ℝ) := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg N)
    have hc := reciprocal_cell_log_bounds (x + (N : ℝ)) hu
    have harg : x + ((N + 1 : ℕ) : ℝ) = (x + (N : ℝ)) + 1 := by push_cast; ring
    simp only [Finset.sum_range_succ]
    change Real.log (x + ((N + 1 : ℕ) : ℝ)) - Real.log x +
        (1 / x - 1 / (x + ((N + 1 : ℕ) : ℝ))) / 2 ≤
      (∑ k ∈ Finset.range N, 1 / (x + (k : ℝ))) + 1 / (x + (N : ℝ)) ∧
      (∑ k ∈ Finset.range N, 1 / (x + (k : ℝ))) + 1 / (x + (N : ℝ)) ≤
        Real.log (x + ((N + 1 : ℕ) : ℝ)) - Real.log x + 1 / x - 1 / (x + ((N + 1 : ℕ) : ℝ))
    rw [harg]
    constructor <;> linarith [ih.1, ih.2, hc.1, hc.2]

end BanditRL.OnlineGamma
