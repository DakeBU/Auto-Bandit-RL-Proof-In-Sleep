import Mathlib

/-! # Real Gamma estimates for online learning

Midpoint reciprocal-square estimates and finite Euler log-Gamma approximants
used in the proof of Orabona, Appendix A.2, Lemma A.13.
-/

namespace BanditRL.OnlineGamma

open Filter Finset Set

noncomputable section

def midpointInvSq (x : ℝ) (k : ℕ) : ℝ := 1 / (x + (k : ℝ) + 1/2)^2
def reciprocalDifference (x : ℝ) (k : ℕ) : ℝ := 1 / (x + (k : ℝ)) - 1 / (x + (k : ℝ) + 1)

theorem midpointInvSq_le_reciprocalDifference (x : ℝ) (hx : 0 < x) (k : ℕ) :
    midpointInvSq x k ≤ reciprocalDifference x k := by
  let y := x + (k : ℝ)
  have hy : 0 < y := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)
  have hnext : 0 < y + 1 := by positivity
  change 1 / (y + 1 / 2)^2 ≤ 1 / y - 1 / (y + 1)
  calc
    1 / (y + 1 / 2)^2 ≤ 1 / (y * (y + 1)) :=
      one_div_le_one_div_of_le (mul_pos hy hnext) (by nlinarith)
    _ = 1 / y - 1 / (y + 1) := by
      field_simp [hy.ne', hnext.ne'] <;> ring

theorem sum_reciprocalDifference (x : ℝ) (N : ℕ) :
    ∑ k ∈ range N, reciprocalDifference x k = 1/x - 1/(x + (N : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    simp only [reciprocalDifference, Nat.cast_succ, ← add_assoc]
    ring

theorem sum_midpointInvSq_le (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ range N, midpointInvSq x k ≤ 1/x - 1/(x + (N : ℝ)) := by
  calc
    ∑ k ∈ range N, midpointInvSq x k ≤ ∑ k ∈ range N, reciprocalDifference x k :=
      Finset.sum_le_sum (fun k _ => midpointInvSq_le_reciprocalDifference x hx k)
    _ = 1/x - 1/(x + (N : ℝ)) := sum_reciprocalDifference x N
theorem summable_midpointInvSq_and_tsum_le (x : ℝ) (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / (x + (k : ℝ) + 1 / 2)^2) ∧
    (∑' k : ℕ, 1 / (x + (k : ℝ) + 1 / 2)^2) ≤ 1 / x := by
  have hn : ∀ k : ℕ, 0 ≤ midpointInvSq x k := by
    intro k
    unfold midpointInvSq
    positivity
  have hu : ∀ N : ℕ, ∑ k ∈ range N, midpointInvSq x k ≤ 1/x := by
    intro N
    exact (sum_midpointInvSq_le x hx N).trans (sub_le_self _ (by positivity))
  exact ⟨summable_of_sum_range_le hn hu, Real.tsum_le_of_sum_range_le hn hu⟩

noncomputable def logGammaSlopeApprox (N : ℕ) (y : ℝ) : ℝ :=
  Real.log (N : ℝ) - ∑ k ∈ range (N + 1), 1 / (y + (k : ℝ))

noncomputable def logGammaCurvatureApprox (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), 1 / (y + (k : ℝ)) ^ 2

theorem hasDerivAt_logGammaSeq_and_slopeApprox (N : ℕ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.BohrMollerup.logGammaSeq z N) (logGammaSlopeApprox N y) y ∧
    HasDerivAt (logGammaSlopeApprox N) (logGammaCurvatureApprox N y) y := by
  have hpos (k : ℕ) : 0 < y + (k : ℝ) := add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg k)
  have hlog (k : ℕ) :
      HasDerivAt (fun z : ℝ => Real.log (z + (k : ℝ))) (1 / (y + (k : ℝ))) y :=
    ((hasDerivAt_id y).add_const (k : ℝ)).log (hpos k).ne'
  have hinv (k : ℕ) :
      HasDerivAt (fun z : ℝ => 1 / (z + (k : ℝ))) (-(1 / (y + (k : ℝ))^2)) y := by
    simpa [one_div, neg_div, Pi.inv_apply] using
      (((hasDerivAt_id y).add_const (k : ℝ)).inv (hpos k).ne')
  have hlogs := HasDerivAt.fun_sum (u := range (N + 1)) (fun k _ => hlog k)
  have hinvs := HasDerivAt.fun_sum (u := range (N + 1)) (fun k _ => hinv k)
  constructor
  · simpa [Real.BohrMollerup.logGammaSeq, logGammaSlopeApprox] using
      ((((hasDerivAt_id y).mul_const (Real.log (N : ℝ))).add_const (Real.log (Nat.factorial N : ℝ))).sub hlogs)
  · change HasDerivAt (fun z : ℝ => Real.log (N : ℝ) -
        ∑ k ∈ range (N + 1), 1 / (z + (k : ℝ)))
        (logGammaCurvatureApprox N y) y
    simpa [Pi.sub_def, logGammaCurvatureApprox, Finset.sum_neg_distrib] using
      ((hasDerivAt_const y (Real.log (N : ℝ))).sub hinvs)

def compensatedReciprocal (k : ℕ) (y : ℝ) : ℝ :=
  1 / ((k : ℝ) + 1) - 1 / (y + ((k : ℝ) + 1))

def shiftedInvSq (k : ℕ) (y : ℝ) : ℝ :=
  1 / (y + ((k : ℝ) + 1)) ^ 2

theorem tendstoUniformlyOn_compensatedReciprocal_and_shiftedInvSq :
  ∀ (a b : ℝ), 0 < a → a < b →
    TendstoUniformlyOn
      (fun (N : ℕ) (y : ℝ) => ∑ k ∈ range N, compensatedReciprocal k y)
      (fun y : ℝ => ∑' k : ℕ, compensatedReciprocal k y) atTop (Icc a b) ∧
    TendstoUniformlyOn
      (fun (N : ℕ) (y : ℝ) => ∑ k ∈ range N, shiftedInvSq k y)
      (fun y : ℝ => ∑' k : ℕ, shiftedInvSq k y) atTop (Icc a b) := by
  intro a b ha hab
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) 1).2 hbase)
  constructor
  · apply tendstoUniformlyOn_tsum_nat (hshift.mul_left b)
    intro k y hy
    let m : ℝ := (k : ℝ) + 1
    have hm : 0 < m := by dsimp [m]; positivity
    have hypos : 0 ≤ y := (ha.le.trans hy.1)
    have hsum : 0 < y + m := add_pos_of_nonneg_of_pos hypos hm
    have heq : compensatedReciprocal k y = y / (m * (y + m)) := by
      change 1/m - 1/(y+m) = y/(m*(y+m))
      field_simp [hm.ne', hsum.ne'] <;> ring
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hypos (mul_pos hm hsum).le)]
    change y / (m * (y + m)) ≤ b * (1 / m^2)
    calc
      y / (m * (y + m)) ≤ y / m^2 :=
        div_le_div_of_nonneg_left hypos (sq_pos_of_pos hm) (by nlinarith [mul_nonneg hm.le hypos])
      _ ≤ b / m^2 := div_le_div_of_nonneg_right hy.2 (sq_nonneg m)
      _ = b * (1 / m^2) := by ring
  · apply tendstoUniformlyOn_tsum_nat hshift
    intro k y hy
    let m : ℝ := (k : ℝ) + 1
    have hm : 0 < m := by dsimp [m]; positivity
    have hypos : 0 ≤ y := ha.le.trans hy.1
    change ‖(1 : ℝ) / (y+m)^2‖ ≤ 1 / m^2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hm)
      (by nlinarith [mul_nonneg hm.le hypos, sq_nonneg y])

end

end BanditRL.OnlineGamma
