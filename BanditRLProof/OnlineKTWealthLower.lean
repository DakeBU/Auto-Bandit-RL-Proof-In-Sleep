import BanditRLProof.OnlineKTWealthBasic
import BanditRLProof.OnlineKTInterpolation
import Mathlib

open Finset
namespace BanditRL.OnlineKT
noncomputable section

theorem ktPotential_le_wealth (ε : ℝ) (hε : 0 < ε) (c : ℕ → ℝ) (n : ℕ)
    (hc : ∀ i < n, |c i| ≤ 1) :
  ktPotential ε n (ktPrefix c n) ≤ ktWealth ε c n := by
  have prefix_bound (m : ℕ) (hm : ∀ i < m, |c i| ≤ 1) : |ktPrefix c m| ≤ (m : ℝ) := by
    calc
      |ktPrefix c m| ≤ ∑ i ∈ range m, |c i| := Finset.abs_sum_le_sum_abs c (range m)
      _ ≤ ∑ _i ∈ range m, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => hm i (Finset.mem_range.mp hi))
      _ = (m : ℝ) := by simp
  revert hc
  induction n with
  | zero =>
    intro hc
    simpa [ktPrefix, ktWealth] using (ktPotential_initial ε).le
  | succ n ih =>
    intro hc
    have hcprev : ∀ i < n, |c i| ≤ 1 :=
      fun i hi => hc i (Nat.lt_trans hi (Nat.lt_succ_self n))
    have hcn : |c n| ≤ 1 := hc n (Nat.lt_succ_self n)
    have hpref := prefix_bound n hcprev
    have hprod : |c n * ktPrefix c n| ≤ (n : ℝ) := by
      calc
        |c n * ktPrefix c n| = |c n| * |ktPrefix c n| := abs_mul _ _
        _ ≤ 1 * |ktPrefix c n| := mul_le_mul_of_nonneg_right hcn (abs_nonneg _)
        _ ≤ (n : ℝ) := by simpa only [one_mul] using hpref
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hdiv : -1 ≤ c n * ktPrefix c n / ((n : ℝ) + 1) :=
      (le_div_iff₀ hden).2 (by have h := (abs_le.mp hprod).1; linarith)
    have hfactor : 0 ≤ 1 + c n * ktPrefix c n / ((n : ℝ) + 1) := by linarith
    have hstep : ktPotential ε (n + 1) (ktPrefix c n + c n) ≤
        (1 + c n * ktPrefix c n / ((n : ℝ) + 1)) * ktPotential ε n (ktPrefix c n) := by
      have h := ktPotential_interpolate ε hε (n + 1) (by omega) (ktPrefix c n) (c n)
        (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hpref) hcn
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h
    calc
      ktPotential ε (n + 1) (ktPrefix c (n + 1)) ≤
          (1 + c n * ktPrefix c n / ((n : ℝ) + 1)) * ktPotential ε n (ktPrefix c n) := by
        simpa only [ktPrefix_succ] using hstep
      _ ≤ (1 + c n * ktPrefix c n / ((n : ℝ) + 1)) * ktWealth ε c n :=
        mul_le_mul_of_nonneg_left (ih hcprev) hfactor
      _ = ktWealth ε c (n + 1) := by
        change (1 + c n * ktPrefix c n / ((n : ℝ) + 1)) * ktWealth ε c n =
          ktWealth ε c n * (1 + c n * ktPrefix c n / ((n : ℝ) + 1))
        ring

end
end BanditRL.OnlineKT
