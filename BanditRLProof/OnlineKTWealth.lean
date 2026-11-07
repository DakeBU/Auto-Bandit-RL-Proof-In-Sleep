import BanditRLProof.OnlineKTWealthLower
import BanditRLProof.OnlineKTExponentialLower
import Mathlib

open Finset
namespace BanditRL.OnlineKT
noncomputable section

theorem ktWealth_two_step (ε : ℝ) (hε : 0 < ε) (c : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hc : ∀ i < T, |c i| ≤ 1) :
  ktPotential ε T (ktPrefix c T) ≤ ktWealth ε c T ∧
  ε * Real.exp ((ktPrefix c T)^2 / (2 * (T : ℝ)) - Real.log (T : ℝ) / 2 - 1) ≤
    ktPotential ε T (ktPrefix c T) := by
  have hpref : |ktPrefix c T| ≤ (T : ℝ) := by
    calc
      |ktPrefix c T| ≤ ∑ i ∈ range T, |c i| := Finset.abs_sum_le_sum_abs c (range T)
      _ ≤ ∑ _i ∈ range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => hc i (Finset.mem_range.mp hi))
      _ = (T : ℝ) := by simp
  exact ⟨ktPotential_le_wealth ε hε c T hc,
    ktPotential_exp_lower ε hε T hT (ktPrefix c T) hpref⟩

end
end BanditRL.OnlineKT
