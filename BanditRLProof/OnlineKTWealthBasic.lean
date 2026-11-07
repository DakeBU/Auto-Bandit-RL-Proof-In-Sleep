import BanditRLProof.OnlineKTPotential
import Mathlib

open Finset
namespace BanditRL.OnlineKT
noncomputable section

def ktPrefix (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, c i

def ktWealth (ε : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => ε
  | n + 1 => ktWealth ε c n * (1 + c n * ktPrefix c n / ((n : ℝ) + 1))

theorem ktPrefix_succ (c : ℕ → ℝ) (n : ℕ) :
  ktPrefix c (n + 1) = ktPrefix c n + c n := by
  simp only [ktPrefix, Finset.sum_range_succ]

end
end BanditRL.OnlineKT
