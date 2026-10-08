import BanditRLProof.RealMeanRegretPullCount
import Mathlib.Tactic

namespace BanditRLProof.QuantumQueryAccounting

/-- One arm is fixed for a whole block; forward and inverse calls both count.
This accounting record alone does not implement Born measurements or reset. -/
structure Block (K D : ℕ) where
  arm : Fin K
  forward : ℕ
  inverse : ℕ
  bounded : forward + inverse ≤ D

def Block.queries {K D : ℕ} (b : Block K D) : ℕ := b.forward + b.inverse

def expanded {K D : ℕ} (blocks : List (Block K D)) : List (Fin K) :=
  blocks.flatMap fun b => List.replicate b.queries b.arm

noncomputable def chargedRegret {K D : ℕ} (mean : Fin K → ℝ)
    (blocks : List (Block K D)) : ℝ :=
  (blocks.map fun b => realMeanGap mean b.arm * b.queries).sum

theorem expanded_length {K D : ℕ} (blocks : List (Block K D)) :
    (expanded blocks).length = (blocks.map Block.queries).sum := by
  induction blocks with
  | nil => simp [expanded]
  | cons b bs _ => simp [expanded]

theorem charge_eq_expanded_gap_sum {K D : ℕ} (mean : Fin K → ℝ)
    (blocks : List (Block K D)) :
    chargedRegret mean blocks = ((expanded blocks).map (realMeanGap mean)).sum := by
  induction blocks with
  | nil => simp [chargedRegret, expanded]
  | cons b bs ih =>
    simp only [chargedRegret, List.map_cons, List.sum_cons] at *
    simp [expanded, ih, List.sum_replicate, nsmul_eq_mul, mul_comm]

/-- The block contract charges even inverse-only queries. -/
theorem inverse_only_charge {K D : ℕ} (mean : Fin K → ℝ) (i : Fin K)
    (q : ℕ) (hq : q ≤ D) :
    chargedRegret mean [⟨i, 0, q, by simpa using hq⟩] = realMeanGap mean i * q := by
  simp [chargedRegret, Block.queries]

/-- Padding acts only after all charged queries; the proved horizon excludes it. -/
def expandedAction {K D : ℕ} (blocks : List (Block K D)) (fallback : Fin K) :
    ActionTrace (Fin K) := fun t => (expanded blocks).getD t fallback

theorem chargedRegret_eq_realMeanRegret {K D : ℕ} (mean : Fin K → ℝ)
    (blocks : List (Block K D)) (fallback : Fin K) :
    chargedRegret mean blocks =
      realMeanRegret mean (expandedAction blocks fallback) (expanded blocks).length := by
  rw [charge_eq_expanded_gap_sum, realMeanRegret_eq_finset_sum_gap,
    ← Fin.sum_univ_eq_sum_range]
  rw [← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact List.getElem_eq_getD fallback

theorem chargedRegret_eq_gap_pullCount {K D : ℕ} (mean : Fin K → ℝ)
    (blocks : List (Block K D)) (fallback : Fin K) :
    chargedRegret mean blocks = ∑ i : Fin K, realMeanGap mean i *
      (pullCount (expandedAction blocks fallback) i (expanded blocks).length : ℝ) := by
  rw [chargedRegret_eq_realMeanRegret, realMeanRegret_eq_sum_gap_mul_pullCount]

end BanditRLProof.QuantumQueryAccounting
