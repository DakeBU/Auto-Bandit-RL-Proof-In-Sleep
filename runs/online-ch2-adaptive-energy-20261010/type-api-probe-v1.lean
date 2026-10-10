import BanditRLProof.TsallisFTRLStationarity
import Mathlib.Tactic

open Finset
#check @BanditRLProof.Tsallis.two_mul_sqrt_sub_sqrt_le_sub_div_sqrt
#check @Real.sqrt_pos
#check @Finset.sum_range_succ
#check @Finset.sum_nonneg
#check (∀ (a : ℕ → ℝ) (T : ℕ), (∀ t < T, 0 ≤ a t) →
  (∑ t ∈ range T, a t / Real.sqrt (∑ i ∈ range (t + 1), a i)) ≤
    2 * Real.sqrt (∑ i ∈ range T, a i))
#check (∀ {E : Type} [NormedAddCommGroup E] (g : ℕ → E) (T : ℕ),
  (∑ t ∈ range T, ‖g t‖ ^ 2 / Real.sqrt (∑ i ∈ range (t + 1), ‖g i‖ ^ 2)) ≤
    2 * Real.sqrt (∑ i ∈ range T, ‖g i‖ ^ 2))
#check (∀ {E : Type} [NormedAddCommGroup E] (g : ℕ → E) (T : ℕ) (D : ℝ), 0 ≤ D →
  D / 2 * (∑ t ∈ range T, ‖g t‖ ^ 2 / Real.sqrt (∑ i ∈ range (t + 1), ‖g i‖ ^ 2)) ≤
    D * Real.sqrt (∑ i ∈ range T, ‖g i‖ ^ 2))
