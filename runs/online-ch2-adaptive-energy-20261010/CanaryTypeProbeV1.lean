import BanditRLProof.OnlineAdaptiveEnergy

open Finset

def proposedCanary1 : Prop :=
    let g : ℕ → ℝ := fun t => if t = 1 then 3 else if t = 3 then 4 else 0
    let Q : (ℕ → ℝ) → ℕ → ℝ := fun v n =>
      ∑ t ∈ range n, ‖v t‖ ^ 2 / Real.sqrt (∑ i ∈ range (t + 1), ‖v i‖ ^ 2)
    let S : (ℕ → ℝ) → ℕ → ℝ := fun v n => ∑ i ∈ range n, ‖v i‖ ^ 2
    (2 : ℝ) / 2 * Q g 4 ≤ 2 * Real.sqrt (S g 4) ∧
      Q g 4 = 31 / 5 ∧ S g 4 = 25 ∧ Q g 4 < 2 * Real.sqrt (S g 4) ∧
      g 0 = 0 ∧ g 2 = 0 ∧ g 1 = 3 ∧ g 3 = 4
#print proposedCanary1

def proposedCanary2 : Prop :=
    let g₁ : ℕ → ℝ := fun _ => 1
    let g₀ : ℕ → ℝ := fun _ => 0
    let Q : (ℕ → ℝ) → ℕ → ℝ := fun v n =>
      ∑ t ∈ range n, ‖v t‖ ^ 2 / Real.sqrt (∑ i ∈ range (t + 1), ‖v i‖ ^ 2)
    let S : (ℕ → ℝ) → ℕ → ℝ := fun v n => ∑ i ∈ range n, ‖v i‖ ^ 2
    ((2 : ℝ) / 2 * Q g₁ 0 ≤ 2 * Real.sqrt (S g₁ 0)) ∧
      ((2 : ℝ) / 2 * Q g₀ 3 ≤ 2 * Real.sqrt (S g₀ 3)) ∧
      ((0 : ℝ) / 2 * Q g₁ 2 ≤ 0 * Real.sqrt (S g₁ 2))
#print proposedCanary2
