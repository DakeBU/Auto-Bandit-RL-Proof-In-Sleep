import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace BanditRL.OnlineOptimalStep

noncomputable def upperBound (A B η : ℝ) : ℝ := A / (2 * η) + η * B / 2
noncomputable def optimalStep (A B : ℝ) : ℝ := Real.sqrt A / Real.sqrt B

#check (∀ (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η),
upperBound A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η))
#check (∀ (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η),
Real.sqrt A * Real.sqrt B ≤ upperBound A B η)
#check (∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
0 < optimalStep A B)
#check (∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
upperBound A B (optimalStep A B) = Real.sqrt A * Real.sqrt B)
#check (∀ (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η),
upperBound A B η = upperBound A B (optimalStep A B) ↔ η = optimalStep A B)
#check (∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
0 < optimalStep A B ∧
    upperBound A B (optimalStep A B) = Real.sqrt (A * B) ∧
    ∀ η : ℝ, 0 < η → upperBound A B (optimalStep A B) ≤ upperBound A B η)
#check (∀ (R B : ℝ) (hR : 0 < R) (hB : 0 < B),
optimalStep (R ^ 2) B = R / Real.sqrt B ∧
    upperBound (R ^ 2) B (R / Real.sqrt B) = R * Real.sqrt B ∧
    ∀ η : ℝ, 0 < η → upperBound (R ^ 2) B (R / Real.sqrt B) ≤ upperBound (R ^ 2) B η)
#check (∀ (D G : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hT : 0 < T),
optimalStep (D ^ 2) (G ^ 2 * (T : ℝ)) = D / (G * Real.sqrt (T : ℝ)) ∧
    upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) =
      D * G * Real.sqrt (T : ℝ) ∧
    ∀ η : ℝ, 0 < η →
      upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) ≤
      upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) η)
#check (∀ (B η : ℝ) (hB : 0 < B) (hη : 0 < η),
0 < η / 2 ∧ upperBound 0 B (η / 2) < upperBound 0 B η)
#check (∀ (A η : ℝ) (hA : 0 < A) (hη : 0 < η),
0 < 2 * η ∧ upperBound A 0 (2 * η) < upperBound A 0 η)
#check (∀ (η : ℝ),
upperBound 0 0 η = 0)
end BanditRL.OnlineOptimalStep
