Neutral mathematical definitions and11unproved targets. Reconstruct each using7slots: model, assumptions, parameters/quantifiers, information structure, objective/regret, guarantee/equality, scope/boundary. Sole permitted input this packet. No source/provenance/name-map/context/other files, proof bodies, compile/evidence receipts or verdicts. Do not prove/compile/sourceverify.

```lean
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace NeutralStepModel

noncomputable def q (A B η : ℝ) : ℝ := A / (2 * η) + η * B / 2
noncomputable def r (A B : ℝ) : ℝ := Real.sqrt A / Real.sqrt B

theorem N01 (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    q A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η)

theorem N02 (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    Real.sqrt A * Real.sqrt B ≤ q A B η

theorem N03 (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < r A B

theorem N04 (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    q A B (r A B) = Real.sqrt A * Real.sqrt B

theorem N05 (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η) :
    q A B η = q A B (r A B) ↔ η = r A B

theorem N06 (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < r A B ∧
    q A B (r A B) = Real.sqrt (A * B) ∧
    ∀ η : ℝ, 0 < η → q A B (r A B) ≤ q A B η

theorem N07 (R B : ℝ) (hR : 0 < R) (hB : 0 < B) :
    r (R ^ 2) B = R / Real.sqrt B ∧
    q (R ^ 2) B (R / Real.sqrt B) = R * Real.sqrt B ∧
    ∀ η : ℝ, 0 < η → q (R ^ 2) B (R / Real.sqrt B) ≤ q (R ^ 2) B η

theorem N08 (D G : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hT : 0 < T) :
    r (D ^ 2) (G ^ 2 * (T : ℝ)) = D / (G * Real.sqrt (T : ℝ)) ∧
    q (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) =
      D * G * Real.sqrt (T : ℝ) ∧
    ∀ η : ℝ, 0 < η →
      q (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) ≤
      q (D ^ 2) (G ^ 2 * (T : ℝ)) η

theorem N09 (B η : ℝ) (hB : 0 < B) (hη : 0 < η) :
    0 < η / 2 ∧ q 0 B (η / 2) < q 0 B η

theorem N10 (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    0 < 2 * η ∧ q A 0 (2 * η) < q A 0 η

theorem N11 (η : ℝ) : q 0 0 η = 0
end NeutralStepModel
```
