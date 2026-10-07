import BanditRLProof.OnlineOptimalStep
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
namespace NeutralScalar
noncomputable def F (A B z : ℝ) : ℝ := A / (2 * z) + z * B / 2
noncomputable def S (A B : ℝ) : ℝ := Real.sqrt A / Real.sqrt B
def Q01 : Prop := ∀ (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η),
  F A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η)

def Q02 : Prop := ∀ (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η),
  Real.sqrt A * Real.sqrt B ≤ F A B η

def Q03 : Prop := ∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
  0 < S A B

def Q04 : Prop := ∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
  F A B (S A B) = Real.sqrt A * Real.sqrt B

def Q05 : Prop := ∀ (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η),
  F A B η = F A B (S A B) ↔ η = S A B

def Q06 : Prop := ∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
  0 < S A B ∧
    F A B (S A B) = Real.sqrt (A * B) ∧
    ∀ η : ℝ, 0 < η → F A B (S A B) ≤ F A B η

def Q07 : Prop := ∀ (R B : ℝ) (hR : 0 < R) (hB : 0 < B),
  S (R ^ 2) B = R / Real.sqrt B ∧
    F (R ^ 2) B (R / Real.sqrt B) = R * Real.sqrt B ∧
    ∀ η : ℝ, 0 < η → F (R ^ 2) B (R / Real.sqrt B) ≤ F (R ^ 2) B η

def Q08 : Prop := ∀ (D G : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hT : 0 < T),
  S (D ^ 2) (G ^ 2 * (T : ℝ)) = D / (G * Real.sqrt (T : ℝ)) ∧
    F (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) =
      D * G * Real.sqrt (T : ℝ) ∧
    ∀ η : ℝ, 0 < η →
      F (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) ≤
      F (D ^ 2) (G ^ 2 * (T : ℝ)) η

def Q09 : Prop := ∀ (B η : ℝ) (hB : 0 < B) (hη : 0 < η),
  0 < η / 2 ∧ F 0 B (η / 2) < F 0 B η

def Q10 : Prop := ∀ (A η : ℝ) (hA : 0 < A) (hη : 0 < η),
  0 < 2 * η ∧ F A 0 (2 * η) < F A 0 η

def Q11 : Prop := ∀ (η : ℝ),
  F 0 0 η = 0
#check Q01
#check Q02
#check Q03
#check Q04
#check Q05
#check Q06
#check Q07
#check Q08
#check Q09
#check Q10
#check Q11
end NeutralScalar
example : NeutralScalar.Q01 = (∀ (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η), BanditRL.OnlineOptimalStep.upperBound A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η)) := by rfl
example : NeutralScalar.Q02 = (∀ (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η), Real.sqrt A * Real.sqrt B ≤ BanditRL.OnlineOptimalStep.upperBound A B η) := by rfl
example : NeutralScalar.Q03 = (∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B), 0 < BanditRL.OnlineOptimalStep.optimalStep A B) := by rfl
example : NeutralScalar.Q04 = (∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B), BanditRL.OnlineOptimalStep.upperBound A B (BanditRL.OnlineOptimalStep.optimalStep A B) = Real.sqrt A * Real.sqrt B) := by rfl
example : NeutralScalar.Q05 = (∀ (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η), BanditRL.OnlineOptimalStep.upperBound A B η = BanditRL.OnlineOptimalStep.upperBound A B (BanditRL.OnlineOptimalStep.optimalStep A B) ↔ η = BanditRL.OnlineOptimalStep.optimalStep A B) := by rfl
example : NeutralScalar.Q06 = (∀ (A B : ℝ) (hA : 0 < A) (hB : 0 < B), 0 < BanditRL.OnlineOptimalStep.optimalStep A B ∧
    BanditRL.OnlineOptimalStep.upperBound A B (BanditRL.OnlineOptimalStep.optimalStep A B) = Real.sqrt (A * B) ∧
    ∀ η : ℝ, 0 < η → BanditRL.OnlineOptimalStep.upperBound A B (BanditRL.OnlineOptimalStep.optimalStep A B) ≤ BanditRL.OnlineOptimalStep.upperBound A B η) := by rfl
example : NeutralScalar.Q07 = (∀ (R B : ℝ) (hR : 0 < R) (hB : 0 < B), BanditRL.OnlineOptimalStep.optimalStep (R ^ 2) B = R / Real.sqrt B ∧
    BanditRL.OnlineOptimalStep.upperBound (R ^ 2) B (R / Real.sqrt B) = R * Real.sqrt B ∧
    ∀ η : ℝ, 0 < η → BanditRL.OnlineOptimalStep.upperBound (R ^ 2) B (R / Real.sqrt B) ≤ BanditRL.OnlineOptimalStep.upperBound (R ^ 2) B η) := by rfl
example : NeutralScalar.Q08 = (∀ (D G : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hT : 0 < T), BanditRL.OnlineOptimalStep.optimalStep (D ^ 2) (G ^ 2 * (T : ℝ)) = D / (G * Real.sqrt (T : ℝ)) ∧
    BanditRL.OnlineOptimalStep.upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) =
      D * G * Real.sqrt (T : ℝ) ∧
    ∀ η : ℝ, 0 < η →
      BanditRL.OnlineOptimalStep.upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) ≤
      BanditRL.OnlineOptimalStep.upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) η) := by rfl
example : NeutralScalar.Q09 = (∀ (B η : ℝ) (hB : 0 < B) (hη : 0 < η), 0 < η / 2 ∧ BanditRL.OnlineOptimalStep.upperBound 0 B (η / 2) < BanditRL.OnlineOptimalStep.upperBound 0 B η) := by rfl
example : NeutralScalar.Q10 = (∀ (A η : ℝ) (hA : 0 < A) (hη : 0 < η), 0 < 2 * η ∧ BanditRL.OnlineOptimalStep.upperBound A 0 (2 * η) < BanditRL.OnlineOptimalStep.upperBound A 0 η) := by rfl
example : NeutralScalar.Q11 = (∀ (η : ℝ), BanditRL.OnlineOptimalStep.upperBound 0 0 η = 0) := by rfl
