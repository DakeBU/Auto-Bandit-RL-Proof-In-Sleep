# Source-blind reconstruction packet
Requested GPT-6 Astra/medium; no model/effort runtime attestation or prior source identity. Reused prior neutral-decoder history must be disclosed. Read ONLY this packet. Reconstruct EACH Q01-Q11 as a universally quantified mathematical statement in natural language and LaTeX, with all seven semantic slots: objects; quantifiers; assumptions; conclusion; constants/indices; operation/information; boundaries. These are CLOSED Props, not proofs; do not infer a named source, theorem identity, prior verdict or body acceptance. F,S are total real functions. Distinguish nonnegative coefficients versus strict positive regimes, admissible z>0 versus total division at0, fixed coefficients versus data dependence and scalar objects versus any unspecified algorithm. Do not invent domain/loss/learner/probability hypotheses absent from the terms.

```lean
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
```

Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this packet's run. Receipt actor.task=/root/osd_blind, packet path/rawSHA, report path/rawSHA, Q01-Q11 covered, prior_history_disclosure and requested/runtime boundary. No source identity search or proof/review verdict. No other file edits.
