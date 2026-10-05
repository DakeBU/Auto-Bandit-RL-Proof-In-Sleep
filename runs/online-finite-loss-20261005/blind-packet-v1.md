Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this packet this pass, no source identity/public-name map/prior verdict/proof body/other files. Two context definitions and two unproved headers. Reconstruct Q0/Q1/M01/M02 in seven slots:objects,quantifiers,assumptions,conclusion,normalization,information/probability,boundary. Compare finite-real witness existence with below-top predicate; both infinities and empty-set cases matter. Do not assume unspecified noBottom premise. Imported EReal conventions should be marked interpretations, not verified code. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with raw packet/report SHA, actor/requested medium, sole input currentpass, prior history not erased, no compilation/source acceptance/human/external/runtime-attestation claim.

```lean
import Mathlib.Data.EReal.Basic
noncomputable section
open Set
namespace Neutral

def Q0 {E : Type*} (f : E → EReal) : Set E := {x | f x < ⊤}

def Q1 {E : Type*} (V : Set E) (x : E) : EReal := by
  classical
  exact if x ∈ V then 0 else ⊤

theorem M01 {E : Type*} (f : E → EReal) (V : Set E) (x : E) :
    (∃ r : ℝ, f x + Q1 V x = (r : EReal)) ↔
      x ∈ V ∧ ∃ r : ℝ, f x = (r : EReal)

theorem M02 {E : Type*} (f : E → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (V : Set E) :
    Q0 (fun x => f x + Q1 V x) = Q0 f ∩ V

end Neutral
```
