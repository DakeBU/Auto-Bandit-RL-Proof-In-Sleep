Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this mathematical packet in this pass. No source identity, public theorem-name map, prior verdict, proof bodies, compile logs or other files. Definitions are algorithm context, not proof bodies. Reconstruct Q0-Q2 and M01-M07 in seven semantic slots:objects,quantifiers,assumptions,conclusions,constants/index,information/probability,boundary. This is retained typed statement text with proof bodies omitted; do not claim source acceptance or new compilation. Write only blind-reconstruction-v1.md and blind-receipt-v1.json beside this packet, including exact raw input/report hashes, actor/requested medium, prior unrelated actor history not erased, sole input this pass, no human/external review.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
open Set Finset
namespace Neutral



def Q0 (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t+1 => Q0 z t + z t

def Q1 (z : ℕ → ℝ) (x0 : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then x0 else if Q0 z t < 0 then 1 else -1

def Q2 (t : ℕ) : ℝ :=
  if t = 0 then -(1/2) else if t % 2 = 1 then 1 else -1


theorem M01 (z : ℕ → ℝ) (t : ℕ) : Q0 z t = ∑ i ∈ range t, z i

theorem M02 (z w : ℕ → ℝ) (x0 : ℝ) (t : ℕ) (h : ∀ i < t, z i = w i) : Q1 z x0 t = Q1 w x0 t

theorem M03 (z : ℕ → ℝ) (x0 : ℝ) (hx0 : x0 ∈ Icc (-1 : ℝ) 1) (t : ℕ) : Q1 z x0 t ∈ Icc (-1 : ℝ) 1

theorem M04 (z : ℕ → ℝ) (x0 : ℝ) (t : ℕ) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : (∑ i ∈ range t, z i * Q1 z x0 t) ≤ ∑ i ∈ range t, z i * u

theorem M05 (t : ℕ) (ht : 0 < t) : Q0 Q2 t = if t % 2 = 1 then -(1/2) else (1/2)

theorem M06 (x0 : ℝ) (t : ℕ) (ht : 0 < t) : Q1 Q2 x0 t = if t % 2 = 1 then 1 else -1

theorem M07 (x0 : ℝ) (hx0 : x0 ∈ Icc (-1 : ℝ) 1) (T : ℕ) (hT : 0 < T) : (∑ t ∈ range T, Q2 t * Q1 Q2 x0 t) - (∑ t ∈ range T, Q2 t * (0 : ℝ)) = (T : ℝ) - 1 - x0 / 2 ∧ (T : ℝ) - 3/2 ≤ (∑ t ∈ range T, Q2 t * Q1 Q2 x0 t) - (∑ t ∈ range T, Q2 t * (0 : ℝ))

end Neutral
```
