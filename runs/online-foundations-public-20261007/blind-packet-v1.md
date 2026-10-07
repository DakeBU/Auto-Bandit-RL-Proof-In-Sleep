# Source-blind closed propositions
Read ONLY this packet. Requested GPT-6 Astra/medium, no escalation/runtime attestation. Disclose reused actor prior history. Reconstruct EVERY N01-N08 in natural language and LaTeX, all seven slots: objects/spaces, quantifiers, assumptions, conclusion, constants/indices, operation/information, boundaries. Do not search source identities, original aliases, theorem bodies or previous verdicts. Report each definition's exact scope; a/b are explicit total functions. No theorem/proof acceptance verdict requested.
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace Neutral
universe u
def a (t : ℕ) (b : Bool) : ℝ := if b then if t = 0 then -2 else 3 else 0
def b (n : ℕ) : Bool := n = 1
def N01 : Prop :=
 ∀ {X : Type u} (V : Set X) (loss : ℕ → X → ℝ)
    (leader : ℕ → X) (T : ℕ)
    (hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V)
    (hmin : ∀ n, 0 < n → n ≤ T → ∀ u ∈ V,
      (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u),
 (∑ t ∈ Finset.range T, loss t (leader (t + 1))) ≤
      ∑ t ∈ Finset.range T, loss t (leader T)

def N02 : Prop :=
 ∀ n, 0 < n → n ≤ 2 → ∀ u ∈ (Set.univ : Set Bool),
      (∑ t ∈ Finset.range n, a t (b n)) ≤
        ∑ t ∈ Finset.range n, a t u

def N03 : Prop :=
 (∑ t ∈ Finset.range 2, a t (b (t + 1))) ≤
      ∑ t ∈ Finset.range 2, a t (b 2)

def N04 : Prop :=
 (∑ t ∈ Finset.range 2, a t (b (t + 1))) = -2 ∧
    (∑ t ∈ Finset.range 2, a t (b 2)) = 0 ∧
    (∑ t ∈ Finset.range 2, a t (b (t + 1))) <
      ∑ t ∈ Finset.range 2, a t (b 2)

def N05 : Prop :=
 ∀ {X : Type u} (V : Set X) (loss : ℕ → X → ℝ)
    (leader : ℕ → X),
 (∑ t ∈ Finset.range 0, loss t (leader (t + 1))) ≤
      ∑ t ∈ Finset.range 0, loss t (leader 0)

def N06 : Prop :=
 ∀ {X : Type u} (loss : ℕ → X → ℝ) (leader : ℕ → X),
 (∑ t ∈ Finset.range 1, loss t (leader (t + 1))) =
      ∑ t ∈ Finset.range 1, loss t (leader 1)

def N07 : Prop :=
    let leader : ℕ → Bool := fun n => n = 2
    (∀ n, 0 < n → n ≤ 2 → leader n ∈ (Set.univ : Set Bool)) ∧
    (∑ t ∈ Finset.range 1, a t true) <
      (∑ t ∈ Finset.range 1, a t (leader 1)) ∧
    (∑ t ∈ Finset.range 2, a t (leader (t + 1))) >
      ∑ t ∈ Finset.range 2, a t (leader 2)

def N08 : Prop :=
    let loss : ℕ → Bool → ℝ := fun t b => if b then if t = 0 then -10 else 5 else 0
    let leader : ℕ → Bool := fun n => n = 2
    let V : Set Bool := {false}
    (∀ n, 0 < n → n ≤ 2 → ∀ u ∈ V,
      (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u) ∧
    leader 2 ∉ V ∧
    (∑ t ∈ Finset.range 2, loss t (leader (t + 1))) >
      ∑ t ∈ Finset.range 2, loss t (leader 2)
#check N01
#check N02
#check N03
#check N04
#check N05
#check N06
#check N07
#check N08
end Neutral

```
Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN. Receipt actor.task=/root/osd_blind, input/report nested path and sha256_raw_bytes, proposition_ids N01-N08, semantic_slots_per_proposition7, prior_history_disclosure, requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false. No source/proof/review edits.
