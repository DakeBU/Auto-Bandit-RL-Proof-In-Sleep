import BanditRLProof.OnlineLearningFoundations
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

universe u
def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.N01.{u} = propositionOf (@BanditRL.OnlineLearning.lemma_1_2.{u}) := by rfl
