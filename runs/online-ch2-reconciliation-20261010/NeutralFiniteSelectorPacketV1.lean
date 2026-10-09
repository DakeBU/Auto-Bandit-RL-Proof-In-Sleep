import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

noncomputable section
open Set Finset
namespace Candidate
variable {X : Type*} {n : ℕ}

def C (past : Fin n → X → ℝ) (x : X) : ℝ :=
  ∑ i, past i x

def M (V : Set X) (past : Fin n → X → ℝ) : Set X :=
  {x | x ∈ V ∧ IsMinOn (C past) V x}

def S (V : Set X) (past : Fin n → X → ℝ) : Option X := by
  classical
  exact if h : (M V past).Nonempty then some (Classical.choose h) else none

def P (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ) : Option X :=
  if t = 0 then some (initial : X) else S V (fun i : Fin t => loss i.val)

-- Terminal 1
#check (∀ (loss : ℕ → X → ℝ) (t : ℕ) (x : X), C (fun i : Fin t => loss i.val) x = ∑ i ∈ range t, loss i x)

-- Terminal 2
#check (∀ (V : Set X) (past : Fin n → X → ℝ) (p : X) (h : S V past = some p), p ∈ V ∧ IsMinOn (C past) V p)

-- Terminal 3
#check (∀ (V : Set X) (past : Fin n → X → ℝ), S V past = none ↔ ¬ ∃ p, p ∈ V ∧ IsMinOn (C past) V p)

-- Terminal 4
#check (∀ (V : Set X) (past past' : Fin n → X → ℝ) (h : ∀ i, EqOn (past i) (past' i) V), S V past = S V past')

-- Terminal 5
#check (∀ (V : Set X) (past : Fin n → X → ℝ) (p : X) (hp : p ∈ V) (hmin : IsMinOn (C past) V p) (hunique : ∀ q ∈ V, IsMinOn (C past) V q → q = p), S V past = some p)

-- Terminal 6
#check (∀ (V : Set X) (initial : V) (loss : ℕ → X → ℝ), P V initial loss 0 = some (initial : X))

-- Terminal 7
#check (∀ (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ) (p : X) (h : P V initial loss t = some p), p ∈ V ∧ IsMinOn (fun x => ∑ i ∈ range t, loss i x) V p)

-- Terminal 8
#check (∀ (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ), P V initial loss t = none ↔ ¬ ∃ p, p ∈ V ∧ IsMinOn (fun x => ∑ i ∈ range t, loss i x) V p)

-- Terminal 9
#check (∀ (V : Set X) (initial : V) (loss loss' : ℕ → X → ℝ) (t : ℕ) (h : ∀ s < t, EqOn (loss s) (loss' s) V), P V initial loss t = P V initial loss' t)

end Candidate
