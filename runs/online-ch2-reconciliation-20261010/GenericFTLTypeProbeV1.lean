import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

noncomputable section
open Set Finset
namespace BanditRL.OnlineFTLSelector
variable {X : Type*} {n : ℕ}

def cumulative (past : Fin n → X → ℝ) (x : X) : ℝ :=
  ∑ i, past i x

def minimizers (V : Set X) (past : Fin n → X → ℝ) : Set X :=
  {x | x ∈ V ∧ IsMinOn (cumulative past) V x}

def select (V : Set X) (past : Fin n → X → ℝ) : Option X := by
  classical
  exact if h : (minimizers V past).Nonempty then some (Classical.choose h) else none

def predict (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ) : Option X :=
  if t = 0 then some (initial : X) else select V (fun i : Fin t => loss i.val)

#eval IO.println "TYPE-PROBE-1"
#check (∀ (loss : ℕ → X → ℝ) (t : ℕ) (x : X), cumulative (fun i : Fin t => loss i.val) x = ∑ i ∈ range t, loss i x)

#eval IO.println "TYPE-PROBE-2"
#check (∀ (V : Set X) (past : Fin n → X → ℝ) (p : X) (h : select V past = some p), p ∈ V ∧ IsMinOn (cumulative past) V p)

#eval IO.println "TYPE-PROBE-3"
#check (∀ (V : Set X) (past : Fin n → X → ℝ), select V past = none ↔ ¬ ∃ p, p ∈ V ∧ IsMinOn (cumulative past) V p)

#eval IO.println "TYPE-PROBE-4"
#check (∀ (V : Set X) (past past' : Fin n → X → ℝ) (h : ∀ i, EqOn (past i) (past' i) V), select V past = select V past')

#eval IO.println "TYPE-PROBE-5"
#check (∀ (V : Set X) (past : Fin n → X → ℝ) (p : X) (hp : p ∈ V) (hmin : IsMinOn (cumulative past) V p) (hunique : ∀ q ∈ V, IsMinOn (cumulative past) V q → q = p), select V past = some p)

#eval IO.println "TYPE-PROBE-6"
#check (∀ (V : Set X) (initial : V) (loss : ℕ → X → ℝ), predict V initial loss 0 = some (initial : X))

#eval IO.println "TYPE-PROBE-7"
#check (∀ (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ) (p : X) (h : predict V initial loss t = some p), p ∈ V ∧ IsMinOn (fun x => ∑ i ∈ range t, loss i x) V p)

#eval IO.println "TYPE-PROBE-8"
#check (∀ (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ), predict V initial loss t = none ↔ ¬ ∃ p, p ∈ V ∧ IsMinOn (fun x => ∑ i ∈ range t, loss i x) V p)

#eval IO.println "TYPE-PROBE-9"
#check (∀ (V : Set X) (initial : V) (loss loss' : ℕ → X → ℝ) (t : ℕ) (h : ∀ s < t, EqOn (loss s) (loss' s) V), predict V initial loss t = predict V initial loss' t)

#check Fin.sum_univ_eq_sum_range
#check isMinOn_iff
#check Classical.choose_spec
end BanditRL.OnlineFTLSelector
