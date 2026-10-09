import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

noncomputable section
open Set Finset
namespace FiniteSelectionPacket
variable {X : Type*} {n : ℕ}

def C (past : Fin n → X → ℝ) (x : X) : ℝ :=
  ∑ i, past i x

def M (V : Set X) (past : Fin n → X → ℝ) : Set X :=
  {x | x ∈ V ∧ IsMinOn (C past) V x}

def S (V : Set X) (past : Fin n → X → ℝ) : Option X := by
  classical
  exact if h : (M V past).Nonempty then some (Classical.choose h) else none

def P (V : Set X) (a : V) (loss : ℕ → X → ℝ) (t : ℕ) : Option X :=
  if t = 0 then some (a : X) else S V (fun i : Fin t => loss i.val)

end FiniteSelectionPacket

noncomputable section
open Set Finset FiniteSelectionPacket
namespace FiniteSelectionExamples

def D : Set ℝ := Icc 0 1

def a : D := ⟨3 / 4, by norm_num [D]⟩

def b : D := ⟨1 / 4, by norm_num [D]⟩

def q (t : ℕ) (x : ℝ) : ℝ :=
  if t = 0 then (x - 1 / 4) ^ 2 else (x - 3 / 4) ^ 2

def qChanged (t : ℕ) (x : ℝ) : ℝ :=
  if t < 2 then q t x else x + 100

def qExtended (t : ℕ) (x : ℝ) : ℝ :=
  if x ∈ D then q t x else x + 7

def r (t : ℕ) (x : ℝ) : ℝ :=
  if t = 0 then x else x ^ 2 - x

#check ((a : ℝ) = 3 / 4 ∧
    P D a q 0 = some (3 / 4) ∧
    P D a q 1 = some (1 / 4) ∧
    P D a q 2 = some (1 / 2) ∧
    (1 / 4 : ℝ) ≠ 1 / 2 ∧
    q 0 (1 / 4) ≠ q 0 (3 / 4) ∧
    (∀ t ∈ range 3, ∃ p, P D a q t = some p ∧
      p ∈ D ∧ IsMinOn (fun x => ∑ i ∈ range t, q i x) D p) : Prop)

#check (q 2 0 ≠ qChanged 2 0 ∧
    q 3 0 ≠ qChanged 3 0 ∧
    P D a q 2 = P D a qChanged 2 : Prop)

#check ((2 : ℝ) ∉ D ∧
    q 0 2 ≠ qExtended 0 2 ∧
    (∀ t, EqOn (q t) (qExtended t) D) ∧
    S D (fun i : Fin 2 => q i.val) =
      S D (fun i : Fin 2 => qExtended i.val) ∧
    P D a q 2 = P D a qExtended 2 : Prop)

#check ((0 : ℝ) ∈ D ∧ (1 : ℝ) ∈ D ∧ (0 : ℝ) ≠ 1 ∧
    IsMinOn (C (fun _ : Fin 1 => fun _ : ℝ => 0)) D 0 ∧
    IsMinOn (C (fun _ : Fin 1 => fun _ : ℝ => 0)) D 1 ∧
    (∃ p, S D (fun _ : Fin 1 => fun _ : ℝ => 0) = some p ∧
      p ∈ D ∧ IsMinOn (C (fun _ : Fin 1 => fun _ : ℝ => 0)) D p) : Prop)

#check (S (∅ : Set ℝ) (fun _ : Fin 1 => fun x : ℝ => x ^ 2) = none : Prop)

#check ((∃ p, S D (fun i : Fin 0 => Fin.elim0 i) = some p ∧ p ∈ D) ∧
    P D a q 0 = some (3 / 4) ∧
    P D b q 0 = some (1 / 4) ∧
    P D a q 0 ≠ P D b q 0 : Prop)

#check ((univ : Set ℝ).Nonempty ∧ IsClosed (univ : Set ℝ) ∧ Convex ℝ (univ : Set ℝ) ∧
    S univ (fun _ : Fin 1 => fun x : ℝ => x) = none ∧
    P univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 0 = some 0 ∧
    P univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 1 = none : Prop)

#check (P univ ⟨0, mem_univ 0⟩ r 1 = none ∧
    P univ ⟨0, mem_univ 0⟩ r 2 = some 0 ∧
    IsMinOn (fun x => ∑ i ∈ range 2, r i x) univ 0 ∧
    (∀ x, (∑ i ∈ range 2, r i x) = x ^ 2) : Prop)

end FiniteSelectionExamples
