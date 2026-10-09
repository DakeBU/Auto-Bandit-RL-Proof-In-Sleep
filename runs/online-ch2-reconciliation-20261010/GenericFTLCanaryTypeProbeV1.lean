import BanditRLProof.OnlineFTLSelector
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

noncomputable section
open Set Finset BanditRL.OnlineFTLSelector
namespace Tests.OnlineFTLSelector

def interval : Set ℝ := Icc 0 1

def initial : interval := ⟨3 / 4, by norm_num [interval]⟩

def otherInitial : interval := ⟨1 / 4, by norm_num [interval]⟩

def quadraticLoss (t : ℕ) (x : ℝ) : ℝ :=
  if t = 0 then (x - 1 / 4) ^ 2 else (x - 3 / 4) ^ 2

def changedLoss (t : ℕ) (x : ℝ) : ℝ :=
  if t < 2 then quadraticLoss t x else x + 100

def offDomainLoss (t : ℕ) (x : ℝ) : ℝ :=
  if x ∈ interval then quadraticLoss t x else x + 7

def affineThenQuadratic (t : ℕ) (x : ℝ) : ℝ :=
  if t = 0 then x else x ^ 2 - x

#eval IO.println "CANARY-TYPE-PROBE-1"
#check ((initial : ℝ) = 3 / 4 ∧
    predict interval initial quadraticLoss 0 = some (3 / 4) ∧
    predict interval initial quadraticLoss 1 = some (1 / 4) ∧
    predict interval initial quadraticLoss 2 = some (1 / 2) ∧
    (1 / 4 : ℝ) ≠ 1 / 2 ∧
    quadraticLoss 0 (1 / 4) ≠ quadraticLoss 0 (3 / 4) ∧
    (∀ t ∈ range 3, ∃ p, predict interval initial quadraticLoss t = some p ∧
      p ∈ interval ∧ IsMinOn (fun x => ∑ i ∈ range t, quadraticLoss i x) interval p) : Prop)

#eval IO.println "CANARY-TYPE-PROBE-2"
#check (quadraticLoss 2 0 ≠ changedLoss 2 0 ∧
    quadraticLoss 3 0 ≠ changedLoss 3 0 ∧
    predict interval initial quadraticLoss 2 = predict interval initial changedLoss 2 : Prop)

#eval IO.println "CANARY-TYPE-PROBE-3"
#check ((2 : ℝ) ∉ interval ∧
    quadraticLoss 0 2 ≠ offDomainLoss 0 2 ∧
    (∀ t, EqOn (quadraticLoss t) (offDomainLoss t) interval) ∧
    select interval (fun i : Fin 2 => quadraticLoss i.val) =
      select interval (fun i : Fin 2 => offDomainLoss i.val) ∧
    predict interval initial quadraticLoss 2 = predict interval initial offDomainLoss 2 : Prop)

#eval IO.println "CANARY-TYPE-PROBE-4"
#check ((0 : ℝ) ∈ interval ∧ (1 : ℝ) ∈ interval ∧ (0 : ℝ) ≠ 1 ∧
    IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval 0 ∧
    IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval 1 ∧
    (∃ p, select interval (fun _ : Fin 1 => fun _ : ℝ => 0) = some p ∧
      p ∈ interval ∧ IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval p) : Prop)

#eval IO.println "CANARY-TYPE-PROBE-5"
#check (select (∅ : Set ℝ) (fun _ : Fin 1 => fun x : ℝ => x ^ 2) = none : Prop)

#eval IO.println "CANARY-TYPE-PROBE-6"
#check ((∃ p, select interval (fun i : Fin 0 => Fin.elim0 i) = some p ∧ p ∈ interval) ∧
    predict interval initial quadraticLoss 0 = some (3 / 4) ∧
    predict interval otherInitial quadraticLoss 0 = some (1 / 4) ∧
    predict interval initial quadraticLoss 0 ≠ predict interval otherInitial quadraticLoss 0 : Prop)

#eval IO.println "CANARY-TYPE-PROBE-7"
#check ((univ : Set ℝ).Nonempty ∧ IsClosed (univ : Set ℝ) ∧ Convex ℝ (univ : Set ℝ) ∧
    select univ (fun _ : Fin 1 => fun x : ℝ => x) = none ∧
    predict univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 0 = some 0 ∧
    predict univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 1 = none : Prop)

#eval IO.println "CANARY-TYPE-PROBE-8"
#check (predict univ ⟨0, mem_univ 0⟩ affineThenQuadratic 1 = none ∧
    predict univ ⟨0, mem_univ 0⟩ affineThenQuadratic 2 = some 0 ∧
    IsMinOn (fun x => ∑ i ∈ range 2, affineThenQuadratic i x) univ 0 ∧
    (∀ x, (∑ i ∈ range 2, affineThenQuadratic i x) = x ^ 2) : Prop)

end Tests.OnlineFTLSelector
