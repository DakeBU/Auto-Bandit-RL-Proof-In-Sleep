import Tests.OnlineFTLSelectorCanary

noncomputable section
open Set Finset BanditRL.OnlineFTLSelector
namespace Tests.OnlineFTLSelector

example :
    (initial : ℝ) = 3 / 4 ∧
    predict interval initial quadraticLoss 0 = some (3 / 4) ∧
    predict interval initial quadraticLoss 1 = some (1 / 4) ∧
    predict interval initial quadraticLoss 2 = some (1 / 2) ∧
    (1 / 4 : ℝ) ≠ 1 / 2 ∧
    quadraticLoss 0 (1 / 4) ≠ quadraticLoss 0 (3 / 4) ∧
    (∀ t ∈ range 3, ∃ p, predict interval initial quadraticLoss t = some p ∧
      p ∈ interval ∧ IsMinOn (fun x => ∑ i ∈ range t, quadraticLoss i x) interval p) := by
  exact Tests.OnlineFTLSelector.quadratic_trajectory

#check Tests.OnlineFTLSelector.quadratic_trajectory
#print axioms Tests.OnlineFTLSelector.quadratic_trajectory

example :
    quadraticLoss 2 0 ≠ changedLoss 2 0 ∧
    quadraticLoss 3 0 ≠ changedLoss 3 0 ∧
    predict interval initial quadraticLoss 2 = predict interval initial changedLoss 2 := by
  exact Tests.OnlineFTLSelector.current_future_independence

#check Tests.OnlineFTLSelector.current_future_independence
#print axioms Tests.OnlineFTLSelector.current_future_independence

example :
    (2 : ℝ) ∉ interval ∧
    quadraticLoss 0 2 ≠ offDomainLoss 0 2 ∧
    (∀ t, EqOn (quadraticLoss t) (offDomainLoss t) interval) ∧
    select interval (fun i : Fin 2 => quadraticLoss i.val) =
      select interval (fun i : Fin 2 => offDomainLoss i.val) ∧
    predict interval initial quadraticLoss 2 = predict interval initial offDomainLoss 2 := by
  exact Tests.OnlineFTLSelector.off_domain_invariance

#check Tests.OnlineFTLSelector.off_domain_invariance
#print axioms Tests.OnlineFTLSelector.off_domain_invariance

example :
    (0 : ℝ) ∈ interval ∧ (1 : ℝ) ∈ interval ∧ (0 : ℝ) ≠ 1 ∧
    IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval 0 ∧
    IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval 1 ∧
    (∃ p, select interval (fun _ : Fin 1 => fun _ : ℝ => 0) = some p ∧
      p ∈ interval ∧ IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval p) := by
  exact Tests.OnlineFTLSelector.tied_minimizers

#check Tests.OnlineFTLSelector.tied_minimizers
#print axioms Tests.OnlineFTLSelector.tied_minimizers

example :
    select (∅ : Set ℝ) (fun _ : Fin 1 => fun x : ℝ => x ^ 2) = none := by
  exact Tests.OnlineFTLSelector.empty_domain

#check Tests.OnlineFTLSelector.empty_domain
#print axioms Tests.OnlineFTLSelector.empty_domain

example :
    (∃ p, select interval (fun i : Fin 0 => Fin.elim0 i) = some p ∧ p ∈ interval) ∧
    predict interval initial quadraticLoss 0 = some (3 / 4) ∧
    predict interval otherInitial quadraticLoss 0 = some (1 / 4) ∧
    predict interval initial quadraticLoss 0 ≠ predict interval otherInitial quadraticLoss 0 := by
  exact Tests.OnlineFTLSelector.empty_history_and_initialization

#check Tests.OnlineFTLSelector.empty_history_and_initialization
#print axioms Tests.OnlineFTLSelector.empty_history_and_initialization

example :
    (univ : Set ℝ).Nonempty ∧ IsClosed (univ : Set ℝ) ∧ Convex ℝ (univ : Set ℝ) ∧
    select univ (fun _ : Fin 1 => fun x : ℝ => x) = none ∧
    predict univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 0 = some 0 ∧
    predict univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 1 = none := by
  exact Tests.OnlineFTLSelector.affine_nonattainment

#check Tests.OnlineFTLSelector.affine_nonattainment
#print axioms Tests.OnlineFTLSelector.affine_nonattainment

example :
    predict univ ⟨0, mem_univ 0⟩ affineThenQuadratic 1 = none ∧
    predict univ ⟨0, mem_univ 0⟩ affineThenQuadratic 2 = some 0 ∧
    IsMinOn (fun x => ∑ i ∈ range 2, affineThenQuadratic i x) univ 0 ∧
    (∀ x, (∑ i ∈ range 2, affineThenQuadratic i x) = x ^ 2) := by
  exact Tests.OnlineFTLSelector.recovery_after_nonattainment

#check Tests.OnlineFTLSelector.recovery_after_nonattainment
#print axioms Tests.OnlineFTLSelector.recovery_after_nonattainment

end Tests.OnlineFTLSelector
