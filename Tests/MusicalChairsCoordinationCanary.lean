import BanditRLProof

/-! Public-root checks for the coordination component, not the full learner. -/
namespace Tests.MusicalChairsCoordinationCanary
open BanditRLProof.MusicalChairs
open scoped Classical ENNReal

theorem two_player_hazard :
    (1 / 4 : ℝ≥0∞) ≤
      (transition (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3)))
        (fun _ => by simp) (initial 2 3)).toOuterMeasure {s' | s' 0 ≠ none} := by
  have h := transition_unfixed_hazard ({0, 1} : Finset (Fin 3)) (by simp)
    (initial 2 3) (0 : Fin 2) rfl (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_div] at h ⊢
  convert h using 1
  norm_num [← ENNReal.mul_inv]

theorem two_player_isolation :
    (jointDraw (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3))) (fun _ => by simp)).toOuterMeasure
      {draw | ∀ j, draw j ∈ isolationWindow (0 : Fin 2) (0 : Fin 3) j} =
        (1 / 4 : ℝ≥0∞) := by
  have h := jointDraw_isolation ({0, 1} : Finset (Fin 3)) (0 : Fin 2) (0 : Fin 3)
    (by simp) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_div] at h ⊢
  convert h using 1
  norm_num [← ENNReal.mul_inv]

theorem collision_keeps_unfixed :
    step (initial 2 3) (fun _ => (0 : Fin 3)) = initial 2 3 := by
  funext i
  fin_cases i <;> norm_num [step, initial, action, CollisionFree, Fin.forall_fin_two]

theorem separated_draws_fix :
    step (initial 2 3) (fun i => (⟨i.val, by omega⟩ : Fin 3)) =
      fun i => some (⟨i.val, by omega⟩ : Fin 3) := by
  funext i
  fin_cases i <;> norm_num [step, initial, action, CollisionFree, Fin.forall_fin_two]

theorem two_player_occupation (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s,
      (stateLaw (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3))) (fun _ => by simp) t) s *
        (unfixedCount s : ℝ≥0∞) ≤ 16 := by
  have h := expected_unfixed_occupation_le (n := 2) ({0, 1} : Finset (Fin 3)) (by simp) (by decide) T
  convert h using 1
  norm_num

theorem single_player_hazard :
    (1 : ℝ≥0∞) ≤
      (transition (fun _ : Fin 1 => ({0} : Finset (Fin 2)))
        (fun _ => by simp) (initial 1 2)).toOuterMeasure {s' | s' 0 ≠ none} := by
  have h := transition_unfixed_hazard ({0} : Finset (Fin 2)) (by simp)
    (initial 1 2) (0 : Fin 1) rfl (by simp)
  simpa only [Nat.cast_one, Nat.sub_self, pow_zero, one_div_one, mul_one] using h

#print axioms two_player_occupation
#print axioms single_player_hazard
end Tests.MusicalChairsCoordinationCanary
