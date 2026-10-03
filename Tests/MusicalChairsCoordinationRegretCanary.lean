import BanditRLProof

namespace Tests.MusicalChairsCoordinationRegretCanary
open BanditRLProof.MusicalChairs
open scoped Classical ENNReal
set_option autoImplicit false

noncomputable def means (a : Fin 3) : ℝ := if a = 0 then 3/4 else if a = 1 then 1/2 else 1/4

def oneFixed : State 2 3 := fun i => if i = 0 then some 0 else none

theorem collision_positive_regret :
    roundPseudoRegret ({0, 1} : Finset (Fin 3)) means oneFixed (fun _ => 0) = 5/4 := by
  norm_num [roundPseudoRegret, roundMeanReward, means, oneFixed, action,
    CollisionFree, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem collision_one_unfixed : unfixedCount oneFixed = 1 := by
  decide +kernel

theorem separated_zero_regret :
    roundPseudoRegret ({0, 1} : Finset (Fin 3)) means oneFixed
      (fun i => if i = 0 then 0 else 1) = 0 := by
  norm_num [roundPseudoRegret, roundMeanReward, means, oneFixed, action,
    CollisionFree, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem two_player_expected (T : ℕ) :
    expectedCoordinationRegret (n := 2) ({0, 1} : Finset (Fin 3)) (by decide) means T ≤ 32 := by
  have h := expectedCoordinationRegret_le (n := 2) ({0, 1} : Finset (Fin 3))
    (by decide) (by decide) means (by intro a; fin_cases a <;> norm_num [means]) T
  norm_num at h ⊢
  exact h


end Tests.MusicalChairsCoordinationRegretCanary
