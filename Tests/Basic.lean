import BanditRLProof

namespace BanditRLProof

def constantZeroAction : Nat → Nat := fun _ => 0

example : pullCount constantZeroAction 0 3 = 3 := by
  native_decide

def alternatingAction : Nat → Fin 2 :=
  fun n => if n % 2 = 0 then 0 else 1

example : pullCount alternatingAction 0 5 = 3 := by
  native_decide

example : pullCount alternatingAction 0 1 = 1 := by
  rw [pullCount_one]
  native_decide

example : pullCount alternatingAction 0 (2 + 1) =
    pullCount alternatingAction 0 2 + 1 := by
  apply pullCount_succ_of_eq
  native_decide

example : pullCount alternatingAction 0 (1 + 1) =
    pullCount alternatingAction 0 1 := by
  apply pullCount_succ_of_ne
  native_decide

example (t : Nat) :
    pullCount alternatingAction 0 t ≤ pullCount alternatingAction 0 (t + 1) :=
  pullCount_le_succ alternatingAction 0 t

example (s t : Nat) (h : s ≤ t) :
    pullCount alternatingAction 0 s ≤ pullCount alternatingAction 0 t :=
  pullCount_mono alternatingAction 0 h

example (t : Nat) :
    pullCount alternatingAction 0 t ≤ t :=
  pullCount_le_time alternatingAction 0 t

example : pullCount constantZeroAction 1 4 = 0 := by
  apply pullCount_eq_zero_of_forall_ne
  intro s _hs
  simp [constantZeroAction]

example : pullCount constantZeroAction 0 4 = 4 := by
  apply pullCount_eq_time_of_forall_eq
  intro s _hs
  rfl

example : pullCount (fun _ : Nat => 2) 2 7 = 7 := by
  simp

example : pullCount (fun _ : Nat => 2) 1 7 = 0 := by
  exact pullCount_const_of_ne (a := 1) 2 (by decide) 7

example : 0 < pullCount alternatingAction 0 5 := by
  exact pullCount_pos_of_eq_before alternatingAction 0
    (s := 0) (t := 5) (by decide) (by native_decide)

def natReward : Nat → Nat := fun t => t + 1

example : sumRewards (fun _ : Nat => 2) natReward 1 6 = 0 := by
  exact sumRewards_const_of_ne (a := 1) (reward := natReward)
    (fun x => Nat.add_zero x) 2 (by decide) 6

def etcSpec : ETC.Spec 2 where
  hK := by decide
  explorationPulls := 3

example : ETC.exploreArm etcSpec 0 = ETC.exploreArm etcSpec 2 := by
  apply ETC.exploreArm_eq_of_mod_eq
  native_decide

def ucbSpec : UCB.Spec 2 where
  hK := by decide
  explorationScale := 1

def ucbState : UCB.IndexState 2 where
  empiricalMean := fun arm => if arm.val = 0 then 1 else 0
  pulls := fun _ => 1

example (arm : Fin 2) :
    UCB.score ucbSpec ucbState arm = ucbState.empiricalMean arm := by
  simp

def twoArmModel : FiniteBanditModel 2 where
  hK := by decide
  mean := fun arm => if arm.val = 0 then 1 else 0

example : twoArmModel.gap twoArmModel.bestArm = 0 := by
  simp

example : pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) 1 = 0 := by
  rw [pseudoRegret_one]
  simp [FiniteBanditModel.gap_bestArm]

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) (t + 1) =
      pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t := by
  apply pseudoRegret_succ_of_bestArm
  rfl

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t = 0 := by
  simp

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t = 0 := by
  apply pseudoRegret_eq_zero_of_forall_gap_zero
  intro _s _hs
  simp

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t = 0 := by
  exact pseudoRegret_const_bestArm twoArmModel t

end BanditRLProof
