import BanditRLProof

namespace BanditRLProof

def constantZeroAction : Nat → Nat := fun _ => 0

example : pullCount constantZeroAction 0 3 = 3 := by
  native_decide

def alternatingAction : Nat → Fin 2 :=
  fun n => if n % 2 = 0 then 0 else 1

example : pullCount alternatingAction 0 5 = 3 := by
  native_decide

def twoArmModel : FiniteBanditModel 2 where
  hK := by decide
  mean := fun arm => if arm.val = 0 then 1 else 0

example : twoArmModel.gap twoArmModel.bestArm = 0 := by
  simp

end BanditRLProof
