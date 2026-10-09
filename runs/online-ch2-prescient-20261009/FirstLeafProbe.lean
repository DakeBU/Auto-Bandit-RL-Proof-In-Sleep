import BanditRLProof.OnlinePrescientLinear

noncomputable section
open Set Finset
open scoped InnerProductSpace
open BanditRL.OnlineGradientDescent BanditRL.OnlinePrescientLinear
namespace Audit.OnlinePrescientLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def firstLeafValue (V : Domain E) (η : ℝ) (hη : 0 < η) (g x u : E)
    (hu : u ∈ V.carrier) :
    inner ℝ g (advance V η g x - u) ≤
      (‖x - u‖ ^ 2 - ‖advance V η g x - u‖ ^ 2 - ‖advance V η g x - x‖ ^ 2) /
        (2 * η) :=
  BanditRL.OnlinePrescientLinear.advance_sharp_bound V η hη g x u hu

#print axioms firstLeafValue
#print axioms BanditRL.OnlinePrescientLinear.advance_sharp_bound
#check @BanditRL.OnlinePrescientLinear.advance_sharp_bound
end Audit.OnlinePrescientLinear
