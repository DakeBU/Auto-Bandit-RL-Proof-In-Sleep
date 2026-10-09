import BanditRLProof.OnlinePrescientLinear
noncomputable section
open Set Finset
open scoped InnerProductSpace
open BanditRL.OnlineGradientDescent (Domain)
open BanditRL.OnlinePrescientLinear
namespace Audit.Prescient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
def publicValue1 (V : Domain E) (η : ℝ) (hη : 0 < η) (g x u : E)
    (hu : u ∈ V.carrier) :
    inner ℝ g (advance V η g x - u) ≤
      (‖x - u‖ ^ 2 - ‖advance V η g x - u‖ ^ 2 - ‖advance V η g x - x‖ ^ 2) /
        (2 * η) :=
  BanditRL.OnlinePrescientLinear.advance_sharp_bound V η hη g x u hu

#print axioms publicValue1
#print axioms BanditRL.OnlinePrescientLinear.advance_sharp_bound
#check @BanditRL.OnlinePrescientLinear.advance_sharp_bound

def publicValue2 (V : Domain E) (η : ℝ) (hη : 0 < η) (g x : E)
    (b : ℝ) :
    advance V η g x ∈ V.carrier ∧ ∀ u ∈ V.carrier,
      inner ℝ g (advance V η g x) + b + ‖advance V η g x - x‖ ^ 2 / (2 * η) ≤
        inner ℝ g u + b + ‖u - x‖ ^ 2 / (2 * η) :=
  BanditRL.OnlinePrescientLinear.advance_proximal_minimizer V η hη g x b

#print axioms publicValue2
#print axioms BanditRL.OnlinePrescientLinear.advance_proximal_minimizer
#check @BanditRL.OnlinePrescientLinear.advance_proximal_minimizer

def publicValue3 (V : Domain E) (η : ℝ) (g : ℕ → E) (x0 : E) (t : ℕ) :
    prediction V η g x0 t ∈ V.carrier :=
  BanditRL.OnlinePrescientLinear.prediction_mem V η g x0 t

#print axioms publicValue3
#print axioms BanditRL.OnlinePrescientLinear.prediction_mem
#check @BanditRL.OnlinePrescientLinear.prediction_mem

def publicValue4 (V : Domain E) (η : ℝ) (g g' : ℕ → E) (x0 : E) (t : ℕ)
    (h : ∀ s ≤ t, g s = g' s) :
    prediction V η g x0 t = prediction V η g' x0 t :=
  BanditRL.OnlinePrescientLinear.prediction_prefix V η g g' x0 t h

#print axioms publicValue4
#print axioms BanditRL.OnlinePrescientLinear.prediction_prefix
#check @BanditRL.OnlinePrescientLinear.prediction_prefix

def publicValue5 (V : Domain E) (η : ℝ) (g : ℕ → E) (b : ℕ → ℝ)
    (x0 u : E) (T : ℕ) :
    regret V η g x0 u T =
      ∑ t ∈ range T, ((inner ℝ (g t) (prediction V η g x0 t) + b t) -
        (inner ℝ (g t) u + b t)) :=
  BanditRL.OnlinePrescientLinear.regret_eq_loss_difference V η g b x0 u T

#print axioms publicValue5
#print axioms BanditRL.OnlinePrescientLinear.regret_eq_loss_difference
#check @BanditRL.OnlinePrescientLinear.regret_eq_loss_difference

def publicValue6 (V : Domain E) (η : ℝ) (hη : 0 < η) (g : ℕ → E)
    (x0 u : E) (T : ℕ) (hu : u ∈ V.carrier) :
    regret V η g x0 u T ≤ ‖x0 - u‖ ^ 2 / (2 * η) -
      ‖iterate V η g x0 T - u‖ ^ 2 / (2 * η) -
      (∑ t ∈ range T, ‖prediction V η g x0 t - iterate V η g x0 t‖ ^ 2) / (2 * η) :=
  BanditRL.OnlinePrescientLinear.regret_sharp_bound V η hη g x0 u T hu

#print axioms publicValue6
#print axioms BanditRL.OnlinePrescientLinear.regret_sharp_bound
#check @BanditRL.OnlinePrescientLinear.regret_sharp_bound

def publicValue7 (V : Domain E) (η : ℝ) (hη : 0 < η) (g : ℕ → E)
    (x0 u : E) (T : ℕ) (hu : u ∈ V.carrier) :
    regret V η g x0 u T ≤ ‖x0 - u‖ ^ 2 / (2 * η) -
      (∑ t ∈ range T, ‖prediction V η g x0 t - iterate V η g x0 t‖ ^ 2) / (2 * η) :=
  BanditRL.OnlinePrescientLinear.regret_source_bound V η hη g x0 u T hu

#print axioms publicValue7
#print axioms BanditRL.OnlinePrescientLinear.regret_source_bound
#check @BanditRL.OnlinePrescientLinear.regret_source_bound

end Audit.Prescient
