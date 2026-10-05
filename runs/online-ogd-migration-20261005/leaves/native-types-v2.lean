import BanditRLProof.OnlineGradientDescentVariable
import BanditRLProof.OnlineConvexFirstOrder
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace BanditRL.OnlineGradientDescentSource
open BanditRL.OnlineGradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def FeasibleRegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ V.carrier f ∧ ∀ x ∈ V.carrier, DifferentiableAt ℝ f x

def SourceRegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V.carrier ⊆ U ∧
    ConvexOn ℝ V.carrier f ∧ DifferentiableOn ℝ f U

def Type1 : Prop := ∀ (V : Domain E) (f : E → ℝ) (hf : SourceRegularLoss V f), FeasibleRegularLoss V f
#check @Type1
def Type2 : Prop := ∀ (V : Domain E) (f : E → ℝ) (hf : RegularLoss V f), FeasibleRegularLoss V f
#check @Type2
def Type3 : Prop := ∀ (V : Domain E) (g : E), RegularLoss V (fun z => inner ℝ g z)
#check @Type3
def Type4 : Prop := ∀ (g x : E), gradient (fun z => inner ℝ g z) x = g
#check @Type4
def Type5 : Prop := ∀ (V : Domain E) (f : E → ℝ) (hf : FeasibleRegularLoss V f) (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier), f x - f u ≤ inner ℝ (gradient f x) (x - u)
#check @Type5
def Type6 : Prop := ∀ (V : Domain E) (f : E → ℝ) (hf : FeasibleRegularLoss V f) (η : ℝ) (hη : 0 < η) (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier), η * (f x - f u) ≤ η * inner ℝ (gradient f x) (x - u) ∧ η * inner ℝ (gradient f x) (x - u) ≤ ‖x - u‖ ^ 2 / 2 - ‖step V η f x - u‖ ^ 2 / 2 + η ^ 2 / 2 * ‖gradient f x‖ ^ 2
#check @Type6
def Type7 : Prop := ∀ (V : Domain E) (η : ℝ) (hη : 0 < η) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier), regret V η loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) - ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η)
#check @Type7
def Type8 : Prop := ∀ (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (hη : 0 < η t) (hloss : FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier), loss t (iterateVariable V η loss x₁ t) - loss t u ≤ (‖iterateVariable V η loss x₁ t - u‖ ^ 2 - ‖iterateVariable V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) + η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2
#check @Type8
def Type9 : Prop := ∀ (V : Domain E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (D : ℝ) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier), regretVariable V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) - ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))
#check @Type9
def Type10 : Prop := ∀ (V : Domain E) (hV : Bornology.IsBounded V.carrier) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier), regretVariable V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (iterateVariable V η loss x₁ t)‖ ^ 2) - ‖iterateVariable V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))
#check @Type10
def Type11 : Prop := ∀ (V : Domain E) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) (hdist : ‖x₁ - u‖ ≤ D) (hgrad : ∀ t < T, ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G), regret V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T
#check @Type11
def Type12 : Prop := ∀ (V : Domain E) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (hloss : ∀ t < T, FeasibleRegularLoss V (loss t)) (hgrad : ∀ t < T, ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G), ∀ u ∈ V.carrier, regret V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T
#check @Type12
end BanditRL.OnlineGradientDescentSource

