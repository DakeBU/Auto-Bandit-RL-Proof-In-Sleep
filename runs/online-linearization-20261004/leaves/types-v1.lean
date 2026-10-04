import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineLearningRegret
noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace BanditRL.OnlineLinearization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev LinearPolicy := (t : ℕ) → (Fin t → E) → E
abbrev SupportPolicy := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)
def Feasible (V : Domain (E := E)) (A : LinearPolicy (E := E)) : Prop :=
  ∀ t h, A t h ∈ V.carrier
/-- Reconstruct all outputs from a finite strict-past vector history. -/
def outputHistory (A : LinearPolicy (E := E)) {t : ℕ} (h : Fin t → E) : Fin (t + 1) → E :=
  fun i => A i.val (fun j => h ⟨j.val, by omega⟩)
/-- The current support is appended only after the current output has been made. -/
def history (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) : (t : ℕ) → Fin t → E :=
  Nat.rec (motive := fun t => Fin t → E) Fin.elim0
    (fun t h => Fin.snoc h (p t (fun i => loss i.val) (outputHistory A h) (loss t)))
def output (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (t : ℕ) : E := A t (history A loss p t)
def selected (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (outputHistory A (history A loss p t)) (loss t)
def LegalFeedback (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected A loss p t ∈ SourceSubdifferential (loss t) (output A loss p t)
def linearRun (A : LinearPolicy (E := E)) (g : ℕ → E) (t : ℕ) : E :=
  A t (fun i => g i.val)
def linearLoss (g x : E) : ℝ := inner ℝ g x
def regret (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output A loss p t)).toReal - (loss t u).toReal)
#check (∀ (A : LinearPolicy (E := E)) (t : ℕ) (h : Fin t → E) , 
    outputHistory A h (Fin.last t) = A t h)

#check (∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) , 
    history A loss p 0 = Fin.elim0)

#check (∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) , 
    history A loss p (t + 1) = Fin.snoc (history A loss p t) (selected A loss p t))

#check (∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t) , 
    history A loss p (t + 1) i.castSucc = history A loss p t i)

#check (∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t) , 
    history A loss p t i = selected A loss p i.val)

#check (∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) , 
    output A loss p t = linearRun A (selected A loss p) t)

#check (∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin (t + 1)) , 
    outputHistory A (history A loss p t) i = output A loss p i.val)

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) , 
    output A loss p t ∈ V.carrier)

#check (∀ (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s) , 
    history A loss p t = history A loss' p t)

#check (∀ (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s) , 
    output A loss p t = output A loss' p t)

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (hp : BanditRL.OnlineSubgradientPolicy.OracleLaw V p) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) , 
    LegalFeedback A loss p T)

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) , 
    LegalFeedback A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy T)

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (t : ℕ) (ht : t < T) , 
    loss t (output A loss p t) = ((loss t (output A loss p t)).toReal : EReal))

#check (∀ (V : Domain (E := E)) (f : E → EReal) (hf : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f) (x g u : E) (hu : u ∈ V.carrier) (hg : g ∈ SourceSubdifferential f x) , 
    (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u))

#check (∀ (g x u : E) , 
    linearLoss g x - linearLoss g u = inner ℝ g (x - u))

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback A loss p T) (u : E) (hu : u ∈ V.carrier) , 
    regret A loss p u T ≤ BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (selected A loss p t)) (linearRun A (selected A loss p)) u T)

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback A loss p T) (B : (ℕ → E) → E → ℕ → ℝ) (hB : ∀ g u, u ∈ V.carrier → BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (g t)) (linearRun A g) u T ≤ B g u T) (u : E) (hu : u ∈ V.carrier) , 
    regret A loss p u T ≤ B (selected A loss p) u T)

#check (∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier) , 
    regret A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy u T ≤ BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (selected A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy t)) (linearRun A (selected A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy)) u T)
end BanditRL.OnlineLinearization
