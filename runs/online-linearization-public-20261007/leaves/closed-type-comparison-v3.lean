import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineLearningRegret

noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace NeutralPacket
abbrev Supports {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (x : E) := BanditRL.OnlineConvex.SourceSubdifferential f x
abbrev Regular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V : BanditRL.OnlineGradientDescent.Domain E) (f : E → EReal) := BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f
abbrev Law {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V : BanditRL.OnlineGradientDescent.Domain E) (p : BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)) := BanditRL.OnlineSubgradientPolicy.OracleLaw V p
abbrev Default {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] := BanditRL.OnlineSubgradientPolicy.canonicalPolicy (E := E)
abbrev Comparator {E : Type*} (loss : ℕ → E → ℝ) (prediction : ℕ → E) (u : E) (T : ℕ) := BanditRL.OnlineLearning.comparatorRegret loss prediction u T
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
  ∀ t < T, selected A loss p t ∈ Supports (loss t) (output A loss p t)
def linearRun (A : LinearPolicy (E := E)) (g : ℕ → E) (t : ℕ) : E :=
  A t (fun i => g i.val)
def linearLoss (g x : E) : ℝ := inner ℝ g x
def regret (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output A loss p t)).toReal - (loss t u).toReal)
def Q01 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (t : ℕ) (h : Fin t → E),
  outputHistory A h (Fin.last t) = A t h

def Q02 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)),
  history A loss p 0 = Fin.elim0

def Q03 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ),
  history A loss p (t + 1) = Fin.snoc (history A loss p t) (selected A loss p t)

def Q04 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t),
  history A loss p (t + 1) i.castSucc = history A loss p t i

def Q05 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t),
  history A loss p t i = selected A loss p i.val

def Q06 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ),
  output A loss p t = linearRun A (selected A loss p) t

def Q07 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin (t + 1)),
  outputHistory A (history A loss p t) i = output A loss p i.val

def Q08 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ),
  output A loss p t ∈ V.carrier

def Q09 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s),
  history A loss p t = history A loss' p t

def Q10 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s),
  output A loss p t = output A loss' p t

def Q11 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (hp : Law V p) (T : ℕ) (hloss : ∀ t < T, Regular V (loss t)),
  LegalFeedback A loss p T

def Q12 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, Regular V (loss t)),
  LegalFeedback A loss Default T

def Q13 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, Regular V (loss t)) (t : ℕ) (ht : t < T),
  loss t (output A loss p t) = ((loss t (output A loss p t)).toReal : EReal)

def Q14 : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal) (hf : Regular V f) (x g u : E) (hu : u ∈ V.carrier) (hg : g ∈ Supports f x),
  (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u)

def Q15 : Prop :=
  ∀ (g x u : E),
  linearLoss g x - linearLoss g u = inner ℝ g (x - u)

def Q16 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, Regular V (loss t)) (hlegal : LegalFeedback A loss p T) (u : E) (hu : u ∈ V.carrier),
  regret A loss p u T ≤ Comparator (fun t => linearLoss (selected A loss p t)) (linearRun A (selected A loss p)) u T

def Q17 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, Regular V (loss t)) (hlegal : LegalFeedback A loss p T) (B : (ℕ → E) → E → ℕ → ℝ) (hB : ∀ g u, u ∈ V.carrier → Comparator (fun t => linearLoss (g t)) (linearRun A g) u T ≤ B g u T) (u : E) (hu : u ∈ V.carrier),
  regret A loss p u T ≤ B (selected A loss p) u T

def Q18 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, Regular V (loss t)) (u : E) (hu : u ∈ V.carrier),
  regret A loss Default u T ≤ Comparator (fun t => linearLoss (selected A loss Default t)) (linearRun A (selected A loss Default)) u T
#check Q01
#check Q02
#check Q03
#check Q04
#check Q05
#check Q06
#check Q07
#check Q08
#check Q09
#check Q10
#check Q11
#check Q12
#check Q13
#check Q14
#check Q15
#check Q16
#check Q17
#check Q18
end NeutralPacket

noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace CurrentClosedTypes
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
def S01 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (t : ℕ) (h : Fin t → E),
  outputHistory A h (Fin.last t) = A t h

def S02 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)),
  history A loss p 0 = Fin.elim0

def S03 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ),
  history A loss p (t + 1) = Fin.snoc (history A loss p t) (selected A loss p t)

def S04 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t),
  history A loss p (t + 1) i.castSucc = history A loss p t i

def S05 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t),
  history A loss p t i = selected A loss p i.val

def S06 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ),
  output A loss p t = linearRun A (selected A loss p) t

def S07 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin (t + 1)),
  outputHistory A (history A loss p t) i = output A loss p i.val

def S08 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ),
  output A loss p t ∈ V.carrier

def S09 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s),
  history A loss p t = history A loss' p t

def S10 : Prop :=
  ∀ (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s),
  output A loss p t = output A loss' p t

def S11 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (hp : BanditRL.OnlineSubgradientPolicy.OracleLaw V p) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)),
  LegalFeedback A loss p T

def S12 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)),
  LegalFeedback A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy T

def S13 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (t : ℕ) (ht : t < T),
  loss t (output A loss p t) = ((loss t (output A loss p t)).toReal : EReal)

def S14 : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal) (hf : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f) (x g u : E) (hu : u ∈ V.carrier) (hg : g ∈ SourceSubdifferential f x),
  (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u)

def S15 : Prop :=
  ∀ (g x u : E),
  linearLoss g x - linearLoss g u = inner ℝ g (x - u)

def S16 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback A loss p T) (u : E) (hu : u ∈ V.carrier),
  regret A loss p u T ≤ BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (selected A loss p t)) (linearRun A (selected A loss p)) u T

def S17 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback A loss p T) (B : (ℕ → E) → E → ℕ → ℝ) (hB : ∀ g u, u ∈ V.carrier → BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (g t)) (linearRun A g) u T ≤ B g u T) (u : E) (hu : u ∈ V.carrier),
  regret A loss p u T ≤ B (selected A loss p) u T

def S18 : Prop :=
  ∀ (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
  regret A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy u T ≤ BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (selected A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy t)) (linearRun A (selected A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy)) u T
end CurrentClosedTypes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
example : NeutralPacket.Q01 (E := E) = CurrentClosedTypes.S01 (E := E) := rfl
example : NeutralPacket.Q02 (E := E) = CurrentClosedTypes.S02 (E := E) := rfl
example : NeutralPacket.Q03 (E := E) = CurrentClosedTypes.S03 (E := E) := rfl
example : NeutralPacket.Q04 (E := E) = CurrentClosedTypes.S04 (E := E) := rfl
example : NeutralPacket.Q05 (E := E) = CurrentClosedTypes.S05 (E := E) := rfl
example : NeutralPacket.Q06 (E := E) = CurrentClosedTypes.S06 (E := E) := rfl
example : NeutralPacket.Q07 (E := E) = CurrentClosedTypes.S07 (E := E) := rfl
example : NeutralPacket.Q08 (E := E) = CurrentClosedTypes.S08 (E := E) := rfl
example : NeutralPacket.Q09 (E := E) = CurrentClosedTypes.S09 (E := E) := rfl
example : NeutralPacket.Q10 (E := E) = CurrentClosedTypes.S10 (E := E) := rfl
example : NeutralPacket.Q11 (E := E) = CurrentClosedTypes.S11 (E := E) := rfl
example : NeutralPacket.Q12 (E := E) = CurrentClosedTypes.S12 (E := E) := rfl
example : NeutralPacket.Q13 (E := E) = CurrentClosedTypes.S13 (E := E) := rfl
example : NeutralPacket.Q14 (E := E) = CurrentClosedTypes.S14 (E := E) := rfl
example : NeutralPacket.Q15 (E := E) = CurrentClosedTypes.S15 (E := E) := rfl
example : NeutralPacket.Q16 (E := E) = CurrentClosedTypes.S16 (E := E) := rfl
example : NeutralPacket.Q17 (E := E) = CurrentClosedTypes.S17 (E := E) := rfl
example : NeutralPacket.Q18 (E := E) = CurrentClosedTypes.S18 (E := E) := rfl
