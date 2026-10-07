Decode ONLY this neutral complete packet. Source identity/theorem names/prior source verdict withheld. Requested GPT-6 Astra/medium, runtime not attested; disclose any prior neutral-decoder history. Do not inspect repository/source/search/network/other packets. Return allQ01..Q18 full NL and LaTeX reconstruction with seven semantic slots, quantifiers/regularity/current and past inputs/full actual recursion/comparator and finite conversion/universal guarantee boundary/degeneracies. No source acceptance claim.

Complete semantic context: E finite-dimensional real Euclidean space. Domain is shared nonempty closed convex set with carrier field, no boundedness. Proper(f) = (forall x, f(x) != bottom) and (exists x exists r:Real, f(x)=(r:EReal)). Supports(f,x) means forall v:E, f(x)+(inner g(v-x):EReal)<=f(v). Regular(V,f)=Proper(f) and every x in V has a nonempty global support set. SupportPolicy p: t -> finite t past whole functions -> finite (t+1) reconstructed outputs -> whole current function -> vector. Law(V,p) states forall t,past,h,f, Regular(V,f) and h(last t) in V -> p(t,past,h,f) in Supports(f,h(last t)); it is an optional off-path law. Default p ignores past and chooses from nonempty current global Supports by Classical.choose, otherwise0. Comparator(loss,prediction,u,T) is the difference of played and comparator sums over range T. A fixed finite-vector learner reads only strict past vectors. All supplied recursion definitions are literal and complete below. EReal.toReal is totalized, so finite-value derivation must not be omitted. No comparator/future functions queried by A/p; external construction of A/p has no independent stochastic-law guarantee. T0 empty extension; indexing0based. Decode only mathematics, no claimed source fidelity/acceptance.
```lean
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
```
