Restricted source-blind packet. Read ONLY this packet. No source/proof/prior verdict/repo search. Requested GPT6Astra/medium, runtime attestation unavailable. Reconstruct Q01-Q04 individually in natural language and LaTeX and all seven semantic slots. Disclose inherited neutral-decoder context; do not infer source identity/acceptance. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json beside this file; raw packet/report SHA256 and actor.task=/root/osd_blind. These are fully elaborated target proposition descriptions, NOT proofs.
W is the nonempty closed convex [0,1] real domain; project is actual nearest projection. b is finite real absolute loss embedded in EReal. EReal.toReal maps both infinities to zero, but b is finite everywhere. F/X/A/L are exact aliases of the following common context at real E. Global support membership means f(x)+g(z-x)<=f(z) for EVERY real z. A fixed exogenous policy has only the displayed finite explicit inputs; no promise about how exogenous parameters were chosen is implied. No probability or finite-query implementation is provided.
Shared mathematical context, no performance assumptions:
```lean
noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace BanditRL.OnlineSubgradientPolicy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev SupportPolicy := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E
/-- Only finite past losses/outputs and the currently observed loss are inputs. -/
def history (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) : (t : ℕ) → Fin (t + 1) → E :=
  Nat.rec (motive := fun t => Fin (t + 1) → E) (fun _ => x₁)
    (fun t h => Fin.snoc h
      (BanditRL.OnlineGradientDescent.project V
        (h (Fin.last t) - η t • p t (fun i => loss i.val) h (loss t))))
def output (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  history V η loss x₁ p t (Fin.last t)
def selected (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (history V η loss x₁ p t) (loss t)
def OracleLaw (V : Domain (E := E)) (p : SupportPolicy (E := E)) : Prop :=
  ∀ t past h f, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f →
    h (Fin.last t) ∈ V.carrier → p t past h f ∈ SourceSubdifferential f (h (Fin.last t))
def canonicalPolicy : SupportPolicy (E := E) := fun t _ h f =>
  BanditRL.OnlineSubgradientDescent.currentSubgradient f (h (Fin.last t))
/-- Legality is imposed only at the actual played points, not at off-path histories. -/
def LegalFeedback (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal)
```
Complete typed targets:
```lean
import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineGuessingOGD
noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
namespace NeutralScalarHistory
abbrev W := BanditRL.OnlineGradientDescent.unitInterval
abbrev F := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := ℝ)
abbrev X  := BanditRL.OnlineSubgradientPolicy.output (E := ℝ)
abbrev A  := BanditRL.OnlineSubgradientPolicy.selected (E := ℝ)
abbrev L  := BanditRL.OnlineSubgradientPolicy.LegalFeedback (E := ℝ)
def b (y x : ℝ) : EReal := ((|x-y| : ℝ) : EReal)
def Q01 : Prop :=
  ∀ (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : F) (T : ℕ)
    (hlegal : L W η (fun s => b (y s)) x₁ p T)
    (t : ℕ) (ht : t < T),
    ‖A W η (fun s => b (y s)) x₁ p t‖ ≤ 1

def Q02 : Prop :=
  ∀ (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : F) (t : ℕ),
    X W η (fun s => b (y s)) x₁ p (t + 1) =
      min (max (X W η (fun s => b (y s)) x₁ p t -
        η t * A W η (fun s => b (y s)) x₁ p t) 0) 1

def Q03 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ) (p : F)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : L W (fun _ => 1 / Real.sqrt T)
      (fun s => b (y s)) x₁ p T),
    ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|X W (fun _ => 1 / Real.sqrt T)
          (fun s => b (y s)) x₁ p t - y t| - |u - y t|)) ≤ Real.sqrt T

def Q04 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ)
    (p : F) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : ∀ T : ℕ, 0 < T → L W
      (fun _ => 1 / Real.sqrt T) (fun s => b (y s)) x₁ p T)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε),
    ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|X W (fun _ => 1 / Real.sqrt T)
          (fun s => b (y s)) x₁ p t - y t| - |u - y t|)) / T < ε
end NeutralScalarHistory

```
