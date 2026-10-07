Restricted source-blind packet. Requested GPT6Astra/medium only. Read ONLY this packet, no repository/source/proof/prior-verdict search. Reconstruct P01-P21 individually in natural language/LaTeX and seven semantic slots. Disclose any prior neutral-decoder context; no source identity or source acceptance is provided. Write ONLY blind-reconstruction-v1.md / blind-receipt-v1.json adjacent, with raw packet/report SHA, actor.task=/root/osd_blind, requested settings and runtime_model_attested=false. These are fully elaborated proposition descriptions, NOT proofs of the targets. Mathematical definitions are context, not assumed performance bounds.

The finite-dimensional real inner-product space has a nonempty closed convex domain and actual nearest projection. Proper losses are nowhere bottom and finite somewhere; supports test ALL ambient comparisons. EReal.toReal maps BOTH infinities to zero, so finite-value production matters. The policy receives time, exactly Fin t past whole losses, Fin(t+1) actual outputs and current whole loss; recursion appends the actual projection. Played legality differs from the stronger OPTIONAL universal off-path law. Policy/initialization/schedules are prescribed exogenous parameters; strict-prefix comparison keeps p/x1 fixed and compares whole past loss functions/rates. No probability law, measurability, external-parameter independence, executable finite-query oracle or anytime assertion. Audit source-round1/Lean0 indexing, output T endpoint, same actual chosen supports and same tuned eta-dependent run, all residual signs/denominators/constant halves, fixed T0/unbounded versus variable T>0/actual bounded metric diameter, distance-versus-all-comparator tuning with positive D/G/T, and exact identity adapters for the current-only choice. Distinguish structural consequences from any literature attribution, which is not supplied.

```lean
import BanditRLProof.OnlineSubgradientDescent


noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace NeutralHistory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev SupportPolicy := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E

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

def LegalFeedback (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal)

def P01 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)),
    history V η loss x₁ p 0 = fun _ => x₁

def P02 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ),
    history V η loss x₁ p (t + 1) =
      Fin.snoc (history V η loss x₁ p t)
        (BanditRL.OnlineGradientDescent.project V
          (output V η loss x₁ p t - η t • selected V η loss x₁ p t))

def P03 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)),
    output V η loss x₁ p 0 = x₁

def P04 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ),
    output V η loss x₁ p (t + 1) =
      BanditRL.OnlineGradientDescent.project V
        (output V η loss x₁ p t - η t • selected V η loss x₁ p t)

def P05 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (i : Fin (t + 1)),
    history V η loss x₁ p t i ∈ V.carrier

def P06 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ),
    output V η loss x₁ p t ∈ V.carrier

def P07 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s),
    history V η loss x₁ p t = history V η' loss' x₁ p t

def P08 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s),
    output V η loss x₁ p t = output V η' loss' x₁ p t

def P09 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hp : OracleLaw V p)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)),
    LegalFeedback V η loss x₁ p T

def P10 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier),
    loss t (output V η loss x₁ p t) = ((loss t (output V η loss x₁ p t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal)

def P11 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) (hη : 0 < η t)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t))
    (u : E) (hu : u ∈ V.carrier),
    η t * ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal) ≤
      η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ∧
    η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ≤
      ‖output V η loss x₁ p t - u‖ ^ 2 / 2 -
      ‖output V η loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
      (η t) ^ 2 / 2 * ‖selected V η loss x₁ p t‖ ^ 2

def P12 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) (hη : 0 < η t)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t))
    (u : E) (hu : u ∈ V.carrier),
    (loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal ≤
      (‖output V η loss x₁ p t - u‖ ^ 2 -
        ‖output V η loss x₁ p (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2

def P13 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))
    (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) (hu : u ∈ V.carrier),
    regret V (fun _ => η) loss x₁ p u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) -
      ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η)

def P14 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))
    (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) (hu : u ∈ V.carrier),
    regret V (fun _ => η) loss x₁ p u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2)

def P15 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V η loss x₁ p T) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier),
    regret V η loss x₁ p u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) -
      ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1))

def P16 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V η loss x₁ p T) (hV : Bornology.IsBounded V.carrier) (u : E) (hu : u ∈ V.carrier),
    regret V η loss x₁ p u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) -
      ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1))

def P17 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T, ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ≤ G),
    regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ p u T ≤ D * G * Real.sqrt T

def P18 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (hgrad : ∀ t < T, ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ≤ G),
    ∀ u ∈ V.carrier,
      regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ p u T ≤ D * G * Real.sqrt T

def P19 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)),
    OracleLaw V (canonicalPolicy (E := E))

def P20 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (t : ℕ),
    output V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t

def P21 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (t : ℕ),
    selected V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.currentSubgradient (loss t)
        (BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t)
#print BanditRL.OnlineGradientDescent.Domain
#check @BanditRL.OnlineGradientDescent.project_spec
#print BanditRL.OnlineConvex.SourceProper
#print BanditRL.OnlineConvex.SourceSubdifferential
#print BanditRL.OnlineSubgradientDescent.SubdifferentiableOn
#print BanditRL.OnlineSubgradientDescent.currentSubgradient
#print BanditRL.OnlineSubgradientDescent.step
#print BanditRL.OnlineSubgradientDescent.iterate
#print EReal.toReal
#print Metric.diam
#print P01
#print P02
#print P03
#print P04
#print P05
#print P06
#print P07
#print P08
#print P09
#print P10
#print P11
#print P12
#print P13
#print P14
#print P15
#print P16
#print P17
#print P18
#print P19
#print P20
#print P21
end NeutralHistory

```
Actual standalone elaboration and borrowed context (target proofs omitted):
```text
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:63:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:68:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:74:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:74:32: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:80:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:80:32: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:85:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:86:5: warning: unused variable `hp`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:87:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:92:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:93:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:94:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:100:51: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:101:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:102:5: warning: unused variable `hg`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:103:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:113:51: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:114:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:115:5: warning: unused variable `hg`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:116:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:123:35: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:125:5: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:126:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:127:5: warning: unused variable `hlegal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:127:65: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:133:35: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:135:5: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:136:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:137:5: warning: unused variable `hlegal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:137:65: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:143:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:143:74: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:144:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:144:29: warning: unused variable `hmono`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:145:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:146:5: warning: unused variable `hlegal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:147:5: warning: unused variable `hdiam`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:148:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:155:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:155:74: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:156:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:156:29: warning: unused variable `hmono`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:157:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:158:5: warning: unused variable `hlegal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:158:46: warning: unused variable `hV`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:158:91: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:165:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:166:13: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:166:36: warning: unused variable `hD`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:166:49: warning: unused variable `hG`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:167:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:168:5: warning: unused variable `hlegal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:168:85: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:169:5: warning: unused variable `hdist`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:170:5: warning: unused variable `hgrad`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:175:43: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:176:13: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:176:36: warning: unused variable `hD`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:176:49: warning: unused variable `hG`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:177:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:178:5: warning: unused variable `hlegal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:179:5: warning: unused variable `hdiam`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:180:5: warning: unused variable `hgrad`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-policy-public-20261007\leaves\neutral-propositions-v1.lean:184:9: warning: unused variable `instFD`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
structure BanditRL.OnlineGradientDescent.Domain.{u_2} (E : Type u_2) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
  Type u_2
number of parameters: 3
fields:
  BanditRL.OnlineGradientDescent.Domain.carrier : Set E
  BanditRL.OnlineGradientDescent.Domain.nonempty : self.carrier.Nonempty
  BanditRL.OnlineGradientDescent.Domain.closed : IsClosed self.carrier
  BanditRL.OnlineGradientDescent.Domain.convex : Convex ℝ self.carrier
constructor:
  BanditRL.OnlineGradientDescent.Domain.mk.{u_2} {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (carrier : Set E) (nonempty : carrier.Nonempty) (closed : IsClosed carrier) (convex : Convex ℝ carrier) :
    BanditRL.OnlineGradientDescent.Domain E
@BanditRL.OnlineGradientDescent.project_spec : ∀ {E : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (V : BanditRL.OnlineGradientDescent.Domain E) (z : E),
  BanditRL.OnlineGradientDescent.project V z ∈ V.carrier ∧
    ‖z - BanditRL.OnlineGradientDescent.project V z‖ = ⨅ w, ‖z - ↑w‖
def BanditRL.OnlineConvex.SourceProper.{u_1} : {E : Type u_1} → (E → EReal) → Prop :=
fun {E} f => (∀ (x : E), f x ≠ ⊥) ∧ ∃ x r, f x = ↑r
def BanditRL.OnlineConvex.SourceSubdifferential.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → (E → EReal) → E → Set E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] f x => {g | ∀ (y : E), f x + ↑(inner ℝ g (y - x)) ≤ f y}
def BanditRL.OnlineSubgradientDescent.SubdifferentiableOn.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℝ E] → BanditRL.OnlineSubgradientDescent.Domain → (E → EReal) → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] V f =>
  SourceProper f ∧ ∀ x ∈ V.carrier, (SourceSubdifferential f x).Nonempty
def BanditRL.OnlineSubgradientDescent.currentSubgradient.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → (E → EReal) → E → E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] f x =>
  if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
def BanditRL.OnlineSubgradientDescent.step.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℝ E] →
      [FiniteDimensional ℝ E] → BanditRL.OnlineSubgradientDescent.Domain → ℝ → (E → EReal) → E → E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] V η f x =>
  BanditRL.OnlineGradientDescent.project V (x - η • BanditRL.OnlineSubgradientDescent.currentSubgradient f x)
def BanditRL.OnlineSubgradientDescent.iterate.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℝ E] →
      [FiniteDimensional ℝ E] → BanditRL.OnlineSubgradientDescent.Domain → (ℕ → ℝ) → (ℕ → E → EReal) → E → ℕ → E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] V η loss x₁ x =>
  Nat.brecOn x fun x f =>
    (match (motive := (x : ℕ) → Nat.below x → E) x with
      | 0 => fun x => x₁
      | t.succ => fun x => BanditRL.OnlineSubgradientDescent.step V (η t) (loss t) x.1)
      f
def EReal.toReal : EReal → ℝ :=
fun x =>
  match x with
  | none => 0
  | some none => 0
  | some (some x) => x
def Metric.diam.{u} : {α : Type u} → [PseudoMetricSpace α] → Set α → ℝ :=
fun {α} [PseudoMetricSpace α] s => (Metric.ediam s).toReal
def NeutralHistory.P01.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy), history V η loss x₁ p 0 = fun x => x₁
def NeutralHistory.P02.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy) (t : ℕ),
    history V η loss x₁ p (t + 1) =
      Fin.snoc (history V η loss x₁ p t)
        (BanditRL.OnlineGradientDescent.project V (output V η loss x₁ p t - η t • selected V η loss x₁ p t))
def NeutralHistory.P03.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy), output V η loss x₁ p 0 = x₁
def NeutralHistory.P04.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy) (t : ℕ),
    output V η loss x₁ p (t + 1) =
      BanditRL.OnlineGradientDescent.project V (output V η loss x₁ p t - η t • selected V η loss x₁ p t)
def NeutralHistory.P05.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier → ∀ (t : ℕ) (i : Fin (t + 1)), history V η loss x₁ p t i ∈ V.carrier
def NeutralHistory.P06.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier → ∀ (t : ℕ), output V η loss x₁ p t ∈ V.carrier
def NeutralHistory.P07.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η η' : ℕ → ℝ) (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy) (t : ℕ),
    (∀ s < t, η s = η' s) → (∀ s < t, loss s = loss' s) → history V η loss x₁ p t = history V η' loss' x₁ p t
def NeutralHistory.P08.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η η' : ℕ → ℝ) (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy) (t : ℕ),
    (∀ s < t, η s = η' s) → (∀ s < t, loss s = loss' s) → output V η loss x₁ p t = output V η' loss' x₁ p t
def NeutralHistory.P09.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier →
      ∀ (T : ℕ),
        OracleLaw V p →
          (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) → LegalFeedback V η loss x₁ p T
def NeutralHistory.P10.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier →
      ∀ (t : ℕ),
        BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t) →
          ∀ u ∈ V.carrier,
            loss t (output V η loss x₁ p t) = ↑(loss t (output V η loss x₁ p t)).toReal ∧ loss t u = ↑(loss t u).toReal
def NeutralHistory.P11.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy) (t : ℕ),
    0 < η t →
      BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t) →
        selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t) →
          ∀ u ∈ V.carrier,
            η t * ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal) ≤
                η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ∧
              η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ≤
                ‖output V η loss x₁ p t - u‖ ^ 2 / 2 - ‖output V η loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
                  η t ^ 2 / 2 * ‖selected V η loss x₁ p t‖ ^ 2
def NeutralHistory.P12.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy) (t : ℕ),
    0 < η t →
      BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t) →
        selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t) →
          ∀ u ∈ V.carrier,
            (loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal ≤
              (‖output V η loss x₁ p t - u‖ ^ 2 - ‖output V η loss x₁ p (t + 1) - u‖ ^ 2) / (2 * η t) +
                η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2
def NeutralHistory.P13.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℝ),
    0 < η →
      ∀ (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
        x₁ ∈ V.carrier →
          ∀ (T : ℕ),
            (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) →
              LegalFeedback V (fun x => η) loss x₁ p T →
                ∀ u ∈ V.carrier,
                  regret V (fun x => η) loss x₁ p u T ≤
                    ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖selected V (fun x => η) loss x₁ p t‖ ^ 2 -
                      ‖output V (fun x => η) loss x₁ p T - u‖ ^ 2 / (2 * η)
def NeutralHistory.P14.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℝ),
    0 < η →
      ∀ (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
        x₁ ∈ V.carrier →
          ∀ (T : ℕ),
            (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) →
              LegalFeedback V (fun x => η) loss x₁ p T →
                ∀ u ∈ V.carrier,
                  regret V (fun x => η) loss x₁ p u T ≤
                    ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖selected V (fun x => η) loss x₁ p t‖ ^ 2
def NeutralHistory.P15.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier →
      ∀ (T : ℕ),
        0 < T →
          (∀ t < T, 0 < η t) →
            (∀ (t : ℕ), t + 1 < T → η (t + 1) ≤ η t) →
              (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) →
                LegalFeedback V η loss x₁ p T →
                  ∀ (D : ℝ),
                    (∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) →
                      ∀ u ∈ V.carrier,
                        regret V η loss x₁ p u T ≤
                          D ^ 2 / (2 * η (T - 1)) + ∑ t ∈ Finset.range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2 -
                            ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1))
def NeutralHistory.P16.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier →
      ∀ (T : ℕ),
        0 < T →
          (∀ t < T, 0 < η t) →
            (∀ (t : ℕ), t + 1 < T → η (t + 1) ≤ η t) →
              (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) →
                LegalFeedback V η loss x₁ p T →
                  Bornology.IsBounded V.carrier →
                    ∀ u ∈ V.carrier,
                      regret V η loss x₁ p u T ≤
                        Metric.diam V.carrier ^ 2 / (2 * η (T - 1)) +
                            ∑ t ∈ Finset.range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2 -
                          ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1))
def NeutralHistory.P17.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier →
      ∀ (T : ℕ),
        0 < T →
          ∀ (D G : ℝ),
            0 < D →
              0 < G →
                (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) →
                  LegalFeedback V (fun x => D / (G * √↑T)) loss x₁ p T →
                    ∀ u ∈ V.carrier,
                      ‖x₁ - u‖ ≤ D →
                        (∀ t < T, ‖selected V (fun x => D / (G * √↑T)) loss x₁ p t‖ ≤ G) →
                          regret V (fun x => D / (G * √↑T)) loss x₁ p u T ≤ D * G * √↑T
def NeutralHistory.P18.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy),
    x₁ ∈ V.carrier →
      ∀ (T : ℕ),
        0 < T →
          ∀ (D G : ℝ),
            0 < D →
              0 < G →
                (∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) →
                  LegalFeedback V (fun x => D / (G * √↑T)) loss x₁ p T →
                    (∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) →
                      (∀ t < T, ‖selected V (fun x => D / (G * √↑T)) loss x₁ p t‖ ≤ G) →
                        ∀ u ∈ V.carrier, regret V (fun x => D / (G * √↑T)) loss x₁ p u T ≤ D * G * √↑T
def NeutralHistory.P19.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain), OracleLaw V canonicalPolicy
def NeutralHistory.P20.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (t : ℕ),
    output V η loss x₁ canonicalPolicy t = BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t
def NeutralHistory.P21.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [instFD : FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (t : ℕ),
    selected V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.currentSubgradient (loss t)
        (BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t)

```
