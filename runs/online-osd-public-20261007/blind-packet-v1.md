Restricted neutral packet. Requested GPT6Astra/medium. Read ONLY this packet: no source/repository search, proof bodies, literature identity or previous verdict. Reconstruct P01-P15 individually in natural language/LaTeX and seven semantic slots; all needed structural definitions, borrowed actual types and elaboration output follow. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent, with raw packet/report SHA256, actor/requested settings and no runtime attestation/source acceptance. These are actual fully elaborated proposition definitions, NOT proofs of the targets. Mathematical definitions of choice/recursion are context, not assumed performance inequalities.

The real inner-product space is finite dimensional. Borrowed Domain is nonempty closed convex, and project_spec states actual nearest-point membership/minimization. Properness means nowhere bottom and finite somewhere; global supports test EVERY ambient comparison. Actual loss finiteness must precede real differences. Current selector takes f,x only, canonical noncomputable choice from an actual nonempty support set or otherwise zero. Initial value and schedule externally prescribed. Whole-function strict-prefix equality has its literal quantifier scope; a future-dependent external initial value is not constrained by this packet. All claims concern one specified choice/recursion, not every legal support policy or an executable oracle. Fixed0 horizon, variablepositive horizon/last played schedule, bounded diameter and actual same-run support bound are distinct hypotheses. No probability/filtration/measurability/anytime assertion. Audit arbitrary current query versus feasible comparator, ambient global support versus interior support, EReal finiteness versus unconditional toReal, actual algorithm versus supplied single-step performance premise, and all sign/constants/residual/index boundaries.

```lean
import BanditRLProof.OnlineGradientDescentVariable
import BanditRLProof.OnlineLipschitzSubgradient
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace NeutralUpdate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E

def SubdifferentiableOn (V : Domain (E := E)) (f : E → EReal) : Prop :=
  SourceProper f ∧ ∀ x ∈ V.carrier, (SourceSubdifferential f x).Nonempty

def currentSubgradient (f : E → EReal) (x : E) : E :=
  by
    classical
    exact if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)

def P01 : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x),
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2

def P02 : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal)
    (hf : SubdifferentiableOn V f) (x : E) (hx : x ∈ V.carrier),
    currentSubgradient f x ∈ SourceSubdifferential f x

def P03 : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal)
    (hf : SubdifferentiableOn V f) (x : E) (hx : x ∈ V.carrier),
    f x = ((f x).toReal : EReal)

def P04 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ),
    iterate V η loss x₁ t ∈ V.carrier

def P05 : Prop :=
  ∀ (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s),
    iterate V η loss x₁ t = iterate V η' loss' x₁ t

def P06 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : SubdifferentiableOn V (loss t)),
    currentSubgradient (loss t) (iterate V η loss x₁ t) ∈
      SourceSubdifferential (loss t) (iterate V η loss x₁ t)

def P07 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    loss t (iterate V η loss x₁ t) = ((loss t (iterate V η loss x₁ t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal)

def P08 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hη : 0 < η t) (hloss : SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier),
    η t * ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal) ≤
      η t * inner ℝ (currentSubgradient (loss t) (iterate V η loss x₁ t))
        (iterate V η loss x₁ t - u) ∧
    η t * inner ℝ (currentSubgradient (loss t) (iterate V η loss x₁ t))
        (iterate V η loss x₁ t - u) ≤
      ‖iterate V η loss x₁ t - u‖ ^ 2 / 2 -
      ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2 / 2 +
      (η t) ^ 2 / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2

def P09 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hη : 0 < η t) (hloss : SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier),
    (loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal ≤
      (‖iterate V η loss x₁ t - u‖ ^ 2 -
        ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2

def P10 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    regret V (fun _ => η) loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2) -
      ‖iterate V (fun _ => η) loss x₁ T - u‖ ^ 2 / (2 * η)

def P11 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    regret V (fun _ => η) loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2)

def P12 : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier),
    regret V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))

def P13 : Prop :=
  ∀ (V : Domain (E := E)) (hV : Bornology.IsBounded V.carrier)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    regret V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))

def P14 : Prop :=
  ∀ (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T, ‖currentSubgradient (loss t)
      (iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G),
    regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T

def P15 : Prop :=
  ∀ (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t))
    (hgrad : ∀ t < T, ‖currentSubgradient (loss t)
      (iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G),
    ∀ u ∈ V.carrier,
      regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T
#print BanditRL.OnlineGradientDescent.Domain
#print BanditRL.OnlineConvex.SourceProper
#print BanditRL.OnlineConvex.SourceSubdifferential
#print BanditRL.OnlineConvex.effectiveDomain
#check @BanditRL.OnlineGradientDescent.project_spec
#check @BanditRL.OnlineGradientDescent.proposition_2_11
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
end NeutralUpdate

```
Actual standalone elaboration (each P is a proposition description only):
```text
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:26:43: warning: unused variable `hf`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:27:13: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:27:36: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:28:13: warning: unused variable `hg`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:37:5: warning: unused variable `hf`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:37:44: warning: unused variable `hx`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:42:5: warning: unused variable `hf`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:42:44: warning: unused variable `hx`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:47:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:53:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:53:32: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:58:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:59:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:65:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:66:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:66:54: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:72:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:73:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:73:20: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:74:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:86:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:87:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:87:20: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:88:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:95:35: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:96:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:97:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:97:63: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:104:35: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:105:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:106:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:106:63: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:113:37: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:113:68: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:114:5: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:114:29: warning: unused variable `hmono`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:115:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:116:5: warning: unused variable `hdiam`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:117:13: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:123:27: warning: unused variable `hV`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:124:49: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:125:13: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:125:26: warning: unused variable `hη`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:126:5: warning: unused variable `hmono`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:127:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:127:63: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:134:14: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:134:45: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:135:15: warning: unused variable `hD`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:135:28: warning: unused variable `hG`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:136:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:136:63: warning: unused variable `hu`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:137:5: warning: unused variable `hdist`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:138:5: warning: unused variable `hgrad`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:144:14: warning: unused variable `hx₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:144:45: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:145:15: warning: unused variable `hD`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:145:28: warning: unused variable `hG`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:146:5: warning: unused variable `hdiam`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:147:5: warning: unused variable `hloss`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
E:\ABRL\worktrees\research-online-book\runs\online-osd-public-20261007\leaves\neutral-propositions-v1.lean:148:5: warning: unused variable `hgrad`

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
def BanditRL.OnlineConvex.SourceProper.{u_1} : {E : Type u_1} → (E → EReal) → Prop :=
fun {E} f => (∀ (x : E), f x ≠ ⊥) ∧ ∃ x r, f x = ↑r
def BanditRL.OnlineConvex.SourceSubdifferential.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → (E → EReal) → E → Set E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] f x => {g | ∀ (y : E), f x + ↑⟪g, y - x⟫_ℝ ≤ f y}
def BanditRL.OnlineConvex.effectiveDomain.{u_1} : {E : Type u_1} → (E → EReal) → Set E :=
fun {E} f => {x | f x < ⊤}
@BanditRL.OnlineGradientDescent.project_spec : ∀ {E : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (V : BanditRL.OnlineGradientDescent.Domain E) (z : E),
  BanditRL.OnlineGradientDescent.project V z ∈ V.carrier ∧
    ‖z - BanditRL.OnlineGradientDescent.project V z‖ = ⨅ w, ‖z - ↑w‖
@BanditRL.OnlineGradientDescent.proposition_2_11 : ∀ {E : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (V : BanditRL.OnlineGradientDescent.Domain E) (z u : E),
  u ∈ V.carrier → ‖BanditRL.OnlineGradientDescent.project V z - u‖ ≤ ‖z - u‖
def NeutralUpdate.P01.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (f : E → EReal),
    SubdifferentiableOn V f →
      ∀ (η : ℝ),
        0 < η →
          ∀ (x u : E),
            u ∈ V.carrier →
              ∀ g ∈ SourceSubdifferential f x,
                η * ((f x).toReal - (f u).toReal) ≤ η * ⟪g, x - u⟫_ℝ ∧
                  η * ⟪g, x - u⟫_ℝ ≤
                    ‖x - u‖ ^ 2 / 2 - ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
                      η ^ 2 / 2 * ‖g‖ ^ 2
def NeutralUpdate.P02.{u_1} : {E : Type u_1} → [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] =>
  ∀ (V : Domain) (f : E → EReal),
    SubdifferentiableOn V f → ∀ x ∈ V.carrier, currentSubgradient f x ∈ SourceSubdifferential f x
def NeutralUpdate.P03.{u_1} : {E : Type u_1} → [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] =>
  ∀ (V : Domain) (f : E → EReal), SubdifferentiableOn V f → ∀ x ∈ V.carrier, f x = ↑(f x).toReal
def NeutralUpdate.P04.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal), ∀ x₁ ∈ V.carrier, ∀ (t : ℕ), iterate V η loss x₁ t ∈ V.carrier
def NeutralUpdate.P05.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η η' : ℕ → ℝ) (loss loss' : ℕ → E → EReal) (x₁ : E) (t : ℕ),
    (∀ s < t, η s = η' s) → (∀ s < t, loss s = loss' s) → iterate V η loss x₁ t = iterate V η' loss' x₁ t
def NeutralUpdate.P06.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (t : ℕ),
        SubdifferentiableOn V (loss t) →
          currentSubgradient (loss t) (iterate V η loss x₁ t) ∈ SourceSubdifferential (loss t) (iterate V η loss x₁ t)
def NeutralUpdate.P07.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (t : ℕ),
        SubdifferentiableOn V (loss t) →
          ∀ u ∈ V.carrier,
            loss t (iterate V η loss x₁ t) = ↑(loss t (iterate V η loss x₁ t)).toReal ∧ loss t u = ↑(loss t u).toReal
def NeutralUpdate.P08.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (t : ℕ),
        0 < η t →
          SubdifferentiableOn V (loss t) →
            ∀ u ∈ V.carrier,
              η t * ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal) ≤
                  η t * ⟪currentSubgradient (loss t) (iterate V η loss x₁ t), iterate V η loss x₁ t - u⟫_ℝ ∧
                η t * ⟪currentSubgradient (loss t) (iterate V η loss x₁ t), iterate V η loss x₁ t - u⟫_ℝ ≤
                  ‖iterate V η loss x₁ t - u‖ ^ 2 / 2 - ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2 / 2 +
                    η t ^ 2 / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2
def NeutralUpdate.P09.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (t : ℕ),
        0 < η t →
          SubdifferentiableOn V (loss t) →
            ∀ u ∈ V.carrier,
              (loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal ≤
                (‖iterate V η loss x₁ t - u‖ ^ 2 - ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
                  η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2
def NeutralUpdate.P10.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℝ),
    0 < η →
      ∀ (loss : ℕ → E → EReal),
        ∀ x₁ ∈ V.carrier,
          ∀ (T : ℕ),
            (∀ t < T, SubdifferentiableOn V (loss t)) →
              ∀ u ∈ V.carrier,
                regret V (fun x => η) loss x₁ u T ≤
                  ‖x₁ - u‖ ^ 2 / (2 * η) +
                      η / 2 *
                        ∑ t ∈ Finset.range T, ‖currentSubgradient (loss t) (iterate V (fun x => η) loss x₁ t)‖ ^ 2 -
                    ‖iterate V (fun x => η) loss x₁ T - u‖ ^ 2 / (2 * η)
def NeutralUpdate.P11.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℝ),
    0 < η →
      ∀ (loss : ℕ → E → EReal),
        ∀ x₁ ∈ V.carrier,
          ∀ (T : ℕ),
            (∀ t < T, SubdifferentiableOn V (loss t)) →
              ∀ u ∈ V.carrier,
                regret V (fun x => η) loss x₁ u T ≤
                  ‖x₁ - u‖ ^ 2 / (2 * η) +
                    η / 2 * ∑ t ∈ Finset.range T, ‖currentSubgradient (loss t) (iterate V (fun x => η) loss x₁ t)‖ ^ 2
def NeutralUpdate.P12.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (η : ℕ → ℝ) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (T : ℕ),
        0 < T →
          (∀ t < T, 0 < η t) →
            (∀ (t : ℕ), t + 1 < T → η (t + 1) ≤ η t) →
              (∀ t < T, SubdifferentiableOn V (loss t)) →
                ∀ (D : ℝ),
                  (∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) →
                    ∀ u ∈ V.carrier,
                      regret V η loss x₁ u T ≤
                        D ^ 2 / (2 * η (T - 1)) +
                            ∑ t ∈ Finset.range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2 -
                          ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))
def NeutralUpdate.P13.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain),
    Bornology.IsBounded V.carrier →
      ∀ (η : ℕ → ℝ) (loss : ℕ → E → EReal),
        ∀ x₁ ∈ V.carrier,
          ∀ (T : ℕ),
            0 < T →
              (∀ t < T, 0 < η t) →
                (∀ (t : ℕ), t + 1 < T → η (t + 1) ≤ η t) →
                  (∀ t < T, SubdifferentiableOn V (loss t)) →
                    ∀ u ∈ V.carrier,
                      regret V η loss x₁ u T ≤
                        Metric.diam V.carrier ^ 2 / (2 * η (T - 1)) +
                            ∑ t ∈ Finset.range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2 -
                          ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))
def NeutralUpdate.P14.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (T : ℕ),
        0 < T →
          ∀ (D G : ℝ),
            0 < D →
              0 < G →
                (∀ t < T, SubdifferentiableOn V (loss t)) →
                  ∀ u ∈ V.carrier,
                    ‖x₁ - u‖ ≤ D →
                      (∀ t < T, ‖currentSubgradient (loss t) (iterate V (fun x => D / (G * √↑T)) loss x₁ t)‖ ≤ G) →
                        regret V (fun x => D / (G * √↑T)) loss x₁ u T ≤ D * G * √↑T
def NeutralUpdate.P15.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → [FiniteDimensional ℝ E] → Prop :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] =>
  ∀ (V : Domain) (loss : ℕ → E → EReal),
    ∀ x₁ ∈ V.carrier,
      ∀ (T : ℕ),
        0 < T →
          ∀ (D G : ℝ),
            0 < D →
              0 < G →
                (∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) →
                  (∀ t < T, SubdifferentiableOn V (loss t)) →
                    (∀ t < T, ‖currentSubgradient (loss t) (iterate V (fun x => D / (G * √↑T)) loss x₁ t)‖ ≤ G) →
                      ∀ u ∈ V.carrier, regret V (fun x => D / (G * √↑T)) loss x₁ u T ≤ D * G * √↑T

```
