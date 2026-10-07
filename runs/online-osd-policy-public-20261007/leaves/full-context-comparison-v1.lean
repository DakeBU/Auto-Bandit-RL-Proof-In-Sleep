import Lean
import BanditRLProof.OnlineSubgradientPolicy
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


open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let deps : Array (Name × Name) := #[
    (`NeutralHistory.Domain, `BanditRL.OnlineSubgradientPolicy.Domain),
    (`NeutralHistory.SupportPolicy, `BanditRL.OnlineSubgradientPolicy.SupportPolicy),
    (`NeutralHistory.history, `BanditRL.OnlineSubgradientPolicy.history),
    (`NeutralHistory.output, `BanditRL.OnlineSubgradientPolicy.output),
    (`NeutralHistory.selected, `BanditRL.OnlineSubgradientPolicy.selected),
    (`NeutralHistory.OracleLaw, `BanditRL.OnlineSubgradientPolicy.OracleLaw),
    (`NeutralHistory.canonicalPolicy, `BanditRL.OnlineSubgradientPolicy.canonicalPolicy),
    (`NeutralHistory.LegalFeedback, `BanditRL.OnlineSubgradientPolicy.LegalFeedback),
    (`NeutralHistory.regret, `BanditRL.OnlineSubgradientPolicy.regret)]
  let renameDeps (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => match deps.find? (fun p => p.1 == n) with
      | some p => some (.const p.2 ls)
      | none => none
    | _ => none
  for (neutral, actual) in deps do
    let some ai := env.find? actual | throwError "missing actual {actual}"
    let some ni := env.find? neutral | throwError "missing neutral {neutral}"
    unless ← isDefEq ai.type (renameDeps ni.type) do
      throwError "DEPENDENCY TYPE MISMATCH {actual}: {ai.type}; {renameDeps ni.type}"
    let some av := ai.value? | throwError "missing actual value {actual}"
    let some nv := ni.value? | throwError "missing neutral value {neutral}"
    unless ← isDefEq av (renameDeps nv) do
      throwError "DEPENDENCY VALUE MISMATCH {actual}: {av}; {renameDeps nv}"
    logInfo m!"DEPENDENCY_TYPE_VALUE_MATCH {actual} = {neutral}"
  let rec closeLambdas : Expr → Expr
    | .lam n t b bi => .forallE n t (closeLambdas b) bi
    | e => e
  let pairs : Array (Name × Name) := #[
    (`BanditRL.OnlineSubgradientPolicy.history_zero, `NeutralHistory.P01),
    (`BanditRL.OnlineSubgradientPolicy.history_succ, `NeutralHistory.P02),
    (`BanditRL.OnlineSubgradientPolicy.output_zero, `NeutralHistory.P03),
    (`BanditRL.OnlineSubgradientPolicy.output_succ, `NeutralHistory.P04),
    (`BanditRL.OnlineSubgradientPolicy.history_mem, `NeutralHistory.P05),
    (`BanditRL.OnlineSubgradientPolicy.output_mem, `NeutralHistory.P06),
    (`BanditRL.OnlineSubgradientPolicy.history_prefix, `NeutralHistory.P07),
    (`BanditRL.OnlineSubgradientPolicy.output_prefix, `NeutralHistory.P08),
    (`BanditRL.OnlineSubgradientPolicy.oracle_feedback, `NeutralHistory.P09),
    (`BanditRL.OnlineSubgradientPolicy.trajectory_finite_loss, `NeutralHistory.P10),
    (`BanditRL.OnlineSubgradientPolicy.one_step_chain, `NeutralHistory.P11),
    (`BanditRL.OnlineSubgradientPolicy.one_step, `NeutralHistory.P12),
    (`BanditRL.OnlineSubgradientPolicy.regret_fixed, `NeutralHistory.P13),
    (`BanditRL.OnlineSubgradientPolicy.regret_fixed_coarse, `NeutralHistory.P14),
    (`BanditRL.OnlineSubgradientPolicy.regret_variable_bound, `NeutralHistory.P15),
    (`BanditRL.OnlineSubgradientPolicy.regret_variable, `NeutralHistory.P16),
    (`BanditRL.OnlineSubgradientPolicy.regret_tuned_distance, `NeutralHistory.P17),
    (`BanditRL.OnlineSubgradientPolicy.regret_tuned, `NeutralHistory.P18),
    (`BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal, `NeutralHistory.P19),
    (`BanditRL.OnlineSubgradientPolicy.canonical_output, `NeutralHistory.P20),
    (`BanditRL.OnlineSubgradientPolicy.canonical_selected, `NeutralHistory.P21)]
  for (actual, neutral) in pairs do
    let some ai := env.find? actual | throwError "missing actual {actual}"
    let some ni := env.find? neutral | throwError "missing neutral {neutral}"
    let some nv := ni.value? | throwError "missing proposition description {neutral}"
    unless ← isDefEq ai.type (renameDeps (closeLambdas nv)) do
      throwError "FULL CONTEXT MISMATCH {actual}: {ai.type}; {renameDeps (closeLambdas nv)}"
    logInfo m!"FULL_CONTEXT_MATCH {actual} = {neutral}"
