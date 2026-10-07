import BanditRLProof.OnlineSubgradientDescent
import Lean
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

def P01 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x),
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2

def P02 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal)
    (hf : SubdifferentiableOn V f) (x : E) (hx : x ∈ V.carrier),
    currentSubgradient f x ∈ SourceSubdifferential f x

def P03 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (f : E → EReal)
    (hf : SubdifferentiableOn V f) (x : E) (hx : x ∈ V.carrier),
    f x = ((f x).toReal : EReal)

def P04 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ),
    iterate V η loss x₁ t ∈ V.carrier

def P05 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s),
    iterate V η loss x₁ t = iterate V η' loss' x₁ t

def P06 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : SubdifferentiableOn V (loss t)),
    currentSubgradient (loss t) (iterate V η loss x₁ t) ∈
      SourceSubdifferential (loss t) (iterate V η loss x₁ t)

def P07 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    loss t (iterate V η loss x₁ t) = ((loss t (iterate V η loss x₁ t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal)

def P08 [instFD : FiniteDimensional ℝ E] : Prop :=
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

def P09 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hη : 0 < η t) (hloss : SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier),
    (loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal ≤
      (‖iterate V η loss x₁ t - u‖ ^ 2 -
        ‖iterate V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2

def P10 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    regret V (fun _ => η) loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2) -
      ‖iterate V (fun _ => η) loss x₁ T - u‖ ^ 2 / (2 * η)

def P11 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    regret V (fun _ => η) loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T,
        ‖currentSubgradient (loss t) (iterate V (fun _ => η) loss x₁ t)‖ ^ 2)

def P12 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier),
    regret V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))

def P13 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (hV : Bornology.IsBounded V.carrier)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier),
    regret V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖currentSubgradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))

def P14 [instFD : FiniteDimensional ℝ E] : Prop :=
  ∀ (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T, ‖currentSubgradient (loss t)
      (iterate V (fun _ => D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G),
    regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T

def P15 [instFD : FiniteDimensional ℝ E] : Prop :=
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


open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let deps : Array (Name × Name) := #[
    (`NeutralUpdate.Domain, `BanditRL.OnlineSubgradientDescent.Domain),
    (`NeutralUpdate.SubdifferentiableOn, `BanditRL.OnlineSubgradientDescent.SubdifferentiableOn),
    (`NeutralUpdate.currentSubgradient, `BanditRL.OnlineSubgradientDescent.currentSubgradient),
    (`NeutralUpdate.step, `BanditRL.OnlineSubgradientDescent.step),
    (`NeutralUpdate.iterate, `BanditRL.OnlineSubgradientDescent.iterate),
    (`NeutralUpdate.regret, `BanditRL.OnlineSubgradientDescent.regret)]
  let renameDeps (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => match deps.find? (fun p => p.1 == n) with
      | some p => some (.const p.2 ls)
      | none => none
    | _ => none
  for (neutral, actual) in deps do
    let some ai := env.find? actual | throwError "missing actual dependency {actual}"
    let some ni := env.find? neutral | throwError "missing neutral dependency {neutral}"
    unless ← isDefEq ai.type (renameDeps ni.type) do
      throwError "DEPENDENCY TYPE MISMATCH {actual}: {ai.type}; {renameDeps ni.type}"
    let some av := ai.value? | throwError "missing actual definition value {actual}"
    let some nv := ni.value? | throwError "missing neutral definition value {neutral}"
    unless ← isDefEq av (renameDeps nv) do
      throwError "DEPENDENCY VALUE MISMATCH {actual}: {av}; {renameDeps nv}"
    logInfo m!"DEPENDENCY_TYPE_VALUE_MATCH {actual} = {neutral}"
  let rec closeLambdas : Expr → Expr
    | .lam n t b bi => .forallE n t (closeLambdas b) bi
    | e => e
  let pairs : Array (Name × Name) := #[
    (`BanditRL.OnlineSubgradientDescent.lemma_2_31, `NeutralUpdate.P01),
    (`BanditRL.OnlineSubgradientDescent.currentSubgradient_mem, `NeutralUpdate.P02),
    (`BanditRL.OnlineSubgradientDescent.finite_loss, `NeutralUpdate.P03),
    (`BanditRL.OnlineSubgradientDescent.iterate_mem, `NeutralUpdate.P04),
    (`BanditRL.OnlineSubgradientDescent.iterate_prefix, `NeutralUpdate.P05),
    (`BanditRL.OnlineSubgradientDescent.iterate_support, `NeutralUpdate.P06),
    (`BanditRL.OnlineSubgradientDescent.iterate_finite_loss, `NeutralUpdate.P07),
    (`BanditRL.OnlineSubgradientDescent.one_step_chain, `NeutralUpdate.P08),
    (`BanditRL.OnlineSubgradientDescent.one_step, `NeutralUpdate.P09),
    (`BanditRL.OnlineSubgradientDescent.regret_fixed, `NeutralUpdate.P10),
    (`BanditRL.OnlineSubgradientDescent.regret_fixed_coarse, `NeutralUpdate.P11),
    (`BanditRL.OnlineSubgradientDescent.regret_variable_bound, `NeutralUpdate.P12),
    (`BanditRL.OnlineSubgradientDescent.regret_variable, `NeutralUpdate.P13),
    (`BanditRL.OnlineSubgradientDescent.regret_tuned_distance, `NeutralUpdate.P14),
    (`BanditRL.OnlineSubgradientDescent.regret_tuned, `NeutralUpdate.P15)]
  for (actual, neutral) in pairs do
    let some ai := env.find? actual | throwError "missing actual {actual}"
    let some ni := env.find? neutral | throwError "missing neutral {neutral}"
    let some nv := ni.value? | throwError "missing proposition description {neutral}"
    unless ← isDefEq ai.type (renameDeps (closeLambdas nv)) do
      throwError "FULL CONTEXT MISMATCH {actual}: {ai.type}; {renameDeps (closeLambdas nv)}"
    logInfo m!"FULL_CONTEXT_MATCH {actual} = {neutral}"
