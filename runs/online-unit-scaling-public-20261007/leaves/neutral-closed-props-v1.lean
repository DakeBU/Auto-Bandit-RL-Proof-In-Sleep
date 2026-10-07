import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace NeutralUnits
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
structure C (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier
def K : C E := ⟨univ, univ_nonempty, isClosed_univ, convex_univ⟩
def J (z : E) : E := Classical.choose
  (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex z)
def Q (f : E → EReal) : Prop := (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
def B (f : E → EReal) : Prop := Q f ∧ ∀ x ∈ K.carrier, (S f x).Nonempty
abbrev P := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E
def H (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) :
    (t : ℕ) → Fin (t + 1) → E :=
  Nat.rec (motive := fun t => Fin (t + 1) → E) (fun _ => x₁)
    (fun t h => Fin.snoc h (J (h (Fin.last t) - η t • p t (fun i => loss i.val) h (loss t))))
def Z (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ) : E :=
  H k η loss x₁ p t (Fin.last t)
def G (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (H k η loss x₁ p t) (loss t)
def L (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, G k η loss x₁ p t ∈ S (loss t) (Z k η loss x₁ p t)
def R (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (Z k η loss x₁ p t)).toReal - (loss t u).toReal)
def F (c : ℝ) (f : E → EReal) : E → EReal := fun y => f (c • y)
def e (c : ℝ) (η : ℕ → ℝ) : ℕ → ℝ := fun t => η t / c ^ 2
def a (c : ℝ) (p : P (E := E)) : P (E := E) :=
  fun t past h f => c • p t (fun i => F c⁻¹ (past i)) (fun i => c • h i) (F c⁻¹ f)
def U (A B η : ℝ) : ℝ := A / (2 * η) + η * B / 2

def N01 : Prop := ∀ {D : Type*} [AddCommGroup D] (X L H : D) (h : H + (L - X) = X),
  H = X + X - L

def N02 : Prop := ∀ {D : Type*} [AddCommGroup D] (X L : D),
  (X + X - (X + X - L) = L) ∧ ((X + X - L) + (L - X) + (L - X) = L)

def N03 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (f : E → EReal),
  F c⁻¹ (F c f) = f

def N04 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : Q f),
  Q (F c f)

def N05 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : Q f) (y g : E) (hg : g ∈ S f (c • y)),
  c • g ∈ S (F c f) y

def N06 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : B f),
  B (F c f)

def N07 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (f : E → ℝ) (y g : E) (hf : HasGradientAt f g (c • y)),
  HasGradientAt (fun z => f (c • z)) (c • g) y

def N08 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (f : E → ℝ) (y : E) (hf : DifferentiableAt ℝ f (c • y)),
  gradient (fun z => f (c • z)) y = c • gradient f (c • y)

def N09 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℝ) (x g : E),
  c⁻¹ • (x - η • g) = c⁻¹ • x - (η / c ^ 2) • (c • g)

def N10 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℝ) (x g : E),
  c • (c⁻¹ • x - η • (c • g)) = x - (c ^ 2 * η) • g

def N11 : Prop := ∀ (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (t : ℕ) (hη : 0 < η t),
  0 < e c η t

def N12 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ),
  H K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) t = fun i => c⁻¹ • H K η loss x₁ p t i

def N13 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ),
  Z K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) t = c⁻¹ • Z K η loss x₁ p t

def N14 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ),
  G K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) t = c • G K η loss x₁ p t

def N15 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (T : ℕ) (hproper : ∀ t < T, Q (loss t)) (hlegal : L K η loss x₁ p T),
  L K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) T

def N16 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ),
  F c (loss t) (Z K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) t) = loss t (Z K η loss x₁ p t)

def N17 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (u : E) (T : ℕ),
  R K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) (c⁻¹ • u) T = R K η loss x₁ p u T

def N18 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ),
  c • Z K η (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) t = Z K (fun s => c ^ 2 * η s) loss x₁ p t

def N19 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (x u : E),
  ‖c⁻¹ • x - c⁻¹ • u‖ ^ 2 = ‖x - u‖ ^ 2 / c ^ 2

def N20 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (T : ℕ),
  (∑ t ∈ range T, ‖G K (e c η) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) t‖ ^ 2) = c ^ 2 * (∑ t ∈ range T, ‖G K η loss x₁ p t‖ ^ 2)

def N21 : Prop := ∀ (c : ℝ) (hc : 0 < c) (A B η : ℝ) (hη : 0 < η),
  U (A / c ^ 2) (c ^ 2 * B) (η / c ^ 2) = U A B η

def N22 : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (T : ℕ) (hloss : ∀ t < T, B (loss t)) (hlegal : L K (fun _ => η) loss x₁ p T) (u : E),
  R K (e c (fun _ => η)) (fun s => F c (loss s)) (c⁻¹ • x₁) (a c p) (c⁻¹ • u) T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * (∑ t ∈ range T, ‖G K (fun _ => η) loss x₁ p t‖ ^ 2) - ‖Z K (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η)
#check N01
#check N02
#check N03
#check N04
#check N05
#check N06
#check N07
#check N08
#check N09
#check N10
#check N11
#check N12
#check N13
#check N14
#check N15
#check N16
#check N17
#check N18
#check N19
#check N20
#check N21
#check N22
end NeutralUnits
