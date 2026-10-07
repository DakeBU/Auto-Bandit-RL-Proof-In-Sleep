import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
open Filter
namespace Neutral
noncomputable def a {X : Type*} (loss : ℕ → X → ℝ) (prediction : ℕ → X) (u : X) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, loss t (prediction t)) - ∑ t ∈ Finset.range T, loss t u
def b {X : Type*} (V : Set X) (loss : ℕ → X → ℝ) (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, a loss prediction u T / T ≤ ε
def c {X : Type*} (V W : Set X) (hVW : V ⊆ W) : ↥V → ↥W :=
  fun u => ⟨u.val, hVW u.property⟩

def d : Set ℝ := Set.Icc 0 1

def e : Set ℝ := Set.Icc 0 2

def f : ℕ → ↥e → ℝ := fun _ x => -x.val

def g : ℕ → ↥e := fun _ => ⟨2, by norm_num [e]⟩

def h : ↥e := ⟨1, by norm_num [e]⟩

def i : ↥e := ⟨0, by norm_num [e]⟩

def j : Set ↥e := {x | x.val ∈ d}
def N01 : Prop :=
    ∀ {X : Type*} (loss : ℕ → X → ℝ) (prediction : ℕ → X) (u : X) (T : ℕ),
    a loss prediction u T = ∑ t ∈ Finset.range T, (loss t (prediction t) - loss t u)

def N02 : Prop :=
    ∀ {X : Type*} (V : Set X) (loss : ℕ → X → ℝ) (prediction : ℕ → X) (bound : X → ℕ → ℝ) (hb : ∀ u ∈ V, ∀ᶠ T in atTop, a loss prediction u T / T ≤ bound u T) (hl : ∀ u ∈ V, Tendsto (bound u) atTop (nhds 0)),
    b V loss prediction

def N03 : Prop :=
    ∀ {X : Type*} (V W : Set X) (hVW : V ⊆ W)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥V) (T : ℕ),
    a loss prediction (c V W hVW u) T =
      ∑ t ∈ Finset.range T, (loss t (prediction t) - loss t (c V W hVW u))

def N04 : Prop :=
    ∀ {X : Type*} (V W : Set X) (hVW : V ⊆ W)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥V) (u : ↥V) (T : ℕ),
    a (fun t v => loss t (c V W hVW v)) prediction u T =
      a loss (fun t => c V W hVW (prediction t)) (c V W hVW u) T

def N05 : Prop :=
    d ⊆ e ∧ (2 : ℝ) ∈ e ∧ (2 : ℝ) ∉ d

def N06 : Prop :=
    ∀ {X : Type*} (W : Set X)
    (loss other : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥W) (T : ℕ)
    (h : ∀ t < T, ∀ x : ↥W, loss t x = other t x),
    a loss prediction u T = a other prediction u T

def N07 : Prop :=
    ∀ {X : Type*} (W : Set X)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥W),
    a loss prediction u 0 = 0

def N08 : Prop :=
    (g 0).val ∈ e ∧ (g 0).val ∉ d ∧
      a f g h 2 = -2

def N09 : Prop :=
    i.val ∈ d ∧ h.val ∈ d ∧
      a f g i 2 = -4 ∧
      a f g h 2 = -2

def N10 : Prop :=
    b j f g
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
end Neutral
