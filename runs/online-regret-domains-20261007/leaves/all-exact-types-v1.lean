import Tests.OnlineLearningRegretDomainsCanary
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

universe u
def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.N01.{u} = propositionOf (@BanditRL.OnlineLearning.comparatorRegret_eq_sum.{u}) := by rfl
example : Neutral.N02.{u} = propositionOf (@BanditRL.OnlineLearning.noRegret_of_vanishing_bound.{u}) := by rfl
example : Neutral.N03.{u} = propositionOf (@RegretDomainsProbe.domain_gap_sum.{u}) := by rfl
example : Neutral.N04.{u} = propositionOf (@RegretDomainsProbe.restriction_commutes.{u}) := by rfl
example : Neutral.N05 = propositionOf (@RegretDomainsProbe.proper_inclusion) := by rfl
example : Neutral.N06.{u} = propositionOf (@RegretDomainsProbe.loss_prefix.{u}) := by rfl
example : Neutral.N07.{u} = propositionOf (@RegretDomainsProbe.zero_horizon.{u}) := by rfl
example : Neutral.N08 = propositionOf (@RegretDomainsProbe.outside_prediction_and_negative_regret) := by rfl
example : Neutral.N09 = propositionOf (@RegretDomainsProbe.same_prediction_two_comparators) := by rfl
example : Neutral.N10 = propositionOf (@RegretDomainsProbe.negative_game_noRegret) := by rfl
example : @Neutral.a.{u} = @BanditRL.OnlineLearning.comparatorRegret.{u} := by rfl
example : @Neutral.b.{u} = @BanditRL.OnlineLearning.NoRegret.{u} := by rfl
example : @Neutral.c.{u} = @RegretDomainsProbe.embed.{u} := by rfl
example : @Neutral.d = @RegretDomainsProbe.sourceV := by rfl
example : @Neutral.e = @RegretDomainsProbe.outputW := by rfl
example : @Neutral.f = @RegretDomainsProbe.domainLoss := by rfl
example : @Neutral.g = @RegretDomainsProbe.output := by rfl
example : @Neutral.h = @RegretDomainsProbe.referenceOne := by rfl
example : @Neutral.i = @RegretDomainsProbe.referenceZero := by rfl
example : @Neutral.j = @RegretDomainsProbe.liftedComparators := by rfl
