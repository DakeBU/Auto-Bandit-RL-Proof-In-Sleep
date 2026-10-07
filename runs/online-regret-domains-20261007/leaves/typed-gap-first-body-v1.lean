import BanditRLProof.OnlineLearningRegret
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Filter BanditRL.OnlineLearning
namespace RegretDomainsProbe

def embed {X : Type*} (V W : Set X) (hVW : V ⊆ W) : ↥V → ↥W :=
  fun u => ⟨u.val, hVW u.property⟩

def sourceV : Set ℝ := Set.Icc 0 1

def outputW : Set ℝ := Set.Icc 0 2

def domainLoss : ℕ → ↥outputW → ℝ := fun _ x => -x.val

def output : ℕ → ↥outputW := fun _ => ⟨2, by norm_num [outputW]⟩

def referenceOne : ↥outputW := ⟨1, by norm_num [outputW]⟩

def referenceZero : ↥outputW := ⟨0, by norm_num [outputW]⟩

def liftedComparators : Set ↥outputW := {x | x.val ∈ sourceV}

theorem domain_gap_sum {X : Type*} (V W : Set X) (hVW : V ⊆ W)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥V) (T : ℕ) :
    comparatorRegret loss prediction (embed V W hVW u) T =
      ∑ t ∈ Finset.range T, (loss t (prediction t) - loss t (embed V W hVW u)) := by
  exact comparatorRegret_eq_sum loss prediction (embed V W hVW u) T

end RegretDomainsProbe
