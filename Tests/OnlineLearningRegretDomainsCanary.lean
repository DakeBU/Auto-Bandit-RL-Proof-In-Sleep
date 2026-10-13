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

theorem restriction_commutes {X : Type*} (V W : Set X) (hVW : V ⊆ W)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥V) (u : ↥V) (T : ℕ) :
    comparatorRegret (fun t v => loss t (embed V W hVW v)) prediction u T =
      comparatorRegret loss (fun t => embed V W hVW (prediction t)) (embed V W hVW u) T := by
  rfl

theorem proper_inclusion :
    sourceV ⊆ outputW ∧ (2 : ℝ) ∈ outputW ∧ (2 : ℝ) ∉ sourceV := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change 0 ≤ x ∧ x ≤ 2
    change 0 ≤ x ∧ x ≤ 1 at hx
    exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩
  · norm_num [outputW]
  · norm_num [sourceV]

theorem loss_prefix {X : Type*} (W : Set X)
    (loss other : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥W) (T : ℕ)
    (h : ∀ t < T, ∀ x : ↥W, loss t x = other t x) :
    comparatorRegret loss prediction u T = comparatorRegret other prediction u T := by
  unfold comparatorRegret
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    exact h t (Finset.mem_range.mp ht) (prediction t)
  · apply Finset.sum_congr rfl
    intro t ht
    exact h t (Finset.mem_range.mp ht) u

theorem zero_horizon {X : Type*} (W : Set X)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥W) :
    comparatorRegret loss prediction u 0 = 0 := by
  simp [comparatorRegret]

theorem outside_prediction_and_negative_regret :
    (output 0).val ∈ outputW ∧ (output 0).val ∉ sourceV ∧
      comparatorRegret domainLoss output referenceOne 2 = -2 := by
  norm_num [output, outputW, sourceV, comparatorRegret, domainLoss,
    referenceOne, Finset.sum_range_succ]

theorem same_prediction_two_comparators :
    referenceZero.val ∈ sourceV ∧ referenceOne.val ∈ sourceV ∧
      comparatorRegret domainLoss output referenceZero 2 = -4 ∧
      comparatorRegret domainLoss output referenceOne 2 = -2 := by
  norm_num [referenceZero, referenceOne, sourceV, comparatorRegret, domainLoss,
    output, Finset.sum_range_succ]

theorem negative_game_noRegret :
    NoRegret liftedComparators domainLoss output := by
  apply noRegret_of_vanishing_bound liftedComparators domainLoss output (fun _ _ => 0)
  · intro u hu
    exact Filter.Eventually.of_forall (fun T => by
      change comparatorRegret domainLoss output u T / (T : ℝ) ≤ 0
      apply div_nonpos_of_nonpos_of_nonneg ?_ (Nat.cast_nonneg T)
      rw [comparatorRegret_eq_sum]
      apply Finset.sum_nonpos
      intro t ht
      change 0 ≤ u.val ∧ u.val ≤ 1 at hu
      change -(2 : ℝ) - (-u.val) ≤ 0
      linarith [hu.2])
  · intro u hu
    exact tendsto_const_nhds

end RegretDomainsProbe
