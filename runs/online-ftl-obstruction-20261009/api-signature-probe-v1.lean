import BanditRLProof.OnlineFTLLimitSemantics
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
namespace BanditRL.OnlineLearning

/-- Explicit binary dyadic-block observations, independent of the learner and horizon. -/
noncomputable def dyadicObservation : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 - dyadicObservation (n / 2)
termination_by n => n
decreasing_by omega


def draft_meanPredict_limitNoRegret_iff_mean_converges (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) : Prop :=
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y) ↔
      ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean y) atTop (nhds m)

def draft_dyadicObservation_unit : Prop :=
    ∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1

def draft_dyadic_empiricalMean_subsequences : Prop :=
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ) / 3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ) / 3))

def draft_dyadic_meanPredict_obstruction : Prop :=
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation)

#check meanPredict_fixedRegret_limit_iff
#check meanPredict_limitNoRegret_of_mean_converges
#check empiricalMean_mem
#check tendsto_pow_atTop_atTop_of_one_lt
#check Finset.sum_range_succ
#check le_of_tendsto
#check ge_of_tendsto
#check Nat.one_le_pow
#check Filter.tendsto_add_atTop_nat
end BanditRL.OnlineLearning
