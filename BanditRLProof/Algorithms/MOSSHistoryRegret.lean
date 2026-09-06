import BanditRLProof.Algorithms.MOSSHistoryLaw
import BanditRLProof.LowerBounds.InstanceDependent

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BanditRLProof

/-- Inclusive finite-history counts agree with trace counts through t+1. -/
theorem finiteHistoryPullCountENNReal_trace {k : ℕ} {Reward : Type*}
    (action : ActionTrace (Fin k)) (reward : RewardTrace Reward) (t : ℕ) (a : Fin k) :
    LowerBounds.finiteHistoryPullCountENNReal t
      (History.finitePairHistoryOfTrace action reward t) a = (pullCount action a (t+1) : ℝ≥0∞) := by
  induction t with
  | zero =>
      simp [LowerBounds.finiteHistoryPullCountENNReal, History.finitePairHistoryOfTrace,
        pullCount_succ, pullCount_zero]
  | succ t ih =>
      change LowerBounds.finiteHistoryPullCountENNReal t
        (History.finitePairHistoryOfTrace action reward t) a +
        (if action (t+1) = a then 1 else 0) = _
      rw [ih, pullCount_succ, Nat.cast_add]
      split_ifs <;> simp_all

namespace MOSS

/-- The history gap functional is exactly the executed real pseudo-regret. -/
theorem canonicalHistory_gapRegret_toReal {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (mean : Fin k → ℝ) (best : Fin k) (hbest : ∀ a, mean a ≤ mean best)
    (table : UCB.ArmRewardStream k) :
    (LowerBounds.finiteHistoryGapPseudoRegret (fun a => mean best-mean a) t
      (canonicalHistory hk n mean table t)).toReal =
      realMeanRegret mean (canonicalAction hk n mean table) (t+1) := by
  letI : Nonempty (Fin k) := ⟨best⟩
  have hs : (⨆ a, mean a) = mean best :=
    le_antisymm (ciSup_le hbest) (le_ciSup (Finite.bddAbove_range mean) best)
  rw [LowerBounds.finiteHistoryGapPseudoRegret_toReal _ _ _ (fun a => sub_nonneg.mpr (hbest a)),
    realMeanRegret_eq_sum_gap_mul_pullCount]
  apply Finset.sum_congr rfl
  intro a _
  simp only [realMeanGap, hs, LowerBounds.finiteHistoryPullCountReal, canonicalHistory,
    finiteHistoryPullCountENNReal_trace, ENNReal.toReal_natCast]

/-- Exact transport of the common-history expected regret to the reward table. -/
theorem canonicalGapExpectedRegret_eq_integral {k : ℕ} [NeZero k] (hk : 0 < k)
    (n t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν]
    (mean : Fin k → ℝ) (best : Fin k) (hbest : ∀ a, mean a ≤ mean best) :
    LowerBounds.canonicalGapExpectedPseudoRegretReal (historyAlgorithm hk n) ν
      (fun a => mean best-mean a) t =
    ∫ table, realMeanRegret mean (canonicalAction hk n mean table) (t+1)
      ∂UCB.armStreamMeasure ν := by
  let f := LowerBounds.finiteHistoryGapPseudoRegret (Reward := ℝ) (fun a => mean best-mean a) t
  have hm : Measurable f := LowerBounds.measurable_finiteHistoryGapPseudoRegret _ _
  have hf : ∀ history, f history < ∞ := fun history =>
    lt_top_iff_ne_top.mpr (LowerBounds.finiteHistoryGapPseudoRegret_ne_top _ _ history)
  change (∫⁻ history, f history ∂LowerBounds.canonicalBanditHistoryMeasure (historyAlgorithm hk n) ν t).toReal = _
  rw [← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall hf),
    ← map_canonicalHistory_eq hk n mean ν t,
    integral_map (measurable_canonicalHistory hk n mean t).aemeasurable hm.ennreal_toReal.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (canonicalHistory_gapRegret_toReal hk n t mean best hbest)

/-- Source constant 39, now for the same history-law regret used by lower bounds. -/
theorem canonicalGapExpectedRegret_le {k : ℕ} [NeZero k] (hk : 0 < k)
    (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] (t : ℕ) (hkt : k ≤ t+1)
    (mean : Fin k → ℝ) (best : Fin k) (hbest : ∀ a, mean a ≤ mean best)
    (hmean : ∀ a, ∫ r, r ∂ν a = mean a)
    (hsubG : ∀ a, HasSubgaussianMGF (fun r => r-mean a) 1 (ν a)) :
    LowerBounds.canonicalGapExpectedPseudoRegretReal (historyAlgorithm hk (t+1)) ν
      (fun a => mean best-mean a) t ≤
      39*Real.sqrt (((t+1 : ℕ) : ℝ)*k) + ∑ a, (mean best-mean a) := by
  rw [canonicalGapExpectedRegret_eq_integral hk (t+1) t ν mean best hbest]
  exact integral_canonicalReward_regret_le hk ν (t+1) hkt mean best hbest hmean hsubG

end MOSS
end BanditRLProof
