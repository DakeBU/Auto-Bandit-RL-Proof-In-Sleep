import BanditRLProof.Algorithms.MOSSExpectedRegret
import BanditRLProof.Algorithms.UCBArmStreamTail

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

/-- One-based centered reward table; sample zero is unused by MOSS. -/
def centeredRewardTable {k : ℕ} (mean : Fin k → ℝ) :
    Fin k → ℕ → UCB.ArmRewardStream k → ℝ :=
  fun a i table => table i a - mean a

/-- Exact MOSS bound on the canonical product space of arbitrary arm laws. -/
theorem integral_canonicalReward_regret_le {k : ℕ} (hk : 0 < k)
    (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (best : Fin k) (hbest : ∀ a, mean a ≤ mean best)
    (hmean : ∀ a, ∫ r, r ∂ν a = mean a)
    (hsubG : ∀ a, HasSubgaussianMGF (fun r => r-mean a) 1 (ν a)) :
    (∫ table, realMeanRegret mean (streamTrace hk n mean (centeredRewardTable mean) table) n
      ∂UCB.armStreamMeasure ν) ≤ 39*Real.sqrt ((n : ℝ)*k) + ∑ a, (mean best-mean a) := by
  have hm (a : Fin k) (i : ℕ) : Measurable (fun table : UCB.ArmRewardStream k => table i a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply i)
  apply integral_streamTrace_regret_le _ hk n hkn mean _ best hbest
  · intro a i
    exact ((hm a i).sub measurable_const).stronglyMeasurable
  · intro a
    exact UCB.iIndepFun_armStreamMeasure_coord_sub ν a (mean a)
  · intro a i
    have hr : Integrable (fun r : ℝ => r) (ν a) := by
      have h := (hsubG a).integrable.add (integrable_const (mean a))
      change Integrable (fun r : ℝ => (r-mean a)+mean a) (ν a) at h
      simpa only [Pi.add_apply, sub_add_cancel] using h
    have he := integral_map (μ := UCB.armStreamMeasure ν) (f := fun r : ℝ => r-mean a) (hm a i).aemeasurable
      (measurable_id.sub measurable_const).aestronglyMeasurable
    rw [UCB.armStreamMeasure_map_coord ν i a] at he
    change (∫ table : UCB.ArmRewardStream k, table i a - mean a ∂UCB.armStreamMeasure ν) = 0
    rw [← he, integral_sub hr (integrable_const _)]
    simp [hmean a]
  · intro a i
    exact UCB.hasSubgaussianMGF_armStreamMeasure_coord_sub ν a (mean a) 1 (hsubG a) i

/-- Centering is analytical only: positive-count empirical means use raw rewards. -/
theorem mean_add_centeredRewardTable_average {k : ℕ} (mean : Fin k → ℝ)
    (table : UCB.ArmRewardStream k) (a : Fin k) (s : ℕ) (hs : 0 < s) :
    mean a + streamMean (centeredRewardTable mean a) table s =
      (∑ j ∈ Finset.range s, table (j+1) a)/(s : ℝ) := by
  have hsR : (s : ℝ) ≠ 0 := by positivity
  simp only [streamMean, peelingSum, centeredRewardTable, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- After initialization each arm has a positive realized count. -/
theorem streamTrace_pullCount_pos {Ω : Type*} {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (a : Fin k) (ht : k ≤ t) :
    0 < pullCount (streamTrace hk n mean X ω) a t := by
  apply pullCount_pos_of_eq_before _ _ (lt_of_lt_of_le a.isLt ht)
  exact action_initial_arm hk n _ _ a

/-- The centered execution selects solely from raw empirical rewards and counts.
The unknown means cancel; zero-count states are handled by initialization. -/
theorem canonicalReward_action_eq_raw {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (mean : Fin k → ℝ) (table : UCB.ArmRewardStream k) :
    streamTrace hk n mean (centeredRewardTable mean) table t =
      action hk n t
        (fun a => (∑ j ∈ Finset.range (pullCount (streamTrace hk n mean (centeredRewardTable mean) table) a t),
          table (j+1) a)/(pullCount (streamTrace hk n mean (centeredRewardTable mean) table) a t : ℝ))
        (fun a => pullCount (streamTrace hk n mean (centeredRewardTable mean) table) a t) := by
  rw [streamTrace_policy]
  by_cases ht : t < k
  · rw [action_of_lt hk n t _ _ ht, action_of_lt hk n t _ _ ht]
  · congr 1
    funext a
    apply mean_add_centeredRewardTable_average
    exact streamTrace_pullCount_pos hk n t mean _ table a (Nat.le_of_not_gt ht)

end BanditRLProof.MOSS
