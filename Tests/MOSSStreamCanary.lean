import BanditRLProof.Algorithms.MOSSStream
import BanditRLProof.Algorithms.MOSSRegret
import BanditRLProof.Algorithms.MOSSExpectedRegret
import BanditRLProof.Algorithms.MOSSCanonicalReward
import BanditRLProof.Algorithms.MOSSCanonicalHistory
import BanditRLProof.Algorithms.MOSSUnusedCoordinate

open BanditRLProof

example {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (best chosen : Fin k)
    (hgap : 2 * MOSS.optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω < mean best - mean chosen) :
    (pullCount (MOSS.streamTrace hk n mean X ω) chosen n : ℝ) ≤ 1 +
      MOSS.indexExceedanceCount (MOSS.streamMean (X chosen) ω) ((k : ℝ)/(n : ℝ))
        (mean best - mean chosen) n :=
  MOSS.streamTrace_pullCount_le hk n hkn mean X ω best chosen hgap

#print axioms MOSS.neg_optimismDeficit_le_centeredIndex
#print axioms MOSS.radius_eq_streamRadius
#print axioms MOSS.pullCount_le_of_stream_policy
#print axioms MOSS.pullCount_streamTrace
#print axioms MOSS.streamTrace_policy
#print axioms MOSS.streamTrace_pullCount_le

example {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (best : Fin k)
    (hbest : ∀ a, mean a ≤ mean best) :
    realMeanRegret mean (MOSS.streamTrace hk n mean X ω) n ≤
      (8*Real.sqrt ((k : ℝ)/(n : ℝ)) + 2*MOSS.optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω)*(n : ℝ) +
      ∑ a, if 8*Real.sqrt ((k : ℝ)/(n : ℝ)) ≤ mean best - mean a then
        (mean best - mean a) * (1 + MOSS.indexExceedanceCount (MOSS.streamMean (X a) ω)
          ((k : ℝ)/(n : ℝ)) (mean best - mean a) n) else 0 :=
  MOSS.streamTrace_realMeanRegret_le hk n hkn mean X ω best hbest

#print axioms MOSS.integrable_indexExceedanceCount
#print axioms MOSS.streamTrace_gapSum_le
#print axioms MOSS.streamTrace_realMeanRegret_le
#print axioms MOSS.integral_largeGapCountSum_le

open MeasureTheory ProbabilityTheory
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (best : Fin k)
    (hbest : ∀ a, mean a ≤ mean best) (hXm : ∀ a i, StronglyMeasurable (X a i))
    (hind : ∀ a, iIndepFun (X a) μ) (hmean : ∀ a i, ∫ ω, X a i ω ∂μ = 0)
    (hsubG : ∀ a i, HasSubgaussianMGF (X a i) 1 μ) :
    (∫ ω, realMeanRegret mean (MOSS.streamTrace hk n mean X ω) n ∂μ) ≤
      39*Real.sqrt ((n : ℝ)*k) + ∑ a, (mean best-mean a) :=
  MOSS.integral_streamTrace_regret_le μ hk n hkn mean X best hbest hXm hind hmean hsubG

#print axioms MOSS.measurable_streamTrace
#print axioms MOSS.integrable_streamTrace_regret
#print axioms MOSS.integral_streamTrace_regret_le

example {k : ℕ} (hk : 0 < k) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν]
    (n : ℕ) (hkn : k ≤ n) (mean : Fin k → ℝ) (best : Fin k)
    (hbest : ∀ a, mean a ≤ mean best) (hmean : ∀ a, ∫ r, r ∂ν a = mean a)
    (hsubG : ∀ a, HasSubgaussianMGF (fun r => r-mean a) 1 (ν a)) :
    (∫ table, realMeanRegret mean (MOSS.streamTrace hk n mean (MOSS.centeredRewardTable mean) table) n
      ∂UCB.armStreamMeasure ν) ≤ 39*Real.sqrt ((n : ℝ)*k) + ∑ a, (mean best-mean a) :=
  MOSS.integral_canonicalReward_regret_le hk ν n hkn mean best hbest hmean hsubG

#print axioms MOSS.integral_canonicalReward_regret_le
#print axioms MOSS.mean_add_centeredRewardTable_average
#print axioms MOSS.canonicalReward_action_eq_raw

example {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ)
    (table table' : UCB.ArmRewardStream k) (t : ℕ)
    (h : ∀ a j, j < pullCount (MOSS.canonicalAction hk n mean table) a (t+1) →
      table (j+1) a = table' (j+1) a) :
    MOSS.canonicalHistory hk n mean table t = MOSS.canonicalHistory hk n mean table' t :=
  MOSS.canonicalHistory_eq_of_eq_consumed hk n mean table table' t h

#print axioms MOSS.canonicalHistory_empiricalMean
#print axioms MOSS.canonicalAction_succ_eq_historyAction
#print axioms MOSS.measurable_canonicalHistory
#print axioms MOSS.canonicalHistory_eq_of_eq_consumed

#print axioms MOSS.canonicalNextCoordinate_eq_iff_insert
#print axioms MOSS.canonicalCondition_eq_without
#print axioms MOSS.indepFun_coordinate_canonicalConditionWithout
#print axioms MOSS.map_canonicalConditionWithout_coordinate
