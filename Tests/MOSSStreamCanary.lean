import BanditRLProof.Algorithms.MOSSStream
import BanditRLProof.Algorithms.MOSSRegret

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
