import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningStochastic

open MeasureTheory ProbabilityTheory

namespace BanditRL.OnlineLearning

/-- The source strategy's strict-past sufficient statistic is independent of the current target. -/
theorem meanPredict_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ) (t : ℕ) :
    IndepFun (fun ω => meanPredict (fun i => Y i ω) t) (Y t) μ := by
  by_cases ht : t = 0
  · subst t
    simpa [meanPredict] using indepFun_const_left (μ := μ) (1/2 : ℝ) (Y 0)
  · have hs := hind.indepFun_sum_range_succ hY t
    have hc := hs.comp (φ := fun z : ℝ => z / (t : ℝ))
      (ψ := id) (by fun_prop) measurable_id
    simpa [Function.comp_def, meanPredict, ht, empiricalMean, Finset.sum_apply] using hc

end BanditRL.OnlineLearning
