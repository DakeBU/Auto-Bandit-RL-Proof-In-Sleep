import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningStochastic

open MeasureTheory ProbabilityTheory

/-!
Derived information proof for the actual initial-half, strict-past sample-mean learner in Orabona v10, printed pp.3-4 / PDF pp.15-16, applied to the IID motivation on p.1 / PDF p.13. Joint independence and target measurability derive current-target independence. No same-law, boundedness or supplied current-independence premise is required. The population mean and horizon are not learner inputs.
-/

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
