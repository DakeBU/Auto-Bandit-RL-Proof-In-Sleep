import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Filter Asymptotics
universe u v
namespace BanditRL.OnlineLearning

end BanditRL.OnlineLearning
#check Asymptotics.isLittleO_iff_tendsto'
#check Asymptotics.IsLittleO.tendsto_div_nhds_zero
#check Filter.tendsto_congr'
#check Filter.Tendsto.congr'
#check squeeze_zero'
#check MeasureTheory.integrable_finset_sum
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_sub
#check BanditRL.OnlineLearning.normalized_excess
#check BanditRL.OnlineLearning.expected_fixed_prefix_decomposition
#check BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#check BanditRL.OnlineLearning.meanPredict_expectedFixed_excess
#check BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
#check BanditRL.OnlineLearning.theorem_1_3
#check BanditRL.OnlineLearning.empiricalMean_minimizes
#check BanditRL.OnlineLearning.meanPredict_measurable
#check BanditRL.OnlineLearning.meanPredict_mem
#check Real.tendsto_pow_log_div_mul_add_atTop
#check tendsto_natCast_atTop_atTop
#print axioms Asymptotics.isLittleO_iff_tendsto'
#print axioms Asymptotics.IsLittleO.tendsto_div_nhds_zero
#print axioms Filter.tendsto_congr'
#print axioms Filter.Tendsto.congr'
#print axioms MeasureTheory.integrable_finset_sum
#print axioms MeasureTheory.integral_mono_ae
#print axioms MeasureTheory.integral_sub
#print axioms BanditRL.OnlineLearning.normalized_excess
#print axioms BanditRL.OnlineLearning.expected_fixed_prefix_decomposition
#print axioms BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#print axioms BanditRL.OnlineLearning.meanPredict_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
#print axioms BanditRL.OnlineLearning.theorem_1_3
#print axioms BanditRL.OnlineLearning.empiricalMean_minimizes
#print axioms BanditRL.OnlineLearning.meanPredict_measurable
#print axioms BanditRL.OnlineLearning.meanPredict_mem
#print axioms Real.tendsto_pow_log_div_mul_add_atTop
#print axioms tendsto_natCast_atTop_atTop
