import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Topology.UnitInterval

open MeasureTheory ProbabilityTheory

#check Measurable.exists_eq_measurable_comp
#check AEStronglyMeasurable.measurable_mk
#check AEStronglyMeasurable.ae_eq_mk
#check AEStronglyMeasurable.mono
#check IndepFun.congr
#check continuous_projIcc
#check Set.projIcc_of_mem
#check Measurable.subtype_coe
#check integral_congr_ae
#check ae_all_iff
#check Finset.sum_congr
#check MeasureTheory.memLp_of_bounded
#check BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
#check BanditRL.OnlineLearning.predictable_private_seed_independent
#check BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#check MeasureTheory.NullMeasurable.aemeasurable
#check AEStronglyMeasurable.of_trim
