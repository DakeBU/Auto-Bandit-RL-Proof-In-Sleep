import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Data.Fin.Tuple.Basic

open MeasureTheory ProbabilityTheory unitInterval
set_option pp.universes true
set_option pp.proofs false

#check Kernel.exists_measurable_map_eq_unitInterval
#check Measure.infinitePi
#check Measure.infinitePi_map_eval
#check iIndepFun_infinitePi
#check iIndepFun.indepFun_finset
#check indepFun_prod
#check indepFun_iff_map_prod_eq_prod_map_map
#check Measure.map_fst_prod
#check Measure.map_snd_prod
#check Measure.map_map
#check Measure.map_apply
#check Measure.prod_apply
#check Measure.compProd_apply
#check condDistrib_ae_eq_of_measure_eq_compProd
#check Measurable.of_uncurry_left
#check measurable_pi_iff
#check Fin.snoc
#check Fin.snoc_last
#check Fin.snoc_castSucc
#check Fin.cases
#check Fin.lastCases
#check Finset.mem_range
#check BanditRL.OnlineLearning.independent_private_seed_pair
#check BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
