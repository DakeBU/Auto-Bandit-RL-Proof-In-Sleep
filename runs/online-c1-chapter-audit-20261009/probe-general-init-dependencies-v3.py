from common_v1 import *
fixed()
write(RUN/'general-init-retrieval-type-probe-v3.lean','''import BanditRLProof.OnlineLearningFTLState
import BanditRLProof.OnlineFTLLimitSemantics

open Filter BanditRL.OnlineLearning
#check Finset.sum_range_succ'
#check ftlPredict_prefix
#check ftlState_eq_predict
#check meanPredict_bestRegret_refined
#check meanPredict_bestRegret_bound
#check comparatorRegret_le_squaredBestRegret
#check noRegret_of_vanishing_bound
#check meanPredict_bestRegret_average_tendsto_zero
#check tendsto_const_div_atTop_nhds_zero_nat
#check Real.tendsto_pow_log_div_mul_add_atTop
#check tendsto_natCast_atTop_atTop
''')
gate('general-init-retrieval-type-probe-v3','lake','env','lean',RUN/'general-init-retrieval-type-probe-v3.lean')
write(RUN/'general-init-retrieval-readiness-v3.json',dict(actual_minimal_two_import_type_probe_exit=0,actual_declaration_checks=11,
    actual_existing_general_init_performance_name_search_found_none=True,
    scalar_limit_reuse='Exact local Mathlib Analysis/SpecificLimits/Basic.lean:51 tendsto_const_div_atTop_nhds_zero_nat; no new constant/T lemma needed.',
    only_dependency_type_readiness_no_new_theorem_body_or_source_acceptance=True))
fixed()
