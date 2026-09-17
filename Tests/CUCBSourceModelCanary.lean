import BanditRLProof.Algorithms.CUCBImpossibleCase
import BanditRLProof.Algorithms.CUCBGapInverse
import BanditRLProof.Algorithms.CUCBOracleSuccess

/-! Source model and deterministic-trigger dependency checks.
The required concrete noisy final-performance witness is still pending. -/
namespace Tests.CUCBSourceModelCanary
open BanditRLProof.CUCB

#print axioms cucbTrajectory_ae_round_property
#print axioms ChargeData.counters_le_observations_ae_of_one
#print axioms FeedbackModel.minTrigger_pos
#print axioms FeedbackModel.minTrigger_le_one
#print axioms FeedbackModel.deterministic_counter_bound
#print axioms FeedbackModel.charged_observation_tail
#print axioms FeedbackModel.nice_event_probability
#print axioms SourceModel.inverseGap_spec
#print axioms SourceModel.chargeData_sufficient
#print axioms SourceModel.not_bad_of_nice_and_sufficient_observations
#print axioms SourceModel.maxPositiveGap_eq_zero_of_no_bad
#print axioms SourceModel.counters_zero_of_no_bad

#print axioms SourceModel.inverseAt_unique
#print axioms SourceModel.inverseAt_gap
#print axioms SourceModel.inverseAt_strictMono
#print axioms SourceModel.gapThreshold_antitone
#print axioms SourceModel.gapThreshold_intervalIntegrable
#print axioms SourceModel.continuous_score
#print axioms SourceModel.continuous_optimum
#print axioms SourceModel.measurableSet_path_oracleSuccess
#print axioms SourceModel.condExp_oracle_success
#print axioms SourceModel.initial_oracle_success
#print axioms SourceModel.oracle_failure_probability
end Tests.CUCBSourceModelCanary
