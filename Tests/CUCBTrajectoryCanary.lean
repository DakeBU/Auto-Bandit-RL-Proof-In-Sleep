import BanditRLProof.Algorithms.CUCBTrajectory
import BanditRLProof.Algorithms.CUCBObservationMGF

/-! Causal feedback/update checks, not a completed noisy performance canary. -/
namespace Tests.CUCBTrajectoryCanary
open BanditRLProof.CUCB

private noncomputable def feedback : Feedback 3 :=
  (fun i => decide (i.val=0 ∨ i.val=2),
    (fun i => if i.val=0 then ⟨1/4, by norm_num⟩ else ⟨3/4, by norm_num⟩, 5))

theorem only_observed_arms_counted :
    observationCount (fun _ => feedback) 1 0=1 ∧
    observationCount (fun _ => feedback) 1 1=0 ∧
    observationCount (fun _ => feedback) 1 2=1 := by
  norm_num [observationCount, feedback, Finset.sum_range_succ]

theorem observed_means_and_unseen_initialization :
    empiricalMean (fun _ => feedback) 1 0=1/4 ∧
    empiricalMean (fun _ => feedback) 1 1=1 ∧
    empiricalMean (fun _ => feedback) 1 2=3/4 := by
  norm_num [empiricalMean, observationCount, observationSum, observation, feedback,
    Finset.sum_range_succ]
  split_ifs <;> norm_num at *
  omega

theorem first_input_all_one : oracleInput (fun _ => feedback) 0=initialInput 3 :=
  oracleInput_zero _

#print axioms oracleInput_causal
#print axioms measurable_oracleInput
#print axioms cucbTrajectory_initial_law
#print axioms cucbTrajectory_condDistrib
#print axioms roundKernel_rectangle
#print axioms roundKernel_action_law
#print axioms observed_means_and_unseen_initialization
#print axioms marginal_subgaussian
#print axioms integrable_observedFactor
#print axioms integral_observedFactor_le_one
#print axioms observedFactor_eq_exp
end Tests.CUCBTrajectoryCanary
