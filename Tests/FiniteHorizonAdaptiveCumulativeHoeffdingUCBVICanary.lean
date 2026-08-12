import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeHoeffdingUCBVI

/-!
# Typed canary for the adaptive cumulative Hoeffding UCB-VI foundation

This canary deliberately checks only the compiled foundation: the cumulative
empirical-model update, the totalized Hoeffding calibration, and the exact
generated-policy/model-state alignment.  It is not a cumulative regret canary.
-/

open MeasureTheory

namespace BanditRLProof.Tests.FiniteHorizonAdaptiveCumulativeHoeffdingUCBVICanary

open FiniteHorizonRL
open FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI

local instance : MeasurableSpace Unit := ⊤

noncomputable def mdp : MDP Unit Unit where
  horizon := 1
  transition := ProbabilityTheory.Kernel.deterministic
    (fun _pair => ()) measurable_const
  transition_isMarkov := by infer_instance
  reward := fun _state _action => 0
  measurable_reward := measurable_const

def sampleStep : EpisodeStep Unit Unit where
  state := ()
  action := ()
  reward := 0
  nextState := ()

def sampleBatch : EpisodeBatch mdp 1 :=
  fun _episode _stage => sampleStep

def trajectory : EpisodeBatchTrajectory mdp 1 :=
  fun _round => sampleBatch

def stage : Fin mdp.horizon := ⟨0, by simp [mdp]⟩

noncomputable def initialTable : DeterministicMarkovPolicyTable mdp :=
  fun _stage _state => ()

example :
    (adaptiveCumulativeEmpiricalModelStateAt trajectory 1).2 stage () () =
      (adaptiveCumulativeEmpiricalModelStateAt trajectory 0).2 stage () () +
        (trajectory 1).rewardSum stage () () := by
  simpa using
    adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ
      trajectory 0 stage () ()

example :
    adaptiveCumulativeAggregateVisitCountAt trajectory 1 () () =
      adaptiveCumulativeAggregateVisitCountAt trajectory 0 () () +
        ∑ currentStage : Fin mdp.horizon,
          (trajectory 1).visitCount currentStage () () := by
  simpa using
    adaptiveCumulativeAggregateVisitCountAt_succ trajectory 0 () ()

example :
    logFactor (State := Unit) (Action := Unit) mdp 4 (1 / 2) =
      Real.log
        (((confidenceNumerator (State := Unit) (Action := Unit) mdp 4 : Nat) : Real) /
          (1 / 2)) := by
  exact logFactor_eq_paper mdp 4 (1 / 2)
    (by simp [mdp]) (by norm_num) (by norm_num) (by norm_num)

noncomputable example :
    (source mdp (Measure.dirac ()) initialTable () 4 (1 / 2)).policyAt
        trajectory 1 =
      ((adaptiveCumulativeEmpiricalModelStateAt trajectory 0).1
        |>.countRadiusOptimisticPlan mdp ()
          (countRadius (State := Unit) (Action := Unit) mdp 4 (1 / 2))
        |>.optimisticPolicy) := by
  simpa using
    source_policyAt_succ_eq_modelState_optimisticPolicy
      mdp (Measure.dirac ()) initialTable () 4 (1 / 2) trajectory 0

#check EpisodeBatchPrefix.measurable_cumulativeEmpiricalModelState
#check measurable_adaptiveCumulativeEmpiricalModelStateAt
#check adaptiveCumulativeEmpiricalModelStateAt_transitionCount_succ
#check adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ
#check adaptiveCumulativeEmpiricalModelStateAt_visitCount
#check TransitionCountSummary.measurable_aggregateVisitCount
#check measurable_adaptiveCumulativeAggregateVisitCountAt
#check adaptiveCumulativeAggregateVisitCountAt_eq_sum
#check adaptiveCumulativeAggregateVisitCountAt_succ
#check AdaptiveCumulativeEmpiricalModelState.empiricalReward_of_visitCount_eq_zero
#check logFactor_eq_paper
#check countRadius_zero
#check countRadius_of_pos
#check source_policyAt_succ_eq_modelState_optimisticPolicy

#print axioms measurable_adaptiveCumulativeEmpiricalModelStateAt
#print axioms adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ
#print axioms adaptiveCumulativeAggregateVisitCountAt_succ
#print axioms logFactor_eq_paper
#print axioms source_policyAt_succ_eq_modelState_optimisticPolicy

end BanditRLProof.Tests.FiniteHorizonAdaptiveCumulativeHoeffdingUCBVICanary
