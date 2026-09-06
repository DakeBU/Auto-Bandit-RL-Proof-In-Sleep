import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNativeTrajectory

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

#check UCB.armStreamMeasure_map_frestrictLe_eq_pi
#check UCB.extendArmStreamFinitePrefix
#check UCB.measurable_extendArmStreamFinitePrefix
#check UCB.extendArmStreamFinitePrefix_apply_of_le
#check UCB.armStreamMeasure_map_output_coordinate_compProd_comap_without_eq_prod
#check Measure.compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq
#check Measure.map_compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq

namespace Thompson

#check latentArmStreamTrajectoryKernel_map_prefix_next_eq_compProd
#check latentArmStreamFeedback_eq_of_withoutCoordinate_eq_of_selectedCoordinate_ne
#check historyStepKernel_apply_eq_of_withoutCoordinate_eq_of_target_count_lt
#check latentArmStreamNextActionNeSet
#check latentArmStreamInitialSafeArmSet
#check measurableSet_latentArmStreamNextActionNeSet
#check historyStepKernel_apply_restrict_nextActionNe_eq_of_withoutCoordinate_eq
#check latentArmStreamTrajectoryKernel_map_frestrictLe_zero
#check latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
#check latentArmStreamVisiblePrefixKernel
#check instLatentArmStreamVisiblePrefixKernelIsMarkov
#check latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap
#check latentArmStreamVisiblePrefixNextAction
#check measurable_latentArmStreamVisiblePrefixNextAction
#check latentArmStreamVisibleNextReward
#check measurable_latentArmStreamVisibleNextReward
#check latentArmStreamPrefixCountCap
#check measurableSet_latentArmStreamPrefixCountCap
#check singletonPairHistory_preimage_latentArmStreamPrefixCountCap_zero
#check latentArmStreamPrefixCountCapLocality_zero
#check latentArmStreamPrefixCountLt
#check measurableSet_latentArmStreamPrefixCountLt
#check latentArmStreamPrefixCountEq
#check measurableSet_latentArmStreamPrefixCountEq
#check realHistoryPullCount_extendPairHistorySucc
#check mem_latentArmStreamPrefixCountCap_extendPairHistorySucc_iff
#check latentArmStreamPrefixCountCap_of_extendPairHistorySucc_mem
#check selectedCoordinate_ne_of_extendPairHistorySucc_mem_prefixCountCap
#check latentArmStreamSuccessorCountCap_preimage
#check latentArmStreamSuccessorCountCapSection
#check measurableSet_latentArmStreamSuccessorCountCapSection
#check historyStepKernel_apply_restrict_successorCountCap_eq_of_withoutCoordinate_eq
#check latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_succ
#check latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_eq_of_withoutCoordinate_eq
#check latentArmStreamVisiblePrefixNextActionBranchKernel
#check instLatentArmStreamVisiblePrefixNextActionBranchKernelIsFinite
#check LatentArmStreamVisiblePrefixNextActionBranchLocality
#check latentArmStreamVisiblePrefixNextActionBranchLocality_of_prefixCountCapLocality
#check latentArmStreamVisiblePrefixNextActionBranchLocality
#check latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod_of_locality
#check latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod
#check latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd
#check latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae
#check measurable_latentArmStreamSelectedCoordinate
#check latentArmStreamVisiblePrefixNextAction_selectedCoordinate_branch_eq_prod
#check latentArmStreamVisiblePrefixNextAction_selectedCoordinate_mixed_eq_compProd
#check latentArmStreamVisiblePrefixNextAction_selectedCoordinate_eq_compProd
#check latentArmStreamVisibleNextReward_joint_eq_compProd
#check latentArmStreamVisibleNextReward_condDistrib_ae_eq_nu
#check latentArmStreamVisibleTrajectoryMeasure_nextReward_joint_eq_compProd
#check latentArmStreamVisibleTrajectoryMeasure_nextReward_condDistrib_ae_eq_nu
#check latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq

/-- Direct-use canary for the discharged branch-locality contract. -/
example
    {Env : Type} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env) (n : Nat) :
    LatentArmStreamVisiblePrefixNextActionBranchLocality algorithm env n := by
  exact latentArmStreamVisiblePrefixNextActionBranchLocality algorithm env n

/-- The deferred-decisions layer proves branch locality, branch aggregation,
and one-step selected-reward freshness while leaving native-prefix
identification and selected-IID laws explicit. -/
example
    {Env : Type} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map
        (fun sample : UCB.ArmRewardStream K ×
            ((t : Nat) -> Fin K × Real) =>
          (Preorder.frestrictLe n sample.1,
            Preorder.frestrictLe n sample.2))
        (latentArmStreamTrajectoryMeasure algorithm env nu) =
      Measure.pi (fun _ : Finset.Iic n =>
          Measure.infinitePi fun arm : Fin K => nu arm) ⊗ₘ
        latentArmStreamVisiblePrefixKernel algorithm env n := by
  exact latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq
    algorithm env nu n

/-- Direct-use canary for selected-reward freshness on the observable trajectory
marginal. -/
example
    {Env : Type} {K : Nat} [MeasurableSpace Env]
    [StandardBorelSpace Env] [NeZero K]
    (algorithm : HistoryAlgorithm (Fin K) Real) (env : Env)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    let visibleMeasure :=
      (latentArmStreamTrajectoryMeasure algorithm env nu).map Prod.snd
    condDistrib
        (latentArmStreamVisibleNextReward n)
        (latentArmStreamVisiblePrefixNextAction n)
        visibleMeasure =ᵐ[
      visibleMeasure.map (latentArmStreamVisiblePrefixNextAction n)]
      UCB.armStreamSelectedRewardKernel n nu := by
  exact
    latentArmStreamVisibleTrajectoryMeasure_nextReward_condDistrib_ae_eq_nu
      algorithm env nu n

#print axioms UCB.armStreamMeasure_map_frestrictLe_eq_pi
#print axioms Measure.compProd_restrict_prod
#print axioms Measure.compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq
#print axioms Measure.map_compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq
#print axioms map_snd_x_compProd_comap_eq_prod_map_of_indepFun
#print axioms UCB.armStreamMeasure_map_output_coordinate_compProd_comap_without_eq_prod
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_restrict_countCap_eq_of_withoutCoordinate_eq
#print axioms latentArmStreamVisiblePrefixNextActionBranchLocality
#print axioms latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod_of_locality
#print axioms latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod
#print axioms latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd
#print axioms latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae
#print axioms measurable_latentArmStreamSelectedCoordinate
#print axioms latentArmStreamVisiblePrefixNextAction_selectedCoordinate_branch_eq_prod
#print axioms latentArmStreamVisiblePrefixNextAction_selectedCoordinate_mixed_eq_compProd
#print axioms latentArmStreamVisiblePrefixNextAction_selectedCoordinate_eq_compProd
#print axioms latentArmStreamVisibleNextReward_joint_eq_compProd
#print axioms latentArmStreamVisibleNextReward_condDistrib_ae_eq_nu
#print axioms latentArmStreamVisibleTrajectoryMeasure_nextReward_joint_eq_compProd
#print axioms latentArmStreamVisibleTrajectoryMeasure_nextReward_condDistrib_ae_eq_nu
#print axioms latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq

end Thompson
end BanditRLProof
