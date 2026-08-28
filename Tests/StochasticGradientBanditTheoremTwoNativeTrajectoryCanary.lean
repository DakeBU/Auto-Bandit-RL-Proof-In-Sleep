import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNativeTrajectory

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

#check UCB.armStreamMeasure_map_frestrictLe_eq_pi
#check UCB.extendArmStreamFinitePrefix
#check UCB.measurable_extendArmStreamFinitePrefix
#check UCB.extendArmStreamFinitePrefix_apply_of_le
#check UCB.armStreamMeasure_map_output_coordinate_compProd_comap_without_eq_prod

namespace Thompson

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
#check realHistoryPullCount_extendPairHistorySucc
#check latentArmStreamVisiblePrefixNextActionBranchKernel
#check instLatentArmStreamVisiblePrefixNextActionBranchKernelIsFinite
#check LatentArmStreamVisiblePrefixNextActionBranchLocality
#check latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod_of_locality
#check latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd
#check latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae
#check latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq

/-- The deferred-decisions producer exposes an exact finite mixture while
leaving the still-unproved native-prefix identification explicit. -/
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

#print axioms UCB.armStreamMeasure_map_frestrictLe_eq_pi
#print axioms Measure.compProd_restrict_prod
#print axioms map_snd_x_compProd_comap_eq_prod_map_of_indepFun
#print axioms UCB.armStreamMeasure_map_output_coordinate_compProd_comap_without_eq_prod
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap
#print axioms latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod_of_locality
#print axioms latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd
#print axioms latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae
#print axioms latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq

end Thompson
end BanditRLProof
