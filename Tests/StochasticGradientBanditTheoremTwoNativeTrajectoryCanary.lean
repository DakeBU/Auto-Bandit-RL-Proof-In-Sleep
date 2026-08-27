import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNativeTrajectory

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

#check UCB.armStreamMeasure_map_frestrictLe_eq_pi
#check UCB.extendArmStreamFinitePrefix
#check UCB.measurable_extendArmStreamFinitePrefix
#check UCB.extendArmStreamFinitePrefix_apply_of_le

namespace Thompson

#check latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
#check latentArmStreamVisiblePrefixKernel
#check instLatentArmStreamVisiblePrefixKernelIsMarkov
#check latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap
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
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_eq_of_streamPrefix_eq
#print axioms latentArmStreamTrajectoryKernel_map_frestrictLe_eq_prefixKernel_comap
#print axioms latentArmStreamTrajectoryMeasure_map_stream_visiblePrefix_eq

end Thompson
end BanditRLProof
