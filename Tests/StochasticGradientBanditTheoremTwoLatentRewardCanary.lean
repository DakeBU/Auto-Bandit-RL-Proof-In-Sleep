import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoLatentReward

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

#check UCB.armStreamMeasure_map_fixedArmFinitePrefix_eq_pi
#check Thompson.latentArmStreamTrajectoryMeasure_map_fixedArmFinitePrefix_eq_pi

namespace StochasticGradientBandit

#check twoArmFixedIIDLatentTrajectoryMeasure
#check instTwoArmFixedIIDLatentTrajectoryMeasureIsProbability
#check twoArmTrajectoryMeasure_dirac_eq_map_trajectoryKernel
#check stationaryRewardKernelAt_twoArmFixedIIDRewardKernel_eq
#check twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi
#check twoArmNthOptimalPullReward_eq_latentCoordinate_ae

/-- The exact two-arm wrapper exposes a genuine finite product law rather than
a list of one-dimensional marginals. -/
example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) :
    Measure.map
        (fun sample :
            UCB.ArmRewardStream 2 × ((n : Nat) -> Fin 2 × Real) =>
          fun i : Fin 3 => sample.1 (i : Nat) 0)
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) =
      Measure.pi (fun _ : Fin 3 => armLaw 0) := by
  exact
    twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi
      armLaw hprob eta 3

/-- The finite-pull readout keeps the chronological witness explicit and does
not totalize a missing pull into an IID coordinate. -/
example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) (pullIndex : Nat) :
    ∀ᵐ sample ∂twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta,
      ∀ t : Nat,
        twoArmNthOptimalPullTime (Env := Unit) pullIndex ((), sample.2) =
            (t : WithTop Nat) ->
          twoArmNthOptimalPullReward (Env := Unit) pullIndex ((), sample.2) =
            sample.1 pullIndex 0 := by
  exact twoArmNthOptimalPullReward_eq_latentCoordinate_ae
    armLaw hprob eta pullIndex

#print axioms UCB.armStreamMeasure_map_fixedArmFinitePrefix_eq_pi
#print axioms Thompson.latentArmStreamTrajectoryMeasure_map_fixedArmFinitePrefix_eq_pi
#print axioms twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi
#print axioms twoArmNthOptimalPullReward_eq_latentCoordinate_ae

end StochasticGradientBandit
end BanditRLProof
