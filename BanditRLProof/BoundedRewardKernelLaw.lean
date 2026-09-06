import BanditRLProof.ConcentrationSubGaussian
import BanditRLProof.RewardKernel

/-!
# Centered laws for bounded context-dependent reward kernels

This module constructs the one-step centered reward-kernel contract directly
from pointwise MGF witnesses or common almost-sure bounds. It is independent of
any bandit algorithm or trajectory construction.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace Concentration

/-- A nondegenerate interval has a strictly positive Hoeffding proxy. -/
theorem intervalVarianceProxy_pos_of_lt
    {lo hi : Real} (hlohi : lo < hi) :
    0 < ((intervalVarianceProxy lo hi : NNReal) : Real) := by
  have hdiff : 0 < hi - lo := sub_pos.mpr hlohi
  have hnorm : 0 < ‖hi - lo‖ := norm_pos_iff.mpr (ne_of_gt hdiff)
  rw [show ((intervalVarianceProxy lo hi : NNReal) : Real) =
      (‖hi - lo‖ / 2) ^ 2 by
    simp [intervalVarianceProxy]]
  positivity

end Concentration

namespace RewardKernel

/--
Exact pointwise means and centered sub-Gaussian MGF witnesses form a centered
law for an arbitrary context/action Markov reward kernel.
-/
noncomputable def centeredRewardKernelLaw_of_hasSubgaussianMGF
    {Context Action : Type}
    [MeasurableSpace Context] [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean : forall context arm,
      integral (selectedMeasure rewardKernel context arm)
          (fun reward : Rat => ((reward : Rat) : Real)) =
        ((mean context arm : Rat) : Real))
    (hsubG : forall context arm,
      HasSubgaussianMGF
        (fun reward : Rat =>
          (((reward - mean context arm : Rat) : Real)))
        (varianceProxy context arm)
        (selectedMeasure rewardKernel context arm)) :
    CenteredRewardKernelLaw rewardKernel mean varianceProxy where
  integrable := by
    intro context arm
    exact (hsubG context arm).integrable
  integral_eq_zero := by
    intro context arm
    haveI : IsProbabilityMeasure
        (selectedMeasure rewardKernel context arm) := by
      change IsProbabilityMeasure (rewardKernel.kernel (context, arm))
      exact isProbabilityMeasure_apply rewardKernel (context, arm)
    have hcenter := (hsubG context arm).integrable
    have hconst : Integrable
        (fun _reward : Rat => ((mean context arm : Rat) : Real))
        (selectedMeasure rewardKernel context arm) := integrable_const _
    have hraw : Integrable
        (fun reward : Rat => ((reward : Rat) : Real))
        (selectedMeasure rewardKernel context arm) := by
      convert hcenter.add hconst using 1
      funext reward
      simp
    simp_rw [Rat.cast_sub]
    rw [integral_sub hraw hconst, hmean context arm]
    simp
  hasSubgaussianMGF := hsubG

/--
Common almost-sure reward bounds and exact pointwise means form a centered law
for an arbitrary context/action Markov reward kernel.
-/
noncomputable def boundedCenteredRewardKernelLaw
    {Context Action : Type}
    [MeasurableSpace Context] [MeasurableSpace Action]
    (rewardKernel : MarkovRewardKernel (Context × Action) Rat)
    (mean : Context -> Action -> Rat)
    (lo hi : Real)
    (hmeas : forall context arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (selectedMeasure rewardKernel context arm))
    (hbound : forall context arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (selectedMeasure rewardKernel context arm)))
    (hmean : forall context arm,
      integral (selectedMeasure rewardKernel context arm)
          (fun reward : Rat => ((reward : Rat) : Real)) =
        ((mean context arm : Rat) : Real)) :
    CenteredRewardKernelLaw rewardKernel mean
      (fun _ _ => Concentration.intervalVarianceProxy lo hi) := by
  apply centeredRewardKernelLaw_of_hasSubgaussianMGF
    rewardKernel mean
      (fun _ _ => Concentration.intervalVarianceProxy lo hi) hmean
  intro context arm
  haveI : IsProbabilityMeasure
      (selectedMeasure rewardKernel context arm) := by
    change IsProbabilityMeasure (rewardKernel.kernel (context, arm))
    exact isProbabilityMeasure_apply rewardKernel (context, arm)
  simpa [Rat.cast_sub] using
    (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := selectedMeasure rewardKernel context arm)
      (X := fun reward : Rat => ((reward : Rat) : Real))
      (lo := lo)
      (hi := hi)
      (mean := ((mean context arm : Rat) : Real))
      (hmeas context arm) (hbound context arm) (hmean context arm))

end RewardKernel
end BanditRLProof
