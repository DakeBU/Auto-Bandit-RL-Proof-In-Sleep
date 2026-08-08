import BanditRLProof.Algorithms.UCBConditionalRewardPairTrajectorySampledAsymptotics
import BanditRLProof.FiniteArmRewardKernelLaw

/-!
# Sampled-pair UCB consistency for finite-arm sub-Gaussian laws

This module instantiates the canonical sampled pair-trajectory asymptotic UCB
route from stationary action-indexed reward laws.  The fixed initial action is
paired with a reward sampled from its arm law, while all successor laws use the
context-independent Markov reward kernel.
-/

open scoped BigOperators ENNReal NNReal

open Filter MeasureTheory ProbabilityTheory
open Asymptotics

namespace BanditRLProof
namespace UCB

/-- Initial pair law obtained by attaching a fixed action to its reward law. -/
noncomputable def finiteArmSubgaussianInitialActionRewardMeasure
    {K : Nat} (armLaw : Fin K -> Measure Rat) (defaultAction : Fin K) :
    Measure (Prod (Fin K) Rat) :=
  Measure.map (Prod.mk defaultAction) (armLaw defaultAction)

/-- The fixed-action reward pushforward remains a probability measure. -/
theorem finiteArmSubgaussianInitialActionRewardMeasure_isProbabilityMeasure
    {K : Nat}
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (defaultAction : Fin K) :
    IsProbabilityMeasure
      (finiteArmSubgaussianInitialActionRewardMeasure armLaw defaultAction) := by
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  exact Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable

/--
Exact sampled-successor expected pseudo-regret for stationary finite-arm
sub-Gaussian laws.  The UCB proxy is the armwise maximum padded by one and the
confidence schedule is `1 / (T + 1)`.
-/
noncomputable def selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (defaultAction : Fin K)
    (T : Nat) : Real :=
  let mu0 :=
    finiteArmSubgaussianInitialActionRewardMeasure armLaw defaultAction
  letI : IsProbabilityMeasure mu0 :=
    finiteArmSubgaussianInitialActionRewardMeasure_isProbabilityMeasure
      armLaw hprob defaultAction
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Unit) armLaw hprob
  let context :
      (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Unit := fun _ _ => ()
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
  selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
    model mu0 rewardKernel context defaultAction sigma2
      (fun _ => measurable_const) T

/--
The exact practical sampled-successor expected pseudo-regret is nonnegative
and satisfies the fixed-model logarithmic envelope at every large horizon.
-/
theorem selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_nonneg_and_le
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K)
    (T : Nat) (hlarge : 2 * K <= T + 1) :
    0 <= selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
        model armLaw hprob varianceProxy defaultAction T /\
      selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
          model armLaw hprob varianceProxy defaultAction T <=
        selectedPolicySuccessorAsymptoticModelCoefficient model
            (Concentration.finiteArmPositiveVarianceProxy varianceProxy) *
          (1 + Real.log (((T + 1 : Nat) : Real))) := by
  have hT : 0 < T := by
    have hK := model.hK
    omega
  let mu0 :=
    finiteArmSubgaussianInitialActionRewardMeasure armLaw defaultAction
  letI : IsProbabilityMeasure mu0 :=
    finiteArmSubgaussianInitialActionRewardMeasure_isProbabilityMeasure
      armLaw hprob defaultAction
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Unit) armLaw hprob
  let context :
      (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Unit := fun _ _ => ()
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
  have hmeanMeas :
      Measurable (fun pair : Prod Unit (Fin K) => model.mean pair.2) :=
    (measurable_of_countable model.mean).comp measurable_snd
  have law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel
        (fun _ arm => model.mean arm)
        (fun _ arm => varianceProxy arm) := by
    simpa [rewardKernel] using
      (RewardKernel.contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
        (Context := Unit)
        armLaw hprob model.mean varianceProxy hmean hsubG)
  have hsigma2 : 0 < (((sigma2 : NNReal) : Real)) := by
    simpa [sigma2] using
      (Concentration.finiteArmPositiveVarianceProxy_pos varianceProxy)
  simpa [selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret,
    mu0, rewardKernel, context, sigma2] using
    (selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_nonneg_and_le
      (model := model)
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := fun _ arm => varianceProxy arm)
      (defaultAction := defaultAction)
      (sigma2 := sigma2)
      (hcontext := fun _ => measurable_const)
      (hmean := hmeanMeas)
      (law := law)
      (hvariance := fun _ _ arm =>
        Concentration.varianceProxy_le_finiteArmPositiveVarianceProxy
          varianceProxy arm)
      (harmMean := fun _ _ _ => rfl)
      (hsigma2 := hsigma2)
      (T := T)
      (hT := hT)
      (hlarge := hlarge))

/-- The exact practical expected pseudo-regret family is logarithmic. -/
theorem selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_isBigO_log
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K) :
    (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
      model armLaw hprob varianceProxy defaultAction) =O[atTop]
      (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) := by
  let mu0 :=
    finiteArmSubgaussianInitialActionRewardMeasure armLaw defaultAction
  letI : IsProbabilityMeasure mu0 :=
    finiteArmSubgaussianInitialActionRewardMeasure_isProbabilityMeasure
      armLaw hprob defaultAction
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Unit) armLaw hprob
  let context :
      (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Unit := fun _ _ => ()
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
  have hmeanMeas :
      Measurable (fun pair : Prod Unit (Fin K) => model.mean pair.2) :=
    (measurable_of_countable model.mean).comp measurable_snd
  have law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel
        (fun _ arm => model.mean arm)
        (fun _ arm => varianceProxy arm) := by
    simpa [rewardKernel] using
      (RewardKernel.contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
        (Context := Unit)
        armLaw hprob model.mean varianceProxy hmean hsubG)
  have hsigma2 : 0 < (((sigma2 : NNReal) : Real)) := by
    simpa [sigma2] using
      (Concentration.finiteArmPositiveVarianceProxy_pos varianceProxy)
  simpa [selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret,
    mu0, rewardKernel, context, sigma2] using
    (selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_isBigO_log
      (model := model)
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := fun _ arm => varianceProxy arm)
      (defaultAction := defaultAction)
      (sigma2 := sigma2)
      (hcontext := fun _ => measurable_const)
      (hmean := hmeanMeas)
      (law := law)
      (hvariance := fun _ _ arm =>
        Concentration.varianceProxy_le_finiteArmPositiveVarianceProxy
          varianceProxy arm)
      (harmMean := fun _ _ _ => rfl)
      (hsigma2 := hsigma2))

/-- The exact practical expected pseudo-regret is little-o of `T + 1`. -/
theorem selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_isLittleO_natCast_succ
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K) :
    (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
      model armLaw hprob varianceProxy defaultAction) =o[atTop]
      (fun T : Nat => (((T + 1 : Nat) : Real))) :=
  (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_isBigO_log
    model armLaw hprob varianceProxy hmean hsubG defaultAction).trans_isLittleO
      log_natCast_succ_isLittleO_natCast_succ

/-- Expected practical sampled-successor pseudo-regret normalized by `T + 1`. -/
noncomputable def
    selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (defaultAction : Fin K)
    (T : Nat) : Real :=
  selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret
      model armLaw hprob varianceProxy defaultAction T /
    (((T + 1 : Nat) : Real))

/--
For stationary finite-arm sub-Gaussian reward laws, the expected pseudo-regret
of the horizon-indexed canonical sampled-pair UCB family, normalized by
`T + 1`, tends to zero.
-/
theorem selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret_tendsto_zero
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K) :
    Tendsto
      (selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret
        model armLaw hprob varianceProxy defaultAction)
      atTop (nhds 0) := by
  have hlimit :=
    (selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_isLittleO_natCast_succ
      model armLaw hprob varianceProxy hmean hsubG
        defaultAction).tendsto_div_nhds_zero
  convert hlimit using 1

end UCB
end BanditRLProof
