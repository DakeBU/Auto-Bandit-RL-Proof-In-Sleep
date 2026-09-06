import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmPathIntegrability
import BanditRLProof.Algorithms.ThompsonStationaryReward
import BanditRLProof.Algorithms.UCBArmStreamFiniteArmRewardLaws

/-!
# Fixed-IID source adapter for the two-arm stochastic-gradient bandit

This module realizes the reward model used by the two-arm source theorem from
an arm-indexed family of fixed probability laws.  The environment is the
stationary history environment over `Unit`; hence its initial and successor
reward fibers are exactly the selected arm law and cannot reveal a latent,
changing environment.

The adapter is deliberately narrower than
`TwoArmBoundedFixedMeanEnvironmentContract`.  The latter also admits
history-dependent reward laws with fixed means, whereas this module produces
one fixed law per arm.  No global recurrence iteration or regret endpoint is
claimed here.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory

/--
The fixed two-arm reward kernel, with a trivial environment coordinate added
for the measurable-history-environment interface.
-/
noncomputable def twoArmFixedIIDRewardKernel
    (armLaw : Fin 2 -> Measure Real) : Kernel (Unit × Fin 2) Real :=
  (UCB.finiteArmRealRewardKernel armLaw).comap Prod.snd measurable_snd

@[simp]
theorem twoArmFixedIIDRewardKernel_apply
    (armLaw : Fin 2 -> Measure Real) (env : Unit) (arm : Fin 2) :
    twoArmFixedIIDRewardKernel armLaw (env, arm) = armLaw arm := by
  rw [twoArmFixedIIDRewardKernel, Kernel.comap_apply,
    UCB.finiteArmRealRewardKernel_apply]

/-- Pointwise probability laws make the fixed two-arm kernel Markov. -/
theorem twoArmFixedIIDRewardKernel_isMarkov
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    IsMarkovKernel (twoArmFixedIIDRewardKernel armLaw) := by
  letI : IsMarkovKernel (UCB.finiteArmRealRewardKernel armLaw) :=
    UCB.finiteArmRealRewardKernel_isMarkov armLaw hprob
  unfold twoArmFixedIIDRewardKernel
  infer_instance

/--
The fixed-IID source environment.  Conditional on the selected arm, every
round uses the same arm law and ignores the observed history.
-/
noncomputable def twoArmFixedIIDEnvironment
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    Thompson.MeasurableHistoryEnvironment Unit (Fin 2) Real := by
  letI : IsMarkovKernel (twoArmFixedIIDRewardKernel armLaw) :=
    twoArmFixedIIDRewardKernel_isMarkov armLaw hprob
  exact Thompson.stationaryMeasurableHistoryEnvironment
    (twoArmFixedIIDRewardKernel armLaw)

@[simp]
theorem twoArmFixedIIDEnvironment_initialFeedback_apply
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (env : Unit) (arm : Fin 2) :
    (twoArmFixedIIDEnvironment armLaw hprob).initialFeedback (env, arm) =
      armLaw arm := by
  simp [twoArmFixedIIDEnvironment]

@[simp]
theorem twoArmFixedIIDEnvironment_feedback_apply
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (n : Nat) (env : Unit)
    (history : History.FinitePairHistory (Fin 2) Real n) (arm : Fin 2) :
    (twoArmFixedIIDEnvironment armLaw hprob).feedback n
        (env, (history, arm)) =
      armLaw arm := by
  simp [twoArmFixedIIDEnvironment]

/-- Real-valued rewards need no extra measurability assumption beyond their law. -/
theorem twoArmFixedIIDReward_aestronglyMeasurable
    (armLaw : Fin 2 -> Measure Real) (arm : Fin 2) :
    AEStronglyMeasurable (fun reward : Real => reward) (armLaw arm) :=
  measurable_id.aestronglyMeasurable

/--
Fixed probability laws supported on `[-1,1]` with the stated arm means produce
the uniform bounded fixed-mean contract used by the compiled two-arm
recurrences.
-/
theorem twoArmFixedIIDEnvironment_contract
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm) :
    TwoArmBoundedFixedMeanEnvironmentContract
      (twoArmFixedIIDEnvironment armLaw hprob) mean := by
  constructor
  · intro env selected
    simpa using hbound selected
  · intro env selected
    simpa using hmean selected
  · intro n env history selected
    simpa using hbound selected
  · intro n env history selected
    simpa using hmean selected

/-- Equation (5) on every generated fixed-IID successor history, with the
source-increment integrability premise discharged from the fixed reward-law
support.  This remains a one-step conditional-kernel identity; it does not
perform a global tower iteration. -/
theorem integral_twoArmFixedIIDHistoryStepKernel_sourceIncrement_eq_gapCoordinate
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm)
    (initialTheta : Fin 2 -> Real) (eta : Real)
    (n : Nat) (history : History.FinitePairHistory (Fin 2) Real n)
    (gap : Fin 2 -> Real) (bestMean : Real) (coordinate : Fin 2)
    (hgap : forall action, gap action = bestMean - mean action) :
    integral
        (Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm initialTheta eta)
          (twoArmFixedIIDEnvironment armLaw hprob) n ((), history))
        (fun pair : Fin 2 × Real =>
          sourceIncrement
            (softmaxProbability
              (historyParameter initialTheta eta n history))
            pair.2 pair.1 coordinate) =
      softmaxProbability
          (historyParameter initialTheta eta n history) coordinate *
        (instantaneousGap
          (softmaxProbability
            (historyParameter initialTheta eta n history)) gap -
          gap coordinate) := by
  let contract :=
    twoArmFixedIIDEnvironment_contract armLaw hprob mean hbound hmean
  apply
    integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_gapCoordinate
      initialTheta eta (twoArmFixedIIDEnvironment armLaw hprob)
      n () history mean gap bestMean coordinate
  · exact
      integrable_measurableTwoArmHistoryStepKernel_sourceIncrement_of_contract
        initialTheta eta (twoArmFixedIIDEnvironment armLaw hprob)
        mean contract n () history coordinate
  · intro selected
    simpa using hmean selected
  · exact hgap

end StochasticGradientBandit
end BanditRLProof
