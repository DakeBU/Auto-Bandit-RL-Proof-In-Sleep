import BanditRLProof.Algorithms.ETCExactSubGaussianTail
import BanditRLProof.RealKernelRegretPullCount

/-!
# Rat arm-law transport to the Real ETC kernel regret surface

This module pushes the existing `Rat` arm laws forward along the cast to
`Real`, identifies the resulting identity-integral kernel means and gaps, and
then assembles the canonical exact per-arm ETC pull-count bounds into the
LML-shaped finite sum for Real kernel regret.

The result is still tied to the canonical generated `Rat` reward history.  It
does not transport an arbitrary native `Real` `IsAlgEnvSeq` process or identify
the local fold argmax with upstream `measurableArgmax` tie semantics.
-/

namespace BanditRLProof

open MeasureTheory

namespace ETC

/-- Push each countable `Rat` arm law forward to a Real-valued arm kernel. -/
noncomputable def ratArmLawRealKernel {K : Nat}
    (armLaw : Fin K -> Measure Rat) :
    ProbabilityTheory.Kernel (Fin K) Real :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun arm =>
      Measure.map (fun reward : Rat => ((reward : Rat) : Real)) (armLaw arm))

@[simp]
theorem ratArmLawRealKernel_apply {K : Nat}
    (armLaw : Fin K -> Measure Rat) (arm : Fin K) :
    ratArmLawRealKernel armLaw arm =
      Measure.map (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm) := by
  rfl

/-- Probability arm laws give a Markov Real pushforward kernel. -/
theorem isMarkovKernel_ratArmLawRealKernel {K : Nat}
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    ProbabilityTheory.IsMarkovKernel (ratArmLawRealKernel armLaw) := by
  constructor
  intro arm
  rw [ratArmLawRealKernel_apply]
  exact
    Measure.isProbabilityMeasure_map
      (measurable_of_countable
        (fun reward : Rat => ((reward : Rat) : Real))).aemeasurable

/-- The pushforward kernel identity integral is the original casted mean. -/
theorem realKernelMean_ratArmLawRealKernel_eq_integral_cast {K : Nat}
    (armLaw : Fin K -> Measure Rat) (arm : Fin K) :
    realKernelMean (ratArmLawRealKernel armLaw) arm =
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) := by
  rw [realKernelMean, ratArmLawRealKernel_apply]
  exact
    integral_map
      (measurable_of_countable
        (fun reward : Rat => ((reward : Rat) : Real))).aemeasurable
      measurable_id.aestronglyMeasurable

/-- Exact arm means identify the pushforward Real kernel mean with the model mean. -/
theorem realKernelMean_ratArmLawRealKernel_eq_modelMean {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (arm : Fin K) :
    realKernelMean (ratArmLawRealKernel armLaw) arm =
      ((model.mean arm : Rat) : Real) := by
  rw [realKernelMean_ratArmLawRealKernel_eq_integral_cast]
  exact hmean arm

/-- The supremum of the cast model means is attained at the local best arm. -/
theorem ciSup_modelMean_cast_eq_bestArm {K : Nat}
    (model : FiniteBanditModel K) :
    (⨆ arm : Fin K, ((model.mean arm : Rat) : Real)) =
      ((model.mean model.bestArm : Rat) : Real) := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  apply le_antisymm
  · exact ciSup_le (fun arm => by
      exact_mod_cast FiniteBanditModel.mean_le_bestArm_mean model arm)
  · exact le_ciSup (f := fun arm : Fin K => ((model.mean arm : Rat) : Real))
      (by simp) model.bestArm

/-- The pushforward Real kernel gap is exactly the cast local model gap. -/
theorem realKernelGap_ratArmLawRealKernel_eq_modelGap {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (arm : Fin K) :
    realKernelGap (ratArmLawRealKernel armLaw) arm =
      ((model.gap arm : Rat) : Real) := by
  rw [realKernelGap, realMeanGap]
  simp_rw [realKernelMean_ratArmLawRealKernel_eq_modelMean model armLaw hmean]
  rw [ciSup_modelMean_cast_eq_bestArm]
  by_cases hbest : arm = model.bestArm
  · subst arm
    simp
  · simp [FiniteBanditModel.gap, FiniteBanditModel.bestMean, hbest,
      Rat.cast_sub]

/--
Canonical exact ETC expected regret against the Real pushforward arm kernel.

This is the finite-arm assembly of the exact per-arm expected pull-count leaf:
the best-arm summand vanishes, while each non-best summand uses the exact
`exp (-m * gap^2 / (4 * sigma2))` count bound.
-/
theorem integral_realKernelRegret_explorationArgmaxAction_le_exact_sum_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - ((model.mean arm : Rat) : Real))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (n : Nat) (hn : K * spec.explorationPulls <= n) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    integral trajMeasure
        (fun trajectory : RewardTrace Rat =>
          realKernelRegret (ratArmLawRealKernel armLaw)
            (ETC.explorationArgmaxAction spec model trajectory) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ((model.gap arm : Rat) : Real) *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  ((model.gap arm : Rat) : Real) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  dsimp only
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let commit : RewardTrace Rat -> Fin K :=
    fun trajectory => ETC.explorationArgmaxCommit spec model trajectory
  let action : RewardTrace Rat -> ActionTrace (Fin K) :=
    fun trajectory => ETC.explorationArgmaxAction spec model trajectory
  have hmeas_coord : forall arm : Fin K,
      Measurable (fun trajectory : RewardTrace Rat =>
        ETC.empMeanAtExploration spec model.bestArm trajectory arm) := by
    exact ETC.measurable_empMeanAtExploration_coordinates
      (spec := spec) (commitArm := model.bestArm)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
  have hmeas_commit : Measurable commit := by
    simpa [commit, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun trajectory : RewardTrace Rat => fun arm : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory arm)
        hmeas_coord)
  have hcount : forall arm : Fin K,
      Integrable
        (fun trajectory : RewardTrace Rat =>
          (pullCount (action trajectory) arm n : Real)) trajMeasure := by
    intro arm
    simpa [action, commit, ETC.explorationArgmaxAction,
      ETC.fixedProductArgmaxAction] using
      (ETC.integrable_real_pullCount_actionWithCommit_choice_of_measurable_commit
        trajMeasure spec commit arm n hmeas_commit)
  rw [show (fun trajectory : RewardTrace Rat =>
      realKernelRegret (ratArmLawRealKernel armLaw)
        (ETC.explorationArgmaxAction spec model trajectory) n) =
      (fun trajectory : RewardTrace Rat =>
        realKernelRegret (ratArmLawRealKernel armLaw)
          (action trajectory) n) by rfl]
  rw [integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount
    trajMeasure (ratArmLawRealKernel armLaw) action n hcount]
  refine Finset.sum_le_sum ?_
  intro arm _harm
  rw [realKernelGap_ratArmLawRealKernel_eq_modelGap model armLaw hmean]
  by_cases hbest : arm = model.bestArm
  · subst arm
    simp
  · exact mul_le_mul_of_nonneg_left
      (ETC.integral_real_pullCount_explorationArgmaxAction_le_exploration_add_remaining_mul_exp_of_armLaws
        spec model armLaw hprob sigma2 hmean hsubG context hcontext
        hexplorationPulls_pos arm n hn (fun h => hbest h))
      ((Rat.cast_nonneg (K := Real)).2
        (FiniteBanditModel.gap_nonneg model arm))

end ETC
end BanditRLProof
