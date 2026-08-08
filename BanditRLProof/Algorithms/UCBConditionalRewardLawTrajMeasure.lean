import BanditRLProof.Algorithms.UCBConditionalRewardLawRegret

/-!
# Canonical reward-only trajectory law for the practical generated UCB policy

This module specializes the canonical reward-only Ionescu-Tulcea trajectory
law to `selectedPolicySuccessorHistoryPolicy`.  It closes the selected-reward
`condExpKernel.map` premise used by the practical UCB regret route, while
leaving reward-range regularity as a separate consumer obligation.
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory

/-- Reward-only history-step kernels for the practical generated UCB policy. -/
noncomputable def selectedPolicySuccessorRewardStepKernelFamily
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) :=
  RewardKernel.historyStepKernelFamily rewardKernel
    (selectedPolicySuccessorHistoryPolicy
      hK sigma2 T delta defaultAction)
    context
    (selectedPolicySuccessorHistoryState
      hK sigma2 T delta defaultAction)
    hcontext
    (measurable_selectedPolicySuccessorHistoryState
      hK sigma2 T delta defaultAction)

/-- Every UCB reward-only history-step kernel is Markov. -/
theorem isMarkovKernel_selectedPolicySuccessorRewardStepKernelFamily
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) :
    forall n : Nat, ProbabilityTheory.IsMarkovKernel
      (selectedPolicySuccessorRewardStepKernelFamily
        hK rewardKernel context hcontext sigma2 T delta defaultAction n) := by
  intro n
  unfold selectedPolicySuccessorRewardStepKernelFamily
  infer_instance

/-- Canonical reward-only trajectory measure for the practical generated UCB policy. -/
noncomputable def selectedPolicySuccessorRewardTrajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) : Measure (RewardTrace Rat) :=
  by
    letI : forall n : Nat, ProbabilityTheory.IsMarkovKernel
        (selectedPolicySuccessorRewardStepKernelFamily
          hK rewardKernel context hcontext sigma2 T delta defaultAction n) :=
      isMarkovKernel_selectedPolicySuccessorRewardStepKernelFamily
        hK rewardKernel context hcontext sigma2 T delta defaultAction
    exact ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) mu0
      (selectedPolicySuccessorRewardStepKernelFamily
        hK rewardKernel context hcontext sigma2 T delta defaultAction)

/-- The canonical UCB reward-only trajectory measure is a probability measure. -/
noncomputable instance instIsProbabilityMeasureSelectedPolicySuccessorRewardTrajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) :
    IsProbabilityMeasure
      (selectedPolicySuccessorRewardTrajMeasure
        hK mu0 rewardKernel context hcontext sigma2 T delta defaultAction) := by
  unfold selectedPolicySuccessorRewardTrajMeasure
  letI : forall n : Nat, ProbabilityTheory.IsMarkovKernel
      (selectedPolicySuccessorRewardStepKernelFamily
        hK rewardKernel context hcontext sigma2 T delta defaultAction n) :=
    isMarkovKernel_selectedPolicySuccessorRewardStepKernelFamily
      hK rewardKernel context hcontext sigma2 T delta defaultAction
  infer_instance

/--
Canonical selected-reward law source for the practical generated UCB policy.
The source constructor transports the canonical comap-trim law to the generated
history filtration.
-/
noncomputable def selectedPolicySuccessorGeneratedUCBSelectedRewardLawSource_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) :
    ConditionalExpectationReward.GeneratedActionSelectedRewardFinitePairHistoryLawSource
      (selectedPolicySuccessorRewardTrajMeasure
        hK mu0 rewardKernel context hcontext sigma2 T delta defaultAction)
      rewardKernel
      (selectedPolicySuccessorHistoryPolicy
        hK sigma2 T delta defaultAction)
      context
      (selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      defaultAction
      (fun trajectory : RewardTrace Rat => trajectory)
      (fun t => measurable_pi_apply t) := by
  exact
    ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy
      (mu := selectedPolicySuccessorRewardTrajMeasure
        hK mu0 rewardKernel context hcontext sigma2 T delta defaultAction)
      (rewardKernel := rewardKernel)
      (policy := selectedPolicySuccessorHistoryPolicy
        hK sigma2 T delta defaultAction)
      (context := context)
      (state := selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      (hcontext := hcontext)
      (hstate := measurable_selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      (defaultAction := defaultAction)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
      (h_reward_map_eq := by
        intro i
        simpa [selectedPolicySuccessorRewardTrajMeasure,
          selectedPolicySuccessorRewardStepKernelFamily] using
          (ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace_trim
            mu0 rewardKernel
            (selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction)
            context
            (selectedPolicySuccessorHistoryState
              hK sigma2 T delta defaultAction)
            hcontext
            (measurable_selectedPolicySuccessorHistoryState
              hK sigma2 T delta defaultAction)
            defaultAction i))

/--
The canonical UCB reward-only trajectory measure satisfies the exact
`historyFiltrationSucc` selected-reward law consumed by the practical regret
theorem.
-/
theorem selectedPolicySuccessorGeneratedUCB_reward_map_eq_selected_policy_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (i : Nat) :
    let mu := selectedPolicySuccessorRewardTrajMeasure
      hK mu0 rewardKernel context hcontext sigma2 T delta defaultAction
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    Filter.Eventually
      (fun trajectory : RewardTrace Rat =>
        @Measure.map (RewardTrace Rat) Rat inferInstance inferInstance
          (fun y : RewardTrace Rat => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel
            (RewardTrace Rat) inferInstance _ mu _
            ((History.historyFiltrationSucc
              (selectedPolicySuccessorGeneratedUCBAction
                hK sigma2 T delta defaultAction reward)
              reward
              (measurable_selectedPolicySuccessorGeneratedUCBAction
                hK sigma2 T delta defaultAction reward
                (fun t => measurable_pi_apply t))
              (fun t => measurable_pi_apply t)) i)
            trajectory) =
        RewardKernel.selectedMeasure rewardKernel
          (context i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i))
          ((selectedPolicySuccessorHistoryPolicy
            hK sigma2 T delta defaultAction i).action
            (selectedPolicySuccessorHistoryState
              hK sigma2 T delta defaultAction i
              (History.finiteRewardHistoryOfTrace (reward trajectory) i))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc
            (selectedPolicySuccessorGeneratedUCBAction
              hK sigma2 T delta defaultAction reward)
            reward
            (measurable_selectedPolicySuccessorGeneratedUCBAction
              hK sigma2 T delta defaultAction reward
              (fun t => measurable_pi_apply t))
            (fun t => measurable_pi_apply t)).le i))) := by
  dsimp only
  let source :=
    selectedPolicySuccessorGeneratedUCBSelectedRewardLawSource_trajMeasure
      hK mu0 rewardKernel context hcontext sigma2 T delta defaultAction
  have hlaw := source.reward_map_eq_selected_policy_finitePairHistory i
  simpa [source, selectedPolicySuccessorGeneratedUCBAction,
    History.pairHistoryRewardProjection_finitePairHistoryOfTrace] using hlaw

/--
Canonical reward-only trajectory specialization of the practical textbook UCB
pseudo-regret theorem. The selected-reward law is produced internally; the
pointwise raw-range premise is retained explicitly.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K)
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall trajectory : RewardTrace Rat,
      Set.Icc (rewardLo i) (rewardHi i)
        (((trajectory (i + 1) : Rat) : Real)))
    (hmean_range : forall i : Nat, forall c : Context, forall arm : Fin K,
      Set.Icc (meanLo i) (meanHi i) (((mean c arm : Rat) : Real)))
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm) :
    ∫⁻ trajectory : RewardTrace Rat,
        ENNReal.ofReal
          (((pseudoRegret model
            (selectedPolicySuccessorGeneratedUCBRegretAction
              model.hK sigma2 T delta defaultAction
              (fun y : RewardTrace Rat => y) trajectory)
            T : Rat) : Real))
      ∂(selectedPolicySuccessorRewardTrajMeasure
        model.hK mu0 rewardKernel context hcontext sigma2 T delta
          defaultAction) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          ENNReal.ofReal
              (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
                (((model.gap arm : Rat) : Real))) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  apply
    lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_of_reward_map_eq_selected_policy
      (mu := selectedPolicySuccessorRewardTrajMeasure
        model.hK mu0 rewardKernel context hcontext sigma2 T delta
          defaultAction)
      (model := model)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
      (rewardLo := rewardLo)
      (rewardHi := rewardHi)
      (meanLo := meanLo)
      (meanHi := meanHi)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmean)
      (hkernel := hkernel)
      (hraw := hraw)
      (hmean_range := hmean_range)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy :=
        selectedPolicySuccessorGeneratedUCB_reward_map_eq_selected_policy_trajMeasure
          model.hK mu0 rewardKernel context hcontext sigma2 T delta
            defaultAction)

end UCB
end BanditRLProof
