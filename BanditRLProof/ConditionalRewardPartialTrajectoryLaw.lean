import BanditRLProof.ConditionalRewardLawSource

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace ConditionalExpectationReward

/--
An ambient reward process satisfying the configured initial law and successor
conditional-distribution recursion has the generated finite-pair
`partialTraj` law on the generated history filtration.

Unlike the unrestricted theorem card, the action trace here is the policy
action generated from the reward history, and the model-side trajectory law is
supplied by `hzero` and `hcond` rather than assumed through the conclusion.
-/
theorem historyStepKernelFamily_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_condDistrib
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action] [Nonempty Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu = mu0)
    (hcond : forall i : Nat,
      Filter.EventuallyEq
        (ae (mu.map (fun omega : Omega =>
          Preorder.frestrictLe i (reward omega))))
        (ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega => Preorder.frestrictLe i (reward omega))
          mu)
        (RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate i))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (generatedActionFromRewardHistory policy state defaultAction
                reward y)
              (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (generatedActionFromRewardHistory policy state defaultAction
              reward omega)
            (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc
            (generatedActionFromRewardHistory policy state defaultAction
              reward)
            reward
            (generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward hstate)
            hreward).le i))) := by
  let source :=
    historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_of_condDistrib
      mu mu0 rewardKernel policy context state hcontext hstate defaultAction
        reward hreward hzero hcond
  simpa only using source.partialtraj_map_eq i

/--
An arbitrary measurable action/reward process has the full finite-pair
`partialTraj` law at time `i` when its successor pair regular conditional
distribution given the observed finite pair prefix is the configured
history-step action/reward kernel.

This is the unrestricted-action theorem-card route under a genuine upstream
pair `condDistrib` law. It needs neither a generated-action equality nor a
complete trajectory-law assumption.
-/
theorem actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_pair_condDistrib
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    [Nonempty Omega] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (hcond :
      Filter.EventuallyEq
        (ae (mu.map (fun omega : Omega =>
          History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)))
        (ProbabilityTheory.condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i)) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc (mOmega := mOmega)
              action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc (mOmega := mOmega)
            action reward haction hreward).le i))) := by
  let pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat) :=
    fun omega =>
      History.finitePairHistoryOfTrace (action omega) (reward omega) i
  let nextPair : Omega -> Prod Action Rat :=
    fun omega => (action omega (i + 1), reward omega (i + 1))
  let pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context :=
    fun n history =>
      context n (History.pairHistoryRewardProjection history)
  let pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State :=
    fun n history =>
      state n (History.pairHistoryRewardProjection history)
  let hpairContext : forall n : Nat, Measurable (pairContext n) := fun n =>
    (hcontext n).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Action) (Reward := Rat) n)
  let hpairState : forall n : Nat, Measurable (pairState n) := fun n =>
    (hstate n).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Action) (Reward := Rat) n)
  have h_pairHistory : Measurable pairHistory := by
    exact History.measurable_finitePairHistoryOfTrace
      action reward haction hreward i
  have h_nextPair : Measurable nextPair := by
    exact (haction (i + 1)).prod (hreward (i + 1))
  have h_pair_map_comap :=
    condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim
      (mu := mu)
      (X := nextPair)
      (Y := pairHistory)
      h_nextPair h_pairHistory
      (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState i)
      (by simpa [nextPair, pairHistory, pairContext, pairState,
          hpairContext, hpairState] using hcond)
  let mHist : MeasurableSpace Omega :=
    (History.historyFiltrationSucc (mOmega := mOmega)
      action reward haction hreward) i
  let mComap : MeasurableSpace Omega :=
    (inferInstance :
      MeasurableSpace ((j : Finset.Iic i) -> Prod Action Rat)).comap
        pairHistory
  have hfiltration : mHist = mComap := by
    simpa [mHist, mComap, pairHistory] using
      (History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace
        (mOmega := mOmega) action reward haction hreward i)
  have hhist_le : mHist <= mOmega := by
    dsimp [mHist]
    exact
      ((History.historyFiltrationSucc (mOmega := mOmega)
        action reward haction hreward).le i)
  have hcomap_le : mComap <= mOmega := by
    simpa [mComap] using h_pairHistory.comap_le
  let pairMapLaw : MeasurableSpace Omega -> Omega -> Prop :=
    fun m omega =>
      @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          nextPair
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ m omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (pairHistory omega)
  let mHistWithLe : {m : MeasurableSpace Omega // m <= mOmega} :=
    ⟨mHist, hhist_le⟩
  let mComapWithLe : {m : MeasurableSpace Omega // m <= mOmega} :=
    ⟨mComap, hcomap_le⟩
  let pairMapEvent : {m : MeasurableSpace Omega // m <= mOmega} -> Prop :=
    fun m => Filter.Eventually (pairMapLaw m.1)
      (ae (mu.trim m.2))
  have h_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            nextPair
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc (mOmega := mOmega)
                action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc (mOmega := mOmega)
              action reward haction hreward).le i))) := by
    have h_pair_map_mComap : pairMapEvent mComapWithLe := by
      simpa [pairMapEvent, mComapWithLe, pairMapLaw, mComap] using
        h_pair_map_comap
    have hm_eq : mHistWithLe = mComapWithLe := by
      apply Subtype.ext
      exact hfiltration
    have h_pair_map_mHist : pairMapEvent mHistWithLe := by
      exact hm_eq.symm ▸ h_pair_map_mComap
    simpa [pairMapLaw, mHist] using h_pair_map_mHist
  have h_extend_map_eq :=
    actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      (by simpa [nextPair, pairHistory, pairContext, pairState,
          hpairContext, hpairState] using h_pair_map_eq)
  exact
    actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_extend_map_eq

/--
The zero-initialized successor centered-reward process is strongly adapted to
the full action/reward history filtration for any measurable action trace.
-/
theorem centeredRewardSuccProcess_stronglyAdapted_historyFiltrationSucc
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    let F := History.historyFiltrationSucc action reward haction hreward
    let Y : Nat -> Omega -> Real := fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))
    StronglyAdapted F Y := by
  let F := History.historyFiltrationSucc action reward haction hreward
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))
  change StronglyAdapted F Y
  intro t
  cases t with
  | zero =>
      have hzero :
          @Measurable Omega Real (F 0) inferInstance
            (fun _omega : Omega => (0 : Real)) := measurable_const
      simpa [Y] using hzero.stronglyMeasurable
  | succ i =>
      have hreward_succ :
          @Measurable Omega Rat (F (i + 1)) inferInstance
            (fun omega : Omega => reward omega (i + 1)) := by
        simpa [F, History.historyFiltrationSucc_apply] using
          (History.measurable_reward_mem_historyFiltration_of_lt
            (mOmega := mOmega) action reward haction hreward
            (Nat.lt_succ_self (i + 1)))
      have hhistory :
          @Measurable Omega ((j : Finset.Iic i) -> Rat)
            (F (i + 1)) inferInstance
            (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i) := by
        letI : MeasurableSpace Omega := F (i + 1)
        change Measurable
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
        refine measurable_pi_lambda _ ?_
        intro j
        change Measurable (fun omega : Omega => reward omega j.1)
        change @Measurable Omega Rat (F (i + 1)) inferInstance
          (fun omega : Omega => reward omega j.1)
        simpa [F, History.historyFiltrationSucc_apply] using
          (History.measurable_reward_mem_historyFiltration_of_lt
            (mOmega := mOmega) action reward haction hreward
            (Nat.lt_succ_of_le
              (Nat.le_trans (Finset.mem_Iic.mp j.2) (Nat.le_succ i))))
      have hcontext_history :
          @Measurable Omega Context (F (i + 1)) inferInstance
            (fun omega : Omega =>
              context i
                (History.finiteRewardHistoryOfTrace (reward omega) i)) :=
        (hcontext i).comp hhistory
      have hstate_history :
          @Measurable Omega State (F (i + 1)) inferInstance
            (fun omega : Omega =>
              state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)) :=
        (hstate i).comp hhistory
      have hselected_action :
          @Measurable Omega Action (F (i + 1)) inferInstance
            (fun omega : Omega =>
              (policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :=
        (policy i).measurable_action.comp hstate_history
      have hselected_mean :
          @Measurable Omega Rat (F (i + 1)) inferInstance
            (fun omega : Omega =>
              mean
                (context i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))
                ((policy i).action
                  (state i
                    (History.finiteRewardHistoryOfTrace (reward omega) i)))) :=
        hmean.comp (hcontext_history.prodMk hselected_action)
      have hreward_real :
          @Measurable Omega Real (F (i + 1)) inferInstance
            (fun omega : Omega => ((reward omega (i + 1) : Rat) : Real)) :=
        (measurable_of_countable (fun value : Rat => ((value : Rat) : Real))).comp
          hreward_succ
      have hmean_real :
          @Measurable Omega Real (F (i + 1)) inferInstance
            (fun omega : Omega =>
              ((mean
                (context i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))
                ((policy i).action
                  (state i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real)) :=
        (measurable_of_countable (fun value : Rat => ((value : Rat) : Real))).comp
          hselected_mean
      have hcentered := hreward_real.sub hmean_real
      simpa [Y, Rat.cast_sub] using hcentered.stronglyMeasurable

/--
An explicit successor-pair conditional distribution and the native
trimmed-a.e. selected-variance bound yield the centered-reward conditional MGF
witness for an arbitrary measurable action trace.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_of_pair_condDistrib_of_ae_variance
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    [Nonempty Omega] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) (c : NNReal)
    (hvariance :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <= c)
        (ae (mu.trim
          ((History.historyFiltrationSucc (mOmega := mOmega)
            action reward haction hreward).le i))))
    (hcond :
      Filter.EventuallyEq
        (ae (mu.map (fun omega : Omega =>
          History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)))
        (ProbabilityTheory.condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i)) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc (mOmega := mOmega)
        action reward haction hreward) i)
      ((History.historyFiltrationSucc (mOmega := mOmega)
        action reward haction hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  let pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context :=
    fun n history => context n (History.pairHistoryRewardProjection history)
  let pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State :=
    fun n history => state n (History.pairHistoryRewardProjection history)
  let hpairContext : forall n : Nat, Measurable (pairContext n) := fun n =>
    (hcontext n).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Action) (Reward := Rat) n)
  let hpairState : forall n : Nat, Measurable (pairState n) := fun n =>
    (hstate n).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Action) (Reward := Rat) n)
  have hfull :=
    actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_pair_condDistrib
      (mOmega := mOmega) mu action rewardKernel policy context state hcontext
        hstate reward haction hreward i hcond
  have hpair :=
    actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega) (mu := mu) (action := action)
      (rewardKernel := rewardKernel) (policy := policy) (context := context)
      (state := state) (hcontext := hcontext) (hstate := hstate)
      (reward := reward) (haction := haction) (hreward := hreward)
      (i := i) hfull
  have hhistory : Measurable
      (fun omega : Omega =>
        History.finiteRewardHistoryOfTrace (reward omega) i) :=
    History.measurable_finiteRewardHistoryOfTrace reward hreward i
  have hcontext_omega := (hcontext i).comp hhistory
  have hstate_omega := (hstate i).comp hhistory
  have hselected_action := (policy i).measurable_action.comp hstate_omega
  have hselected_mean := hmean.comp (hcontext_omega.prodMk hselected_action)
  have hreward_real : Measurable
      (fun omega : Omega => ((reward omega (i + 1) : Rat) : Real)) :=
    (measurable_of_countable (fun value : Rat => ((value : Rat) : Real))).comp
      (hreward (i + 1))
  have hmean_real : Measurable
      (fun omega : Omega =>
        ((mean
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace (reward omega) i))) : Rat) :
          Real)) :=
    (measurable_of_countable (fun value : Rat => ((value : Rat) : Real))).comp
      hselected_mean
  have hcentered : Measurable
      (fun omega : Omega =>
        ((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) : Rat) :
          Real)) := by
    simpa [Rat.cast_sub] using hreward_real.sub hmean_real
  have hrewardMap :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc (mOmega := mOmega)
                action reward haction hreward) i) omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae (mu.trim
          ((History.historyFiltrationSucc (mOmega := mOmega)
            action reward haction hreward).le i))) := by
    filter_upwards [hpair] with omega hpair_eq
    let condKernel : Measure Omega :=
      @ProbabilityTheory.condExpKernel Omega mOmega _ mu _
        ((History.historyFiltrationSucc (mOmega := mOmega)
          action reward haction hreward) i) omega
    let nextPair : Omega -> Prod Action Rat :=
      fun y => (action y (i + 1), reward y (i + 1))
    have hnextPair : Measurable nextPair :=
      (haction (i + 1)).prod (hreward (i + 1))
    have hleft :
        Measure.map Prod.snd (Measure.map nextPair condKernel) =
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1)) condKernel := by
      rw [Measure.map_map measurable_snd hnextPair]
      rfl
    have hstep :=
      RewardKernel.actionRewardHistoryStepKernelFamily_reward_map
        rewardKernel policy pairContext pairState hpairContext hpairState i
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) i)
    calc
      @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1)) condKernel =
        Measure.map Prod.snd (Measure.map nextPair condKernel) := hleft.symm
      _ = Measure.map Prod.snd
          (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)) := by
        rw [hpair_eq]
      _ = RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate i
          (History.finiteRewardHistoryOfTrace (reward omega) i) := by
        simpa [pairContext, pairState,
          History.pairHistoryRewardProjection_finitePairHistoryOfTrace,
          RewardKernel.historyStepKernelFamily_apply] using hstep
  exact
    centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
      (mOmega := mOmega) (mu := mu) (action := action)
      (rewardKernel := rewardKernel) (policy := policy) (context := context)
      (state := state) (hcontext := hcontext) (hstate := hstate)
      (mean := mean) (varianceProxy := varianceProxy) (law := law)
      (reward := reward) (haction := haction) (hreward := hreward)
      (i := i) (c := c) hcentered hrewardMap hvariance

/--
Compatibility wrapper for a pointwise selected-history variance ceiling.

The core pair-conditional-law transfer only needs the corresponding
trimmed-a.e. variance event.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_of_pair_condDistrib
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    [Nonempty Omega] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) (c : NNReal)
    (hvariance : forall history : ((j : Finset.Iic i) -> Rat),
      varianceProxy (context i history)
        ((policy i).action (state i history)) <= c)
    (hcond :
      Filter.EventuallyEq
        (ae (mu.map (fun omega : Omega =>
          History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)))
        (ProbabilityTheory.condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i)) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc (mOmega := mOmega)
        action reward haction hreward) i)
      ((History.historyFiltrationSucc (mOmega := mOmega)
        action reward haction hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  apply
    centeredReward_succ_hasCondSubgaussianMGF_of_pair_condDistrib_of_ae_variance
      (mOmega := mOmega) (mu := mu) (action := action)
      (rewardKernel := rewardKernel) (policy := policy) (context := context)
      (state := state) (hcontext := hcontext) (hstate := hstate)
      (mean := mean) (varianceProxy := varianceProxy) (law := law)
      (hmean := hmean) (reward := reward) (haction := haction)
      (hreward := hreward) (i := i) (c := c) ?_ hcond
  exact Filter.Eventually.of_forall (fun omega =>
    hvariance (History.finiteRewardHistoryOfTrace (reward omega) i))

/--
Azuma-Hoeffding upper tail for an arbitrary measurable action/reward process
whose every successor-pair conditional law is the configured history-step
kernel.
-/
theorem actionRewardHistoryStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_pair_condDistrib
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    [Nonempty Omega] [Nonempty Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hcondLaw : forall i : Nat,
      Filter.EventuallyEq
        (ae (mu.map (fun omega : Omega =>
          History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)))
        (ProbabilityTheory.condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i))
    (varianceCeiling : Nat -> NNReal)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (n : Nat) {eps : Real} (heps : 0 <= eps) :
    let Y : Nat -> Omega -> Real := fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))
    let cY : Nat -> NNReal := fun t =>
      match t with
      | 0 => 0
      | i + 1 => varianceCeiling i
    mu {omega | eps <= (Finset.range n).sum (fun t => Y t omega)} <=
      ENNReal.ofReal
        (Real.exp
          (-eps ^ 2 /
            (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  let F := History.historyFiltrationSucc action reward haction hreward
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | i + 1 => varianceCeiling i
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (centeredRewardSuccProcess_stronglyAdapted_historyFiltrationSucc
        (mOmega := mOmega) action policy context state hcontext hstate mean
        hmean reward haction hreward)
  have hzeroMGF :
      ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu := by
    simp [Y, cY]
  have hcondMGF : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu := by
    intro i _hi
    have hmgf :=
      centeredReward_succ_hasCondSubgaussianMGF_of_pair_condDistrib
        (mOmega := mOmega) mu action rewardKernel policy context state hcontext
          hstate mean varianceProxy law hmean reward haction hreward i
          (varianceCeiling i) (hvariance i) (hcondLaw i)
    simpa [F, Y, cY] using hmgf
  have htail :=
    Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
      (mu := mu) (Y := Y) (cY := cY) (F := F)
      hadapted hzeroMGF n hcondMGF heps
  simpa [F, Y, cY] using htail

/--
Finite-horizon Azuma-Hoeffding upper tail for an arbitrary measurable
action/reward process.

Only successor-pair laws and trimmed-a.e. selected-variance bounds at indices
`i < n - 1` are required.  This is the native contract consumed by the
finite-sum conditional sub-Gaussian assembler.
-/
theorem actionRewardHistoryStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_pair_condDistrib_on_horizon
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    [Nonempty Omega] [Nonempty Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (n : Nat)
    (hcondLaw : forall i : Nat, i < n - 1 ->
      Filter.EventuallyEq
        (ae (mu.map (fun omega : Omega =>
          History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)))
        (ProbabilityTheory.condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i))
    (varianceCeiling : Nat -> NNReal)
    (hvariance : forall i : Nat, i < n - 1 ->
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            varianceCeiling i)
        (ae (mu.trim
          ((History.historyFiltrationSucc (mOmega := mOmega)
            action reward haction hreward).le i))))
    {eps : Real} (heps : 0 <= eps) :
    let Y : Nat -> Omega -> Real := fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))
    let cY : Nat -> NNReal := fun t =>
      match t with
      | 0 => 0
      | i + 1 => varianceCeiling i
    mu {omega | eps <= (Finset.range n).sum (fun t => Y t omega)} <=
      ENNReal.ofReal
        (Real.exp
          (-eps ^ 2 /
            (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  let F := History.historyFiltrationSucc action reward haction hreward
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | i + 1 => varianceCeiling i
  have hadapted : StronglyAdapted F Y := by
    simpa [F, Y] using
      (centeredRewardSuccProcess_stronglyAdapted_historyFiltrationSucc
        (mOmega := mOmega) action policy context state hcontext hstate mean
        hmean reward haction hreward)
  have hzeroMGF :
      ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu := by
    simp [Y, cY]
  have hcondMGF : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu := by
    intro i hi
    have hmgf :=
      centeredReward_succ_hasCondSubgaussianMGF_of_pair_condDistrib_of_ae_variance
        (mOmega := mOmega) mu action rewardKernel policy context state hcontext
          hstate mean varianceProxy law hmean reward haction hreward i
          (varianceCeiling i) (hvariance i hi) (hcondLaw i hi)
    simpa [F, Y, cY] using hmgf
  have htail :=
    Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
      (mu := mu) (Y := Y) (cY := cY) (F := F)
      hadapted hzeroMGF n hcondMGF heps
  simpa [F, Y, cY] using htail

/--
Canonical action/reward `trajMeasure` Azuma-Hoeffding upper tail.

The Mathlib Ionescu--Tulcea trajectory law supplies every successor-pair
conditional distribution.  The caller only provides the centered reward
kernel law and horizon-local selected-history variance ceilings.
-/
theorem actionRewardHistoryStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure_on_horizon
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action] [Nonempty Action]
    (mu0 : Measure (Prod Action Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (n : Nat)
    (varianceCeiling : Nat -> NNReal)
    (hvariance : forall i : Nat, i < n - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    {eps : Real} (heps : 0 <= eps) :
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod Action Rat) -> Context :=
      fun i history =>
        context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod Action Rat) -> State :=
      fun i history =>
        state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (hstate i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) i)
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState
    let mu :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod Action Rat) mu0 stepKernel
    let reward : (Nat -> Prod Action Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let Y : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 =>
          (((reward trajectory (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace
                  (reward trajectory) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))) : Rat) : Real))
    let cY : Nat -> NNReal := fun t =>
      match t with
      | 0 => 0
      | i + 1 => varianceCeiling i
    mu {trajectory | eps <= (Finset.range n).sum (fun t => Y t trajectory)} <=
      ENNReal.ofReal
        (Real.exp
          (-eps ^ 2 /
            (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod Action Rat) -> Context :=
    fun i history =>
      context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod Action Rat) -> State :=
    fun i history =>
      state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Action) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (hstate i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Action) (Reward := Rat) i)
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      pairContext pairState hpairContext hpairState
  let mu :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod Action Rat) mu0 stepKernel
  let action : (Nat -> Prod Action Rat) -> ActionTrace Action :=
    fun trajectory t => (trajectory t).1
  let reward : (Nat -> Prod Action Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  have haction : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod Action Rat =>
        action trajectory t) := fun t =>
    measurable_fst.comp (measurable_pi_apply t)
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod Action Rat =>
        reward trajectory t) := fun t =>
    measurable_snd.comp (measurable_pi_apply t)
  apply
    actionRewardHistoryStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_pair_condDistrib_on_horizon
      (mu := mu) (action := action) (rewardKernel := rewardKernel)
      (policy := policy) (context := context) (state := state)
      (hcontext := hcontext) (hstate := hstate) (mean := mean)
      (varianceProxy := varianceProxy) (law := law) (hmean := hmean)
      (reward := reward) (haction := haction) (hreward := hreward)
      (n := n) ?_ varianceCeiling ?_ heps
  · intro i _hi
    have hcanonical :=
      RewardKernel.actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    simpa [mu, stepKernel, action, reward, pairContext, pairState,
      hpairContext, hpairState, History.finitePairHistoryOfTrace] using
        hcanonical
  · intro i hi
    exact Filter.Eventually.of_forall (fun trajectory =>
      hvariance i hi
        (History.finiteRewardHistoryOfTrace (reward trajectory) i))

end ConditionalExpectationReward
end BanditRLProof
