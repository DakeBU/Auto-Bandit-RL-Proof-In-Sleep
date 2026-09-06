import BanditRLProof.Algorithms.UCBConditionalRewardLawTrajMeasure

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace ConditionalExpectationReward

/--
Direct selected-law conditional-MGF bridge for a centered reward kernel.

Unlike the older raw-range source route, this theorem consumes the
`CenteredRewardKernelLaw` MGF field directly. No pointwise or almost-everywhere
reward-range hypothesis is needed.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_centeredKernel_of_variance_le
    {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (state : (n : Nat) -> History.FiniteRewardHistory Rat n -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Context × Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward).le i))))
    (i : Nat) (c : NNReal)
    (hvariance : forall history : History.FiniteRewardHistory Rat i,
      varianceProxy (context i history) ((policy i).action (state i history)) <= c) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state) (defaultAction := defaultAction)
          (reward := reward) hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state) (defaultAction := defaultAction)
          (reward := reward) hreward hstate)
        hreward).le i)
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
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t) :=
    generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward hstate
  let F := History.historyFiltrationSucc action reward haction hreward
  let X : Omega -> Real := fun omega =>
    (((reward omega (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward omega) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward omega) i))) :
      Rat) : Real))
  have hstrong :=
    generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (hmean := hmean)
      (defaultAction := defaultAction)
      (reward := reward)
      (hreward := hreward)
  have hcentered : Measurable X := by
    have hs := hstrong (i + 1)
    have hs' := hs.mono (F.le (i + 1))
    simpa [action, F, X] using hs'.measurable
  have hmap :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
                omega) =
            RewardKernel.historyStepKernelFamily rewardKernel policy context
              state hcontext hstate i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae (mu.trim (F.le i))) := by
    filter_upwards [h_reward_map_eq_policy i] with omega homega
    simpa [action, F, RewardKernel.historyStepKernelFamily_apply] using homega
  have hvariance' :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <= c)
        (ae (mu.trim (F.le i))) := by
    exact Filter.Eventually.of_forall (fun omega =>
      hvariance (History.finiteRewardHistoryOfTrace (reward omega) i))
  simpa [action, F, X] using
    centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := hkernel)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      (c := c)
      hcentered hmap hvariance'

/--
Predictable-variance two-sided tail for one arm, obtained directly from the
centered-kernel conditional MGF. The selected arm is charged `sigma2` only at
successor times when it is pulled.
-/
theorem armMaskedCenteredRewardSuccProcess_sum_abs_tail_predictableVariance_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (state : (n : Nat) -> History.FiniteRewardHistory Rat n -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction arm : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Context × Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward).le i))))
    (n : Nat) (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let action :=
      generatedActionFromRewardHistory policy state defaultAction reward
    let X : Nat -> Omega -> Real := fun i omega =>
      (((reward omega (i + 1) -
        mean
          (context i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace (reward omega) i))) :
        Rat) : Real))
    let Y : Nat -> Omega -> Real := fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          {omega : Omega |
            action omega (i + 1) = arm}.indicator (X i) omega
    let V : Nat -> Omega -> Real := fun t omega =>
      match t with
      | 0 => 0
      | i + 1 =>
          {omega : Omega | action omega (i + 1) = arm}.indicator
            (fun _ => (((sigma2 : NNReal) : Real))) omega
    mu {omega |
        Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => Y t omega)| ∧
        (Finset.range n).sum (fun t => V t omega) <= varianceBudget} <=
      ENNReal.ofReal delta := by
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t) :=
    generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward hstate
  let F := History.historyFiltrationSucc action reward haction hreward
  let X : Nat -> Omega -> Real := fun i omega =>
    (((reward omega (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward omega) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward omega) i))) :
      Rat) : Real))
  let s : Nat -> Set Omega := fun i =>
    {omega : Omega | action omega (i + 1) = arm}
  let c : Nat -> NNReal := fun _ => sigma2
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 => (s i).indicator (X i) omega
  let V : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (s i).indicator (fun _ => (((sigma2 : NNReal) : Real))) omega
  have hs : forall i, @MeasurableSet Omega (F i) (s i) := by
    intro i
    have hpredict :
        @Measurable Omega Action (F i) inferInstance
          (fun omega : Omega => action omega (i + 1)) := by
      simpa [F, action] using
        (generatedActionFromRewardHistory_succ_measurable_historyFiltrationSucc
          (mOmega := mOmega) policy state hstate defaultAction reward hreward i)
    simpa [s, Set.preimage] using hpredict (MeasurableSet.singleton arm)
  have hY : StronglyAdapted F Y := by
    simpa [F, Y, X, s, action] using
      (generatedActionFromRewardHistory_armMaskedCenteredRewardSuccProcess_stronglyAdapted
        (policy := policy)
        (context := context)
        (state := state)
        (hcontext := hcontext)
        (hstate := hstate)
        (mean := mean)
        (hmean := hmean)
        (defaultAction := defaultAction)
        (arm := arm)
        (reward := reward)
        (hreward := hreward))
  have hV : StronglyAdapted F V := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ i =>
        have hsi : @MeasurableSet Omega (F (i + 1)) (s i) :=
          (F.mono (Nat.le_succ i)) _ (hs i)
        simpa [V] using
          (MeasureTheory.stronglyMeasurable_const.indicator hsi)
  have hsubG : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (X i) (c i) mu := by
    intro i _hi
    have hmgf :=
      centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_centeredKernel_of_variance_le
        (mu := mu)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (reward := reward)
        (hreward := hreward)
        (hcontext := hcontext)
        (hstate := hstate)
        (hmean := hmean)
        (hkernel := hkernel)
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        (i := i)
        (c := sigma2)
        (hvariance i)
    simpa [action, F, X, c] using hmgf
  have htail :=
    Concentration.condSubGaussian_indicator_sum_abs_tail_predictableVariance_delta
      F X c s hY hV hs n hsubG varianceBudget delta
        hvarianceBudget hdelta
  simpa [action, F, X, c, s, Y, V] using htail

/-- Exact positive pull-count confidence using the centered-kernel route. -/
theorem successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action] [DecidableEq Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (state : (n : Nat) -> History.FiniteRewardHistory Rat n -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction arm : Action)
    (armMean : Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Context × Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        mean (context i history) arm = armMean)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward).le i))))
    (n k : Nat) (hk : 0 < k)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) :
    let action :=
      generatedActionFromRewardHistory policy state defaultAction reward
    let count : Omega -> Nat := fun omega =>
      successorArmPullCount (action omega) arm n
    mu {omega |
        count omega = k ∧
          successorArmEmpiricalMeanExactCountRadius sigma2 k delta <=
            |successorArmEmpiricalMean (action omega) (reward omega) arm n -
              (armMean : Real)|} <=
      ENNReal.ofReal delta := by
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  let X : Nat -> Omega -> Real := fun i omega =>
    (((reward omega (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward omega) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward omega) i))) :
      Rat) : Real))
  let s : Nat -> Set Omega := fun i =>
    {omega : Omega | action omega (i + 1) = arm}
  let Y : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 => (s i).indicator (X i) omega
  let V : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        (s i).indicator (fun _ => (((sigma2 : NNReal) : Real))) omega
  let count : Omega -> Nat := fun omega =>
    successorArmPullCount (action omega) arm n
  let varianceBudget : Real := (((sigma2 : NNReal) : Real)) * (k : Real)
  have hvarianceBudget : 0 < varianceBudget := by
    exact mul_pos hsigma2 (by exact_mod_cast hk)
  have htail :
      mu {omega |
          Concentration.subGaussianPredictableVarianceRadius
              varianceBudget delta <=
            |(Finset.range n).sum (fun t => Y t omega)| ∧
          (Finset.range n).sum (fun t => V t omega) <= varianceBudget} <=
        ENNReal.ofReal delta := by
    simpa [action, X, s, Y, V, varianceBudget] using
      (armMaskedCenteredRewardSuccProcess_sum_abs_tail_predictableVariance_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
        (mu := mu)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (arm := arm)
        (reward := reward)
        (hreward := hreward)
        (sigma2 := sigma2)
        (hcontext := hcontext)
        (hstate := hstate)
        (hmean := hmean)
        (hkernel := hkernel)
        (hvariance := hvariance)
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        (n := n)
        (varianceBudget := varianceBudget)
        (delta := delta)
        hvarianceBudget hdelta)
  refine (measure_mono ?_).trans htail
  intro omega homega
  rcases homega with ⟨hcount, hbad⟩
  have hcountLocal : count omega = k := by
    simpa [count, action] using hcount
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hkNe : (k : Real) ≠ 0 := ne_of_gt hkReal
  have hcenterOmega : forall i : Nat,
      action omega (i + 1) = arm ->
        mean
          (context i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace (reward omega) i))) =
          armMean := by
    intro i hselected
    have hselected' :
        (policy i).action
          (state i (History.finiteRewardHistoryOfTrace (reward omega) i)) =
            arm := by
      simpa [action, generatedActionFromRewardHistory,
        Policy.generatedActionTraceSucc] using hselected
    simpa [hselected'] using
      (harmMean i (History.finiteRewardHistoryOfTrace (reward omega) i))
  have hsum :
      (Finset.range n).sum (fun t => Y t omega) =
        successorArmRewardSum (action omega) (reward omega) arm n -
          (count omega : Real) * (armMean : Real) := by
    simpa [Y, X, s, Set.indicator, count] using
      (armMaskedCenteredRewardSuccProcess_sum_eq_successorArmRewardSum_sub_pullCount_mul
        (action omega) (reward omega)
        (fun i =>
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        arm armMean hcenterOmega n)
  have haverage :
      (Finset.range n).sum (fun t => Y t omega) / (k : Real) =
        successorArmEmpiricalMean (action omega) (reward omega) arm n -
          (armMean : Real) := by
    rw [hsum, hcountLocal]
    simp only [successorArmEmpiricalMean]
    rw [show successorArmPullCount (action omega) arm n = k by
      simpa [count] using hcountLocal]
    field_simp [hkNe]
  have hsumBad :
      Concentration.subGaussianPredictableVarianceRadius
          varianceBudget delta <=
        |(Finset.range n).sum (fun t => Y t omega)| := by
    change
      Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta / (k : Real) <=
        |successorArmEmpiricalMean (action omega) (reward omega) arm n -
          (armMean : Real)| at hbad
    rw [← haverage, abs_div, abs_of_pos hkReal] at hbad
    exact (div_le_div_iff_of_pos_right hkReal).mp hbad
  have hvarianceSum :
      (Finset.range n).sum (fun t => V t omega) = varianceBudget := by
    have hidentity :=
      armMaskedVarianceSuccProcess_sum_eq_mul_successorArmPullCount
        (action omega) arm sigma2 n
    rw [show successorArmPullCount (action omega) arm n = k by
      simpa [count] using hcountLocal] at hidentity
    simpa [V, s, Set.indicator, varianceBudget] using hidentity
  exact ⟨hsumBad, hvarianceSum.le⟩

/-- Positive random pull-count confidence via finite exact-count peeling. -/
theorem successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action] [DecidableEq Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (state : (n : Nat) -> History.FiniteRewardHistory Rat n -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction arm : Action)
    (armMean : Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Context × Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        mean (context i history) arm = armMean)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward).le i))))
    (n : Nat) (hn : 0 < n)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) :
    let action :=
      generatedActionFromRewardHistory policy state defaultAction reward
    let count : Omega -> Nat := fun omega =>
      successorArmPullCount (action omega) arm n
    mu {omega |
        0 < count omega ∧
          successorArmEmpiricalMeanPeelingRadius sigma2 (count omega) n delta <=
            |successorArmEmpiricalMean (action omega) (reward omega) arm n -
              (armMean : Real)|} <=
      ENNReal.ofReal delta := by
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  let count : Omega -> Nat := fun omega =>
    successorArmPullCount (action omega) arm n
  let bad : Nat -> Set Omega := fun k =>
    {omega |
      successorArmEmpiricalMeanPeelingRadius sigma2 k n delta <=
        |successorArmEmpiricalMean (action omega) (reward omega) arm n -
          (armMean : Real)|}
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hdeltaShare : 0 < delta / (n : Real) := div_pos hdelta hnReal
  have hcount_le : forall omega, count omega <= n := by
    intro omega
    exact successorArmPullCount_le_horizon (action omega) arm n
  have hfiber : forall k, 0 < k -> k <= n ->
      mu {omega | count omega = k ∧ omega ∈ bad k} <=
        ENNReal.ofReal (delta / (n : Real)) := by
    intro k hk _hk_le
    simpa [action, count, bad, successorArmEmpiricalMeanPeelingRadius] using
      (successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
        (mu := mu)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (arm := arm)
        (armMean := armMean)
        (reward := reward)
        (hreward := hreward)
        (sigma2 := sigma2)
        (hcontext := hcontext)
        (hstate := hstate)
        (hmean := hmean)
        (hkernel := hkernel)
        (hvariance := hvariance)
        (harmMean := harmMean)
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        (n := n) (k := k) hk hsigma2
        (delta / (n : Real)) hdeltaShare)
  simpa [action, count, bad] using
    (Concentration.measure_positive_randomCount_event_le_of_exactCount_uniform
      mu count n bad hcount_le hn delta hdelta hfiber)

/--
Finite-arm, finite-time empirical-mean confidence from the centered-kernel
selected-law route. This is fixed-horizon and union-bounded, not anytime.
-/
theorem successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action] [DecidableEq Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (state : (n : Nat) -> History.FiniteRewardHistory Rat n -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (arms : Finset Action) (harms : arms.Nonempty)
    (armMean : Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Context × Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm, arm ∈ arms ->
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward).le i))))
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) :
    let action :=
      generatedActionFromRewardHistory policy state defaultAction reward
    mu (successorArmEmpiricalMeanFiniteArmTimeBadEvent action reward arms
      armMean sigma2 T delta) <= ENNReal.ofReal delta := by
  classical
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  let family := arms.product (Finset.range T)
  let deltaShare :=
    successorArmEmpiricalMeanFiniteArmTimeConfidenceShare arms T delta
  let bad : Action × Nat -> Set Omega := fun pair =>
    {omega |
      0 < successorArmPullCount (action omega) pair.1 (pair.2 + 1) ∧
        successorArmEmpiricalMeanFiniteArmTimePeelingRadius sigma2
            (successorArmPullCount (action omega) pair.1 (pair.2 + 1))
            (pair.2 + 1) arms T delta <=
          |successorArmEmpiricalMean (action omega) (reward omega) pair.1
              (pair.2 + 1) - (armMean pair.1 : Real)|}
  have hfamily : family.Nonempty := by
    rcases harms with ⟨arm, harm⟩
    refine ⟨(arm, 0), ?_⟩
    exact Finset.mem_product.mpr
      ⟨harm, Finset.mem_range.mpr hT⟩
  have hfamilyCard : 0 < family.card := Finset.card_pos.mpr hfamily
  have hfamilyCardReal : 0 < (family.card : Real) :=
    Nat.cast_pos.mpr hfamilyCard
  have hdeltaShare : 0 < deltaShare := by
    simpa [deltaShare,
      successorArmEmpiricalMeanFiniteArmTimeConfidenceShare, family] using
      (div_pos hdelta hfamilyCardReal)
  have htail : forall pair, pair ∈ family ->
      mu (bad pair) <= ENNReal.ofReal (delta / (family.card : Real)) := by
    intro pair hpair
    have hpairMem := Finset.mem_product.mp hpair
    have hsingle :=
      successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
        (mu := mu)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (arm := pair.1)
        (armMean := armMean pair.1)
        (reward := reward)
        (hreward := hreward)
        (sigma2 := sigma2)
        (hcontext := hcontext)
        (hstate := hstate)
        (hmean := hmean)
        (hkernel := hkernel)
        (hvariance := hvariance)
        (harmMean := fun i history =>
          harmMean i history pair.1 hpairMem.1)
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        (n := pair.2 + 1) (Nat.succ_pos pair.2) hsigma2
        deltaShare hdeltaShare
    simpa [action, bad, family, deltaShare,
      successorArmEmpiricalMeanFiniteArmTimePeelingRadius,
      successorArmEmpiricalMeanFiniteArmTimeConfidenceShare] using hsingle
  simpa [action, family, bad,
    successorArmEmpiricalMeanFiniteArmTimeBadEvent] using
    (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
      mu family hfamily delta bad htail)

end ConditionalExpectationReward

namespace UCB

/--
Practical selected-policy UCB large-gap event bound using the centered-kernel
conditional-MGF route. No reward or mean range contract is exposed.
-/
theorem measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action] [DecidableEq Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (state : (n : Nat) -> History.FiniteRewardHistory Rat n -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (arms : Finset Action) (harms : arms.Nonempty)
    (armMean : Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Context × Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm, arm ∈ arms ->
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward hstate)
              hreward).le i))))
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (source : SelectedPolicySuccessorInitializedScoreMaxSource
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      reward arms armMean sigma2 T delta) :
    mu (selectedPolicySuccessorLargeGapEvent source) <=
      ENNReal.ofReal delta := by
  let action :=
    ConditionalExpectationReward.generatedActionFromRewardHistory
      policy state defaultAction reward
  have htail :=
    ConditionalExpectationReward.successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
      (mu := mu)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (arms := arms) harms
      (armMean := armMean)
      (reward := reward)
      (hreward := hreward)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hstate := hstate)
      (hmean := hmean)
      (hkernel := hkernel)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy := h_reward_map_eq_policy)
      T hT hsigma2 delta hdelta
  refine (measure_mono ?_).trans (by simpa [action] using htail)
  intro omega homega
  rcases homega with ⟨t, ht, hlarge⟩
  by_contra hgood
  have hgap := source.meanGap_le_two_radius_of_not_badEvent
    omega t ht hgood
  exact (not_lt_of_ge hgap) hlarge

/-- Exact selected-reward conditional-law contract for the generated UCB policy. -/
def SelectedPolicySuccessorRewardMapLaw
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal) (T : Nat) (delta : Real) : Prop :=
  forall i : Nat,
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc
                (selectedPolicySuccessorGeneratedUCBAction
                  hK sigma2 T delta defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := selectedPolicySuccessorHistoryPolicy
                    hK sigma2 T delta defaultAction)
                  (state := selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward
                  (measurable_selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction))
                hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc
            (selectedPolicySuccessorGeneratedUCBAction
              hK sigma2 T delta defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := selectedPolicySuccessorHistoryPolicy
                hK sigma2 T delta defaultAction)
              (state := selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction)
              (defaultAction := defaultAction) (reward := reward)
              hreward
              (measurable_selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction))
            hreward).le i)))

/-- Generated-UCB large-gap event bound with no range assumptions. -/
theorem measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best : Fin K)
    (armMean : Fin K -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy :
      SelectedPolicySuccessorRewardMapLaw hK mu rewardKernel context
        defaultAction reward hreward sigma2 T delta) :
    mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
      ENNReal.ofReal delta := by
  let policy := selectedPolicySuccessorHistoryPolicy
    hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    hK sigma2 T delta defaultAction
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let source :=
    selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
      hK reward armMean sigma2 T delta defaultAction best
  have htail :=
    measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
      (mu := mu)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (arms := (Finset.univ : Finset (Fin K)))
      (by exact ⟨defaultAction, Finset.mem_univ _⟩)
      (armMean := armMean)
      (reward := reward)
      (hreward := hreward)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hstate := measurable_selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      (hmean := hmean)
      (hkernel := hkernel)
      (hvariance := hvariance)
      (harmMean := by
        intro i history arm _harm
        exact harmMean i history arm)
      (h_reward_map_eq_policy := by
        simpa [SelectedPolicySuccessorRewardMapLaw, policy, state, action,
          selectedPolicySuccessorGeneratedUCBAction] using
            h_reward_map_eq_policy)
      T hT hsigma2 delta hdelta source
  simpa [source, action, policy, state,
    selectedPolicySuccessorGeneratedUCBAction] using htail

/--
Expected pull count at the explicit generated-UCB threshold, using only the
centered-kernel law and the selected reward-map identity.
-/
theorem lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best chosen : Fin K)
    (armMean : Fin K -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy :
      SelectedPolicySuccessorRewardMapLaw hK mu rewardKernel context
        defaultAction reward hreward sigma2 T delta)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen) :
    ∫⁻ omega,
        (ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1) : ENNReal) ∂mu <=
      (selectedPolicySuccessorPullThreshold K sigma2 T delta
          (meanGap (fun arm => (armMean arm : Real)) best chosen) : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  have hlargeGap :=
    measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_of_reward_map_eq_selected_policy_centeredKernel
      (hK := hK)
      (mu := mu)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (best := best)
      (armMean := armMean)
      (reward := reward)
      (hreward := hreward)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmean)
      (hkernel := hkernel)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy := h_reward_map_eq_policy)
  exact
    lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_largeGap
      hK mu reward hreward armMean sigma2 T hT delta hdelta
      defaultAction best chosen hgap hlargeGap

/--
Finite-arm ENNReal pseudo-regret assembly for the centered-kernel generated-UCB
route. Positive-gap arms use their explicit pull threshold; zero gaps vanish.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (h_reward_map_eq_policy :
      SelectedPolicySuccessorRewardMapLaw model.hK mu rewardKernel context
        defaultAction reward hreward sigma2 T delta) :
    ∫⁻ omega,
        ENNReal.ofReal
          (((pseudoRegret model
            (selectedPolicySuccessorGeneratedUCBRegretAction
              model.hK sigma2 T delta defaultAction reward omega)
            T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((selectedPolicySuccessorPullThreshold K sigma2 T delta
              (((model.gap arm : Rat) : Real)) : Nat) : ENNReal) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  let action := selectedPolicySuccessorGeneratedUCBRegretAction
    model.hK sigma2 T delta defaultAction reward
  let bound : Fin K -> ENNReal := fun arm =>
    (selectedPolicySuccessorPullThreshold K sigma2 T delta
        (((model.gap arm : Rat) : Real)) : ENNReal) +
      (T : ENNReal) * ENNReal.ofReal delta
  have hbase :=
    lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount
      mu model action
      (fun t =>
        measurable_selectedPolicySuccessorGeneratedUCBRegretAction
          model.hK sigma2 T delta defaultAction reward hreward t)
      T bound
  have hcount : forall arm : Fin K,
      0 < (((model.gap arm : Rat) : Real)) ->
        ∫⁻ omega,
            ((pullCount (action omega) arm T : Nat) : ENNReal) ∂mu <=
          bound arm := by
    intro arm hgap
    have hmeanGap :
        0 < meanGap (fun a => ((model.mean a : Rat) : Real))
          model.bestArm arm := by
      rwa [modelMeanGap_bestArm_eq_realGap]
    have harm :=
      lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_reward_map_eq_selected_policy_centeredKernel
        (hK := model.hK)
        (mu := mu)
        (rewardKernel := rewardKernel)
        (context := context)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (best := model.bestArm)
        (chosen := arm)
        (armMean := model.mean)
        (reward := reward)
        (hreward := hreward)
        (sigma2 := sigma2)
        (hcontext := hcontext)
        (hmean := hmean)
        (hkernel := hkernel)
        (T := T)
        (hT := hT)
        (hsigma2 := hsigma2)
        (delta := delta)
        (hdelta := hdelta)
        (hvariance := hvariance)
        (harmMean := harmMean)
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        (hgap := hmeanGap)
    simpa only [action, bound,
      modelMeanGap_bestArm_eq_realGap,
      pullCount_selectedPolicySuccessorGeneratedUCBRegretAction_eq] using harm
  refine (hbase hcount).trans_eq ?_
  apply Finset.sum_congr rfl
  intro arm _harm
  simp only [bound, mul_add]

/-- Textbook reciprocal-gap pseudo-regret sum for the centered-kernel route. -/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_of_reward_map_eq_selected_policy_centeredKernel
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (h_reward_map_eq_policy :
      SelectedPolicySuccessorRewardMapLaw model.hK mu rewardKernel context
        defaultAction reward hreward sigma2 T delta) :
    ∫⁻ omega,
        ENNReal.ofReal
          (((pseudoRegret model
            (selectedPolicySuccessorGeneratedUCBRegretAction
              model.hK sigma2 T delta defaultAction reward omega)
            T : Rat) : Real)) ∂mu <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          ENNReal.ofReal
              (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
                (((model.gap arm : Rat) : Real))) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  refine
    (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_of_reward_map_eq_selected_policy_centeredKernel
      (mu := mu)
      (model := model)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (reward := reward)
      (hreward := hreward)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmean)
      (hkernel := hkernel)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy := h_reward_map_eq_policy)).trans ?_
  exact sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum
    model sigma2 T delta

/--
Canonical reward-only generated-UCB textbook pseudo-regret theorem.

The canonical `trajMeasure` supplies the selected conditional reward law, and
`CenteredRewardKernelLaw` supplies the analytic MGF/integrability contract.
Consequently no raw-reward or mean-range premise remains.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i history)) <= sigma2)
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
      ∂(selectedPolicySuccessorRewardTrajMeasure model.hK mu0 rewardKernel
        context hcontext sigma2 T delta defaultAction) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          ENNReal.ofReal
              (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
                (((model.gap arm : Rat) : Real))) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  let mu := selectedPolicySuccessorRewardTrajMeasure model.hK mu0 rewardKernel
    context hcontext sigma2 T delta defaultAction
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  have hlaw :
      SelectedPolicySuccessorRewardMapLaw model.hK mu rewardKernel context
        defaultAction reward (fun t => measurable_pi_apply t)
          sigma2 T delta := by
    intro i
    simpa [mu, reward, SelectedPolicySuccessorRewardMapLaw] using
      (selectedPolicySuccessorGeneratedUCB_reward_map_eq_selected_policy_trajMeasure
        model.hK mu0 rewardKernel context hcontext sigma2 T delta
          defaultAction i)
  simpa [mu, reward] using
    (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_of_reward_map_eq_selected_policy_centeredKernel
      (mu := mu)
      (model := model)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (reward := reward)
      (hreward := fun t => measurable_pi_apply t)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmean)
      (hkernel := hkernel)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy := hlaw))

end UCB
end BanditRLProof
