import BanditRLProof.Algorithms.UCBConditionalRewardLawPolicy
import BanditRLProof.FiniteBanditModelInvariants
import BanditRLProof.ScalarPseudoRegret

/-!
# Practical selected-policy UCB pseudo-regret assembly

This module connects the explicit expected successor pull-count theorem to the
local finite-bandit pseudo-regret surface. The regret action shifts generated
coordinates `1, ..., T` to the standard pull-count coordinates `0, ..., T-1`.
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory

/-- The UCB designated-best Real mean gap is the local model gap after casting. -/
theorem modelMeanGap_bestArm_eq_realGap
    {K : Nat} (model : FiniteBanditModel K) (arm : Fin K) :
    meanGap (fun a => ((model.mean a : Rat) : Real)) model.bestArm arm =
      ((model.gap arm : Rat) : Real) := by
  by_cases h : arm = model.bestArm
  · subst arm
    simp [meanGap]
  · simp [meanGap, FiniteBanditModel.gap, FiniteBanditModel.bestMean, h]

/-- Textbook-style real contribution of one positive-gap arm's count threshold. -/
noncomputable def selectedPolicySuccessorTextbookGapBudget
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real) : Real :=
  32 * (((sigma2 : NNReal) : Real)) *
        selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta / gap +
    4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta +
    2 * gap

/-- The explicit integer pull threshold is at most its real max plus two. -/
theorem selectedPolicySuccessorPullThreshold_cast_le_realThreshold_add_two
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (hgap : 0 < gap) :
    (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : Real) <=
      selectedPolicySuccessorRealPullThreshold K sigma2 T delta gap + 2 := by
  have hbudget :
      0 <= selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta := by
    simp [selectedPolicySuccessorFiniteArmTimeLogBudget]
  have hthreshold :
      0 <= selectedPolicySuccessorRealPullThreshold K sigma2 T delta gap := by
    unfold selectedPolicySuccessorRealPullThreshold
    positivity
  rw [selectedPolicySuccessorPullThreshold, Nat.cast_add, Nat.cast_one]
  exact le_of_lt (by
    have hceil := Nat.ceil_lt_add_one hthreshold
    linarith)

/-- Multiplying the explicit threshold by a positive gap removes one gap power. -/
theorem gap_mul_selectedPolicySuccessorPullThreshold_cast_le_textbookGapBudget
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (hgap : 0 < gap) :
    gap * (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : Real) <=
      selectedPolicySuccessorTextbookGapBudget K sigma2 T delta gap := by
  let budget := selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta
  let variance := (((sigma2 : NNReal) : Real))
  let quadratic := 32 * variance * budget / gap ^ 2
  let linear := 4 * budget / gap
  have hbudget : 0 <= budget := by
    simp [budget, selectedPolicySuccessorFiniteArmTimeLogBudget]
  have hquadratic : 0 <= quadratic := by
    dsimp [quadratic]
    positivity
  have hlinear : 0 <= linear := by
    dsimp [linear]
    positivity
  have hmax : max quadratic linear <= quadratic + linear := by
    exact max_le (le_add_of_nonneg_right hlinear)
      (le_add_of_nonneg_left hquadratic)
  have hthreshold :=
    selectedPolicySuccessorPullThreshold_cast_le_realThreshold_add_two
      K sigma2 T delta gap hgap
  have hmul := mul_le_mul_of_nonneg_left hthreshold hgap.le
  calc
    gap * (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : Real) <=
        gap * (max quadratic linear + 2) := by
      simpa [selectedPolicySuccessorRealPullThreshold, quadratic, linear,
        variance, budget] using hmul
    _ <= gap * (quadratic + linear + 2) := by
      apply mul_le_mul_of_nonneg_left _ hgap.le
      linarith
    _ = selectedPolicySuccessorTextbookGapBudget K sigma2 T delta gap := by
      dsimp [selectedPolicySuccessorTextbookGapBudget, quadratic, linear,
        variance, budget]
      field_simp [ne_of_gt hgap]

/-- ENNReal form of the one-arm textbook threshold contribution. -/
theorem ofReal_gap_mul_selectedPolicySuccessorPullThreshold_le_textbookGapBudget
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (hgap : 0 < gap) :
    ENNReal.ofReal gap *
        (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : ENNReal) <=
      ENNReal.ofReal
        (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta gap) := by
  rw [← ENNReal.ofReal_natCast
    (selectedPolicySuccessorPullThreshold K sigma2 T delta gap),
    ← ENNReal.ofReal_mul hgap.le]
  exact ENNReal.ofReal_le_ofReal
    (gap_mul_selectedPolicySuccessorPullThreshold_cast_le_textbookGapBudget
      K sigma2 T delta gap hgap)

/--
Finite-arm threshold simplification. Only positive model gaps remain in the
textbook sum, and the confidence-failure contribution is preserved exactly.
-/
theorem sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum
    {K : Nat} (model : FiniteBanditModel K)
    (sigma2 : NNReal) (T : Nat) (delta : Real) :
    (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          (selectedPolicySuccessorPullThreshold K sigma2 T delta
            (((model.gap arm : Rat) : Real)) : ENNReal) +
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((T : ENNReal) * ENNReal.ofReal delta)) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          ENNReal.ofReal
              (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
                (((model.gap arm : Rat) : Real))) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro arm _harm
  have hgap_nonneg : 0 <= (((model.gap arm : Rat) : Real)) := by
    exact_mod_cast FiniteBanditModel.gap_nonneg model arm
  by_cases hgap : 0 < (((model.gap arm : Rat) : Real))
  · simp only [hgap, if_true]
    exact add_le_add
      (ofReal_gap_mul_selectedPolicySuccessorPullThreshold_le_textbookGapBudget
        K sigma2 T delta (((model.gap arm : Rat) : Real)) hgap)
      le_rfl
  · have hgap_zero : (((model.gap arm : Rat) : Real)) = 0 :=
      le_antisymm (le_of_not_gt hgap) hgap_nonneg
    simp [hgap_zero]

/-- Shift successor generated actions `1, ..., T` to regret times `0, ..., T-1`. -/
noncomputable def selectedPolicySuccessorGeneratedUCBRegretAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat) :
    Omega -> ActionTrace (Fin K) :=
  fun omega t =>
    selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward omega (t + 1)

/-- Every coordinate of the shifted generated UCB regret action is measurable. -/
theorem measurable_selectedPolicySuccessorGeneratedUCBRegretAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable (fun omega =>
      selectedPolicySuccessorGeneratedUCBRegretAction
        hK sigma2 T delta defaultAction reward omega t) := by
  exact
    measurable_selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward hreward (t + 1)

/-- The shifted regret pull count is exactly the existing successor pull count. -/
theorem pullCount_selectedPolicySuccessorGeneratedUCBRegretAction_eq
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (omega : Omega) (arm : Fin K) :
    pullCount
        (selectedPolicySuccessorGeneratedUCBRegretAction
          hK sigma2 T delta defaultAction reward omega)
        arm T =
      ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorGeneratedUCBAction
          hK sigma2 T delta defaultAction reward omega)
        arm (T + 1) := by
  unfold ConditionalExpectationReward.successorArmPullCount
  rw [Nat.add_sub_cancel]
  rfl

/--
Generic finite-arm ENNReal pseudo-regret assembly. Only positive-gap arms need
a pull-count bound; zero-gap arms disappear after multiplication.
-/
theorem lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat}
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) (bound : Fin K -> ENNReal)
    (hcount : forall arm : Fin K,
      0 < (((model.gap arm : Rat) : Real)) ->
        ∫⁻ omega,
            ((pullCount (action omega) arm n : Nat) : ENNReal) ∂mu <=
          bound arm) :
    ∫⁻ omega,
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) * bound arm) := by
  let gap : Fin K -> ENNReal := fun arm =>
    ENNReal.ofReal (((model.gap arm : Rat) : Real))
  let count : Fin K -> Omega -> ENNReal := fun arm omega =>
    ((pullCount (action omega) arm n : Nat) : ENNReal)
  have hgap_nonneg : forall arm : Fin K,
      0 <= (((model.gap arm : Rat) : Real)) := by
    intro arm
    exact_mod_cast FiniteBanditModel.gap_nonneg model arm
  have hcount_meas : forall arm : Fin K, Measurable (count arm) := by
    intro arm
    exact measurable_natCast_pullCount
      (Beta := ENNReal) action haction arm n
  calc
    ∫⁻ omega,
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)) ∂mu =
      ∫⁻ omega,
        (Finset.univ : Finset (Fin K)).sum
          (fun arm => gap arm * count arm omega) ∂mu := by
        apply lintegral_congr
        intro omega
        simpa [gap, count] using
          ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
            model (action omega) hgap_nonneg n
    _ = (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ∫⁻ omega, gap arm * count arm omega ∂mu) := by
      rw [lintegral_finset_sum]
      intro arm _harm
      exact (hcount_meas arm).const_mul (gap arm)
    _ = (Finset.univ : Finset (Fin K)).sum (fun arm =>
        gap arm * ∫⁻ omega, count arm omega ∂mu) := by
      apply Finset.sum_congr rfl
      intro arm _harm
      exact lintegral_const_mul (gap arm) (hcount_meas arm)
    _ <= (Finset.univ : Finset (Fin K)).sum (fun arm =>
        gap arm * bound arm) := by
      apply Finset.sum_le_sum
      intro arm _harm
      by_cases hzero : (((model.gap arm : Rat) : Real)) = 0
      · simp [gap, hzero]
      · have hpos : 0 < (((model.gap arm : Rat) : Real)) :=
          lt_of_le_of_ne (hgap_nonneg arm) (Ne.symm hzero)
        exact mul_le_mul_left' (hcount arm hpos) (gap arm)
    _ = (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) * bound arm) := by
      rfl

/--
End-to-end practical selected-reward-law pseudo-regret bound for the concrete
generated UCB policy. Every positive-gap arm uses its own explicit threshold;
zero-gap arms vanish from the finite weighted sum.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_of_reward_map_eq_selected_policy
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
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real)))
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
          mean (context i history) arm = model.mean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc
                (selectedPolicySuccessorGeneratedUCBAction
                  model.hK sigma2 T delta defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := selectedPolicySuccessorHistoryPolicy
                    model.hK sigma2 T delta defaultAction)
                  (state := selectedPolicySuccessorHistoryState
                    model.hK sigma2 T delta defaultAction)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward
                  (measurable_selectedPolicySuccessorHistoryState
                    model.hK sigma2 T delta defaultAction))
                hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (selectedPolicySuccessorGeneratedUCBAction
                model.hK sigma2 T delta defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := selectedPolicySuccessorHistoryPolicy
                  model.hK sigma2 T delta defaultAction)
                (state := selectedPolicySuccessorHistoryState
                  model.hK sigma2 T delta defaultAction)
                (defaultAction := defaultAction) (reward := reward)
                hreward
                (measurable_selectedPolicySuccessorHistoryState
                  model.hK sigma2 T delta defaultAction))
              hreward).le i)))) :
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
      lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_reward_map_eq_selected_policy
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
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        (hgap := hmeanGap)
    simpa only [action, bound,
      modelMeanGap_bestArm_eq_realGap,
      pullCount_selectedPolicySuccessorGeneratedUCBRegretAction_eq] using harm
  refine (hbase hcount).trans_eq ?_
  apply Finset.sum_congr rfl
  intro arm _harm
  simp only [bound, mul_add]

/--
End-to-end practical selected-reward-law pseudo-regret bound with the integer
threshold eliminated in favor of a textbook reciprocal-gap finite sum.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_of_reward_map_eq_selected_policy
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
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real)))
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
          mean (context i history) arm = model.mean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc
                (selectedPolicySuccessorGeneratedUCBAction
                  model.hK sigma2 T delta defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := selectedPolicySuccessorHistoryPolicy
                    model.hK sigma2 T delta defaultAction)
                  (state := selectedPolicySuccessorHistoryState
                    model.hK sigma2 T delta defaultAction)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward
                  (measurable_selectedPolicySuccessorHistoryState
                    model.hK sigma2 T delta defaultAction))
                hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (selectedPolicySuccessorGeneratedUCBAction
                model.hK sigma2 T delta defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := selectedPolicySuccessorHistoryPolicy
                  model.hK sigma2 T delta defaultAction)
                (state := selectedPolicySuccessorHistoryState
                  model.hK sigma2 T delta defaultAction)
                (defaultAction := defaultAction) (reward := reward)
                hreward
                (measurable_selectedPolicySuccessorHistoryState
                  model.hK sigma2 T delta defaultAction))
              hreward).le i)))) :
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
    (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_of_reward_map_eq_selected_policy
      (mu := mu)
      (model := model)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (reward := reward)
      (hreward := hreward)
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
      (h_reward_map_eq_policy := h_reward_map_eq_policy)).trans ?_
  exact sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum
    model sigma2 T delta

end UCB
end BanditRLProof
