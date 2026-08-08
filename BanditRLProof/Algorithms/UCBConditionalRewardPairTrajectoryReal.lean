import BanditRLProof.Algorithms.UCBConditionalRewardPairTrajectory
import BanditRLProof.Algorithms.UCBConditionalRewardLawCenteredKernelReal

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/-
Canonical pair-trajectory Real/Bochner textbook pseudo-regret endpoint.

The probabilistic estimate is inherited from the pair-trajectory ENNReal
theorem. Finite-horizon integrability and the finite ENNReal-to-Real sum
conversion are discharged internally.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal) (T : Nat) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat, i < T - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hT : 0 < T) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
    let policy := selectedPolicySuccessorHistoryPolicy
      model.hK sigma2 T delta defaultAction
    let state := selectedPolicySuccessorHistoryState
      model.hK sigma2 T delta defaultAction
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
      fun i history =>
        context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
          SelectedPolicySuccessorFiniteHistoryState K :=
      fun i history =>
        state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (measurable_selectedPolicySuccessorHistoryState
        model.hK sigma2 T delta defaultAction i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState
    let mu :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorGeneratedUCBRegretAction
      model.hK sigma2 T delta defaultAction reward
    MeasureTheory.integral mu (fun trajectory =>
        (((pseudoRegret model (action trajectory) T : Rat) : Real))) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
              (((model.gap arm : Rat) : Real)) +
            (((model.gap arm : Rat) : Real)) * ((T : Real) * delta)) := by
  let policy := selectedPolicySuccessorHistoryPolicy
    model.hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    model.hK sigma2 T delta defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history =>
      context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history =>
      state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_selectedPolicySuccessorHistoryState
      model.hK sigma2 T delta defaultAction i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      pairContext pairState hpairContext hpairState
  let mu :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  let action := selectedPolicySuccessorGeneratedUCBRegretAction
    model.hK sigma2 T delta defaultAction reward
  let regret : (Nat -> Prod (Fin K) Rat) -> Real := fun trajectory =>
    (((pseudoRegret model (action trajectory) T : Rat) : Real))
  let rhsENN : ENNReal :=
    ((Finset.univ : Finset (Fin K)).filter (fun arm =>
      0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
        ENNReal.ofReal
            (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
              (((model.gap arm : Rat) : Real))) +
          ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
            ((T : ENNReal) * ENNReal.ofReal delta))
  let rhsReal : Real :=
    ((Finset.univ : Finset (Fin K)).filter (fun arm =>
      0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
        selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
            (((model.gap arm : Rat) : Real)) +
          (((model.gap arm : Rat) : Real)) * ((T : Real) * delta))
  change MeasureTheory.integral mu regret <= rhsReal
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod (Fin K) Rat =>
        reward trajectory t) := by
    intro t
    exact measurable_snd.comp (measurable_pi_apply t)
  have hintegrable : Integrable regret mu := by
    simpa [regret, action] using
      (integrable_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction
        model.hK mu model sigma2 T delta defaultAction reward hreward)
  have hnonneg : forall trajectory : Nat -> Prod (Fin K) Rat,
      0 <= regret trajectory := by
    intro trajectory
    have hrat :
        (0 : Rat) <= pseudoRegret model (action trajectory) T := by
      rw [pseudoRegret_eq_finset_sum_gap_mul_pullCount]
      exact Finset.sum_nonneg fun arm _ =>
        mul_nonneg (FiniteBanditModel.gap_nonneg model arm) (by positivity)
    dsimp [regret]
    exact_mod_cast hrat
  have hlin :
      MeasureTheory.lintegral mu
          (fun trajectory => ENNReal.ofReal (regret trajectory)) <=
        rhsENN := by
    simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, reward, action, regret, rhsENN] using
      (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
        (model := model)
        (mu0 := mu0)
        (rewardKernel := rewardKernel)
        (context := context)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (sigma2 := sigma2)
        (T := T)
        (delta := delta)
        (hcontext := hcontext)
        (hmean := hmean)
        (law := law)
        (hvariance := hvariance)
        (harmMean := harmMean)
        (hT := hT)
        (hsigma2 := hsigma2)
        (hdelta := hdelta))
  have hrhs_ne_top : rhsENN ≠ ⊤ := by
    dsimp [rhsENN]
    apply ENNReal.sum_ne_top.mpr
    intro arm harm
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.ofReal_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.natCast_ne_top T
        · exact ENNReal.ofReal_ne_top
  have hofReal :
      ENNReal.ofReal (MeasureTheory.integral mu regret) <= rhsENN := by
    rw [ofReal_integral_eq_lintegral_ofReal hintegrable
      (Filter.Eventually.of_forall hnonneg)]
    exact hlin
  have hreal : MeasureTheory.integral mu regret <= rhsENN.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hrhs_ne_top).mp hofReal
  have hrhsReal : rhsENN.toReal = rhsReal := by
    dsimp [rhsENN, rhsReal]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro arm harm
      have hgap : 0 < (((model.gap arm : Rat) : Real)) :=
        (Finset.mem_filter.mp harm).2
      have hbudget :
          0 <= selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
            (((model.gap arm : Rat) : Real)) :=
        selectedPolicySuccessorTextbookGapBudget_nonneg
          K sigma2 T delta (((model.gap arm : Rat) : Real)) hgap
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_ofReal hbudget]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hgap.le]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdelta.le]
      simp
    · intro arm harm
      finiteness
  rw [hrhsReal] at hreal
  exact hreal

end UCB
end BanditRLProof
