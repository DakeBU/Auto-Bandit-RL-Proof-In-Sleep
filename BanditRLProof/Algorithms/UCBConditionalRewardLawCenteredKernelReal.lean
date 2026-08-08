import BanditRLProof.Algorithms.UCBConditionalRewardLawCenteredKernel
import BanditRLProof.ExpectationRegretPullCount

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/-- A positive-gap arm has a nonnegative textbook threshold contribution. -/
theorem selectedPolicySuccessorTextbookGapBudget_nonneg
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (hgap : 0 < gap) :
    0 <= selectedPolicySuccessorTextbookGapBudget K sigma2 T delta gap := by
  have hlog :
      0 <= selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta := by
    simp [selectedPolicySuccessorFiniteArmTimeLogBudget]
  unfold selectedPolicySuccessorTextbookGapBudget
  positivity

/--
Finite-horizon shifted UCB pseudo-regret is Bochner integrable whenever the
underlying reward coordinates are measurable and the ambient measure is
finite. No reward-law or concentration assumption is needed for this
regularity statement.
-/
theorem integrable_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (model : FiniteBanditModel K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Integrable
      (fun omega : Omega =>
        ((pseudoRegret model
          (selectedPolicySuccessorGeneratedUCBRegretAction
            hK sigma2 T delta defaultAction reward omega)
          T : Rat) : Real)) mu := by
  let action : Omega -> ActionTrace (Fin K) :=
    selectedPolicySuccessorGeneratedUCBRegretAction
      hK sigma2 T delta defaultAction reward
  apply integrable_real_pseudoRegret_of_integrable_pullCount
  intro arm
  apply integrable_real_pullCount_of_measurable_action mu action
  intro t
  simpa [action] using
    (measurable_selectedPolicySuccessorGeneratedUCBRegretAction
      hK sigma2 T delta defaultAction reward hreward t)

/--
Canonical Real/Bochner expected pseudo-regret theorem for the generated UCB
trajectory measure and a centered sub-Gaussian reward kernel.

The probabilistic work is inherited from the ENNReal canonical theorem. This
wrapper proves finite-horizon integrability, uses nonnegativity of model gaps,
and converts the finite ENNReal textbook sum term by term to `Real`.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
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
    MeasureTheory.integral
        (selectedPolicySuccessorRewardTrajMeasure model.hK mu0 rewardKernel
          context hcontext sigma2 T delta defaultAction)
        (fun trajectory : RewardTrace Rat =>
          ((pseudoRegret model
            (selectedPolicySuccessorGeneratedUCBRegretAction
              model.hK sigma2 T delta defaultAction
              (fun y : RewardTrace Rat => y) trajectory)
            T : Rat) : Real)) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
              (((model.gap arm : Rat) : Real)) +
            (((model.gap arm : Rat) : Real)) * ((T : Real) * delta)) := by
  let mu := selectedPolicySuccessorRewardTrajMeasure model.hK mu0 rewardKernel
    context hcontext sigma2 T delta defaultAction
  let action : RewardTrace Rat -> ActionTrace (Fin K) :=
    selectedPolicySuccessorGeneratedUCBRegretAction
      model.hK sigma2 T delta defaultAction (fun y : RewardTrace Rat => y)
  let regret : RewardTrace Rat -> Real := fun trajectory =>
    ((pseudoRegret model (action trajectory) T : Rat) : Real)
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
  have haction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => action trajectory t) := by
    intro t
    simpa [action] using
      (measurable_selectedPolicySuccessorGeneratedUCBRegretAction
        model.hK sigma2 T delta defaultAction
          (fun y : RewardTrace Rat => y) (fun s => measurable_pi_apply s) t)
  have hintegrable : Integrable regret mu := by
    simpa [regret, action] using
      (integrable_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction
        model.hK mu model sigma2 T delta defaultAction
          (fun y : RewardTrace Rat => y) (fun s => measurable_pi_apply s))
  have hnonneg : forall trajectory : RewardTrace Rat, 0 <= regret trajectory := by
    intro trajectory
    have hrat :
        (0 : Rat) <= pseudoRegret model (action trajectory) T := by
      rw [pseudoRegret_eq_finset_sum_gap_mul_pullCount]
      exact Finset.sum_nonneg fun arm _ =>
        mul_nonneg (FiniteBanditModel.gap_nonneg model arm) (by positivity)
    dsimp [regret]
    exact_mod_cast hrat
  have hlin :
      MeasureTheory.lintegral mu (fun trajectory => ENNReal.ofReal (regret trajectory)) <=
        rhsENN := by
    simpa [mu, action, regret, rhsENN] using
      (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
        (model := model)
        (mu0 := mu0)
        (rewardKernel := rewardKernel)
        (context := context)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
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
        (harmMean := harmMean))
  have hrhs_ne_top : rhsENN ≠ ∞ := by
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
  simpa [mu, action, regret, rhsReal] using hreal

end UCB
end BanditRLProof
