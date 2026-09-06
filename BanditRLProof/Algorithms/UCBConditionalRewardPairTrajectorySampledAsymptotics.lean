import BanditRLProof.Algorithms.UCBConditionalRewardPairTrajectorySampledReal
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Asymptotic sampled-successor UCB pseudo-regret

This module runs the canonical pair-trajectory sampled-successor UCB theorem
with confidence budget `1 / (T + 1)`, proves logarithmic expected
pseudo-regret for fixed model data, and derives vanishing expected average
pseudo-regret for the resulting horizon-indexed policy family.
-/

open scoped BigOperators ENNReal NNReal Topology

open Filter MeasureTheory ProbabilityTheory Real

namespace BanditRLProof
namespace UCB

/-- Confidence schedule used by the fixed-model asymptotic UCB family. -/
noncomputable def selectedPolicySuccessorAsymptoticDelta (T : Nat) : Real :=
  1 / (((T + 1 : Nat) : Real))

theorem selectedPolicySuccessorAsymptoticDelta_pos (T : Nat) :
    0 < selectedPolicySuccessorAsymptoticDelta T := by
  unfold selectedPolicySuccessorAsymptoticDelta
  positivity

theorem horizon_mul_selectedPolicySuccessorAsymptoticDelta_le_one (T : Nat) :
    (T : Real) * selectedPolicySuccessorAsymptoticDelta T <= 1 := by
  unfold selectedPolicySuccessorAsymptoticDelta
  calc
    (T : Real) * (1 / (((T + 1 : Nat) : Real))) =
        (T : Real) / (((T + 1 : Nat) : Real)) := by ring
    _ <= 1 := (div_le_one (by positivity)).2 (by norm_num)

/-- Under the asymptotic schedule, the full-horizon peeling argument is a polynomial. -/
theorem selectedPolicySuccessorFiniteArmTimeLogBudget_asymptoticDelta_eq
    (K T : Nat) (hK : 0 < K) (hT : 0 < T) :
    selectedPolicySuccessorFiniteArmTimeLogBudget K T T
        (selectedPolicySuccessorAsymptoticDelta T) =
      max
        (Real.log
          (2 * (K : Real) * (T : Real) * (T : Real) *
            (((T + 1 : Nat) : Real))))
        0 := by
  unfold selectedPolicySuccessorFiniteArmTimeLogBudget
  congr 2
  unfold selectedPolicySuccessorAsymptoticDelta
  push_cast
  field_simp

/-- Eventually, the scheduled finite-arm/time peeling budget is at most `4 log(T+1)`. -/
theorem selectedPolicySuccessorFiniteArmTimeLogBudget_asymptoticDelta_le
    (K T : Nat) (hK : 0 < K) (hT : 0 < T) (hlarge : 2 * K <= T + 1) :
    selectedPolicySuccessorFiniteArmTimeLogBudget K T T
        (selectedPolicySuccessorAsymptoticDelta T) <=
      4 * Real.log (((T + 1 : Nat) : Real)) := by
  rw [selectedPolicySuccessorFiniteArmTimeLogBudget_asymptoticDelta_eq
    K T hK hT]
  let n : Real := (((T + 1 : Nat) : Real))
  let arg : Real := 2 * (K : Real) * (T : Real) * (T : Real) * n
  have hn_one : 1 <= n := by
    dsimp [n]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le T)
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn_one
  have htwoK : 2 * (K : Real) <= n := by
    dsimp [n]
    exact_mod_cast hlarge
  have hTn : (T : Real) <= n := by
    dsimp [n]
    exact_mod_cast Nat.le_succ T
  have harg_pos : 0 < arg := by
    dsimp [arg]
    positivity
  have harg_le : arg <= n ^ 4 := by
    calc
      arg <= n * n * n * n := by
        dsimp [arg]
        gcongr
      _ = n ^ 4 := by ring
  have hlog_le : Real.log arg <= 4 * Real.log n := by
    calc
      Real.log arg <= Real.log (n ^ 4) :=
        Real.log_le_log harg_pos harg_le
      _ = 4 * Real.log n := by
        rw [Real.log_pow]
        norm_num
  have hlog_nonneg : 0 <= 4 * Real.log n := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg hn_one)
  simpa [arg, n] using max_le hlog_le hlog_nonneg

/-- Fixed coefficient that absorbs one positive-gap arm's scheduled textbook budget. -/
noncomputable def selectedPolicySuccessorAsymptoticGapCoefficient
    (sigma2 : NNReal) (gap : Real) : Real :=
  128 * (((sigma2 : NNReal) : Real)) / gap + 16 + 3 * gap

theorem selectedPolicySuccessorTextbookGapBudget_add_failure_asymptoticDelta_le
    (K : Nat) (sigma2 : NNReal) (T : Nat) (gap : Real)
    (hK : 0 < K) (hT : 0 < T) (hlarge : 2 * K <= T + 1)
    (hgap : 0 < gap) :
    selectedPolicySuccessorTextbookGapBudget K sigma2 T
          (selectedPolicySuccessorAsymptoticDelta T) gap +
        gap * ((T : Real) * selectedPolicySuccessorAsymptoticDelta T) <=
      selectedPolicySuccessorAsymptoticGapCoefficient sigma2 gap *
        (1 + Real.log (((T + 1 : Nat) : Real))) := by
  let variance : Real := (((sigma2 : NNReal) : Real))
  let budget := selectedPolicySuccessorFiniteArmTimeLogBudget K T T
    (selectedPolicySuccessorAsymptoticDelta T)
  let logN := Real.log (((T + 1 : Nat) : Real))
  let A := 128 * variance / gap + 16
  let C := A + 3 * gap
  have hlogN : 0 <= logN := by
    dsimp [logN]
    exact Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le T))
  have hbudget : budget <= 4 * logN := by
    simpa [budget, logN] using
      selectedPolicySuccessorFiniteArmTimeLogBudget_asymptoticDelta_le
        K T hK hT hlarge
  have hvariance : 0 <= variance := by
    dsimp [variance]
    positivity
  have hquad :
      32 * variance * budget / gap <=
        (128 * variance / gap) * logN := by
    calc
      32 * variance * budget / gap <=
          32 * variance * (4 * logN) / gap := by
        gcongr
      _ = (128 * variance / gap) * logN := by ring
  have hlinear : 4 * budget <= 16 * logN := by
    linarith
  have hfailure :
      gap * ((T : Real) * selectedPolicySuccessorAsymptoticDelta T) <= gap :=
    by
      simpa using mul_le_mul_of_nonneg_left
        (horizon_mul_selectedPolicySuccessorAsymptoticDelta_le_one T) hgap.le
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hmain :
      selectedPolicySuccessorTextbookGapBudget K sigma2 T
            (selectedPolicySuccessorAsymptoticDelta T) gap +
          gap * ((T : Real) * selectedPolicySuccessorAsymptoticDelta T) <=
        A * logN + 3 * gap := by
    unfold selectedPolicySuccessorTextbookGapBudget
    dsimp [budget, variance] at hquad hlinear
    dsimp [A, logN]
    linarith
  have hAL : A * logN <= C * logN := by
    apply mul_le_mul_of_nonneg_right _ hlogN
    dsimp [C]
    linarith
  have hconst : 3 * gap <= C := by
    dsimp [C]
    linarith
  calc
    selectedPolicySuccessorTextbookGapBudget K sigma2 T
          (selectedPolicySuccessorAsymptoticDelta T) gap +
        gap * ((T : Real) * selectedPolicySuccessorAsymptoticDelta T) <=
      A * logN + 3 * gap := hmain
    _ <= C * logN + C := add_le_add hAL hconst
    _ = selectedPolicySuccessorAsymptoticGapCoefficient sigma2 gap *
        (1 + Real.log (((T + 1 : Nat) : Real))) := by
      dsimp [C, A, variance, logN,
        selectedPolicySuccessorAsymptoticGapCoefficient]
      ring

/-- Fixed finite-arm coefficient for the asymptotic textbook UCB envelope. -/
noncomputable def selectedPolicySuccessorAsymptoticModelCoefficient
    {K : Nat} (model : FiniteBanditModel K) (sigma2 : NNReal) : Real :=
  ((Finset.univ : Finset (Fin K)).filter (fun arm =>
    0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
      selectedPolicySuccessorAsymptoticGapCoefficient sigma2
        (((model.gap arm : Rat) : Real)))

theorem selectedPolicySuccessorTextbookGapSum_asymptoticDelta_le
    {K : Nat} (model : FiniteBanditModel K) (sigma2 : NNReal) (T : Nat)
    (hT : 0 < T) (hlarge : 2 * K <= T + 1) :
    ((Finset.univ : Finset (Fin K)).filter (fun arm =>
      0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
        selectedPolicySuccessorTextbookGapBudget K sigma2 T
            (selectedPolicySuccessorAsymptoticDelta T)
            (((model.gap arm : Rat) : Real)) +
          (((model.gap arm : Rat) : Real)) *
            ((T : Real) * selectedPolicySuccessorAsymptoticDelta T)) <=
      selectedPolicySuccessorAsymptoticModelCoefficient model sigma2 *
        (1 + Real.log (((T + 1 : Nat) : Real))) := by
  classical
  unfold selectedPolicySuccessorAsymptoticModelCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro arm harm
  have hgap : 0 < (((model.gap arm : Rat) : Real)) :=
    (Finset.mem_filter.mp harm).2
  exact
    selectedPolicySuccessorTextbookGapBudget_add_failure_asymptoticDelta_le
      K sigma2 T (((model.gap arm : Rat) : Real))
      model.hK hT hlarge hgap

/--
Exact sampled-successor expected pseudo-regret for the canonical pair process
at confidence budget `1 / (T + 1)`.
-/
noncomputable def selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (defaultAction : Fin K) (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (T : Nat) : Real :=
  let delta := selectedPolicySuccessorAsymptoticDelta T
  let policy := selectedPolicySuccessorHistoryPolicy
    model.hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    model.hK sigma2 T delta defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history => context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history => state i (History.pairHistoryRewardProjection history)
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
  MeasureTheory.integral mu (fun trajectory =>
    (((pseudoRegret model
      (actionRewardTrajectorySuccessorAction trajectory) T : Rat) : Real)))

/-- Pointwise fixed-horizon envelope used by the asymptotic route. -/
theorem selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_nonneg_and_le
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          varianceProxy (context i history) arm <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (T : Nat) (hT : 0 < T) (hlarge : 2 * K <= T + 1) :
    0 <= selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
        model mu0 rewardKernel context defaultAction sigma2 hcontext T /\
      selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
          model mu0 rewardKernel context defaultAction sigma2 hcontext T <=
        selectedPolicySuccessorAsymptoticModelCoefficient model sigma2 *
          (1 + Real.log (((T + 1 : Nat) : Real))) := by
  constructor
  · unfold selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
    exact integral_nonneg fun trajectory => by
      show (0 : Real) <=
        (((pseudoRegret model
          (actionRewardTrajectorySuccessorAction trajectory) T : Rat) : Real))
      have hrat :
          (0 : Rat) <= pseudoRegret model
            (actionRewardTrajectorySuccessorAction trajectory) T := by
        rw [pseudoRegret_eq_finset_sum_gap_mul_pullCount]
        exact Finset.sum_nonneg fun arm _ =>
          mul_nonneg (FiniteBanditModel.gap_nonneg model arm) (by positivity)
      exact_mod_cast hrat
  · calc
      selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
          model mu0 rewardKernel context defaultAction sigma2 hcontext T <=
        ((Finset.univ : Finset (Fin K)).filter (fun arm =>
          0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
            selectedPolicySuccessorTextbookGapBudget K sigma2 T
                (selectedPolicySuccessorAsymptoticDelta T)
                (((model.gap arm : Rat) : Real)) +
              (((model.gap arm : Rat) : Real)) *
                ((T : Real) * selectedPolicySuccessorAsymptoticDelta T)) := by
        unfold selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
        exact
          integral_real_pseudoRegret_actionRewardTrajectorySuccessorAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
            (model := model)
            (mu0 := mu0)
            (rewardKernel := rewardKernel)
            (context := context)
            (mean := mean)
            (varianceProxy := varianceProxy)
            (defaultAction := defaultAction)
            (sigma2 := sigma2)
            (T := T)
            (delta := selectedPolicySuccessorAsymptoticDelta T)
            (hcontext := hcontext)
            (hmean := hmean)
            (law := law)
            (hvariance := fun i _hi history =>
              hvariance i history _)
            (harmMean := harmMean)
            (hT := hT)
            (hsigma2 := hsigma2)
            (hdelta := selectedPolicySuccessorAsymptoticDelta_pos T)
      _ <= selectedPolicySuccessorAsymptoticModelCoefficient model sigma2 *
          (1 + Real.log (((T + 1 : Nat) : Real))) :=
        selectedPolicySuccessorTextbookGapSum_asymptoticDelta_le
          model sigma2 T hT hlarge

theorem selectedPolicySuccessorAsymptoticModelCoefficient_nonneg
    {K : Nat} (model : FiniteBanditModel K) (sigma2 : NNReal) :
    0 <= selectedPolicySuccessorAsymptoticModelCoefficient model sigma2 := by
  classical
  unfold selectedPolicySuccessorAsymptoticModelCoefficient
  apply Finset.sum_nonneg
  intro arm harm
  have hgap : 0 < (((model.gap arm : Rat) : Real)) :=
    (Finset.mem_filter.mp harm).2
  unfold selectedPolicySuccessorAsymptoticGapCoefficient
  positivity

theorem one_add_log_natCast_succ_isBigO_log_natCast_succ :
    (fun T : Nat => 1 + Real.log (((T + 1 : Nat) : Real))) =O[atTop]
      (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) := by
  let n : Nat -> Real := fun T => (((T + 1 : Nat) : Real))
  have hn_tendsto : Tendsto n atTop atTop := by
    exact (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
  have hconst :
      (fun _T : Nat => (1 : Real)) =o[atTop]
        (fun T : Nat => Real.log (n T)) := by
    simpa only [Function.comp_apply] using
      (Real.isLittleO_const_log_atTop (c := (1 : Real))).comp_tendsto
        hn_tendsto
  have hsum := hconst.isBigO.add
    (Asymptotics.isBigO_refl (fun T : Nat => Real.log (n T)) atTop)
  simpa [n] using hsum

/--
For fixed model and reward-law data, the exact canonical sampled-successor
expected pseudo-regret is logarithmic for the horizon-indexed confidence
schedule `1 / (T + 1)`.
-/
theorem selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_isBigO_log
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          varianceProxy (context i history) arm <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real))) :
    (selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
      model mu0 rewardKernel context defaultAction sigma2 hcontext) =O[atTop]
      (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) := by
  let coefficient :=
    selectedPolicySuccessorAsymptoticModelCoefficient model sigma2
  let envelope : Nat -> Real := fun T =>
    coefficient * (1 + Real.log (((T + 1 : Nat) : Real)))
  have hcoefficient : 0 <= coefficient := by
    exact selectedPolicySuccessorAsymptoticModelCoefficient_nonneg model sigma2
  have henvelope : envelope =O[atTop]
      (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) := by
    simpa [envelope, coefficient] using
      one_add_log_natCast_succ_isBigO_log_natCast_succ.const_mul_left
        (selectedPolicySuccessorAsymptoticModelCoefficient model sigma2)
  rw [Asymptotics.isBigO_iff] at henvelope ⊢
  obtain ⟨c, hc⟩ := henvelope
  refine ⟨c, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (2 * K)] with T henvelopeT hTlarge
  have hT : 0 < T :=
    (Nat.mul_pos (by norm_num) model.hK).trans_le hTlarge
  have hlarge : 2 * K <= T + 1 := hTlarge.trans (Nat.le_succ T)
  have hpoint :=
    selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_nonneg_and_le
      model mu0 rewardKernel context mean varianceProxy defaultAction sigma2
      hcontext hmean law hvariance harmMean hsigma2 T hT hlarge
  have henvelope_nonneg : 0 <= envelope T := by
    dsimp [envelope]
    exact mul_nonneg hcoefficient (add_nonneg zero_le_one
      (Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le T))))
  calc
    ‖selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
        model mu0 rewardKernel context defaultAction sigma2 hcontext T‖ =
      selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
        model mu0 rewardKernel context defaultAction sigma2 hcontext T :=
      Real.norm_of_nonneg hpoint.1
    _ <= envelope T := by simpa [envelope, coefficient] using hpoint.2
    _ = ‖envelope T‖ := (Real.norm_of_nonneg henvelope_nonneg).symm
    _ <= c * ‖Real.log (((T + 1 : Nat) : Real))‖ := henvelopeT

theorem log_natCast_succ_isLittleO_natCast_succ :
    (fun T : Nat => Real.log (((T + 1 : Nat) : Real))) =o[atTop]
      (fun T : Nat => (((T + 1 : Nat) : Real))) := by
  let n : Nat -> Real := fun T => (((T + 1 : Nat) : Real))
  have hn_tendsto : Tendsto n atTop atTop := by
    exact (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
  simpa [n, Function.comp_apply] using
    Real.isLittleO_log_id_atTop.comp_tendsto hn_tendsto

theorem selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_isLittleO_natCast_succ
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          varianceProxy (context i history) arm <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real))) :
    (selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
      model mu0 rewardKernel context defaultAction sigma2 hcontext) =o[atTop]
      (fun T : Nat => (((T + 1 : Nat) : Real))) :=
  (selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_isBigO_log
    model mu0 rewardKernel context mean varianceProxy defaultAction sigma2
    hcontext hmean law hvariance harmMean hsigma2).trans_isLittleO
      log_natCast_succ_isLittleO_natCast_succ

/-- Expected sampled-successor pseudo-regret normalized by `T + 1`. -/
noncomputable def selectedPolicySuccessorActionRewardTrajMeasureExpectedAveragePseudoRegret
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (defaultAction : Fin K) (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (T : Nat) : Real :=
  selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret
      model mu0 rewardKernel context defaultAction sigma2 hcontext T /
    (((T + 1 : Nat) : Real))

/--
For the fixed-model horizon-indexed canonical UCB family, expected
sampled-successor pseudo-regret normalized by `T + 1` tends to zero.
-/
theorem selectedPolicySuccessorActionRewardTrajMeasureExpectedAveragePseudoRegret_tendsto_zero
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          varianceProxy (context i history) arm <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real))) :
    Tendsto
      (selectedPolicySuccessorActionRewardTrajMeasureExpectedAveragePseudoRegret
        model mu0 rewardKernel context defaultAction sigma2 hcontext)
      atTop (nhds 0) := by
  have hlimit :=
    (selectedPolicySuccessorActionRewardTrajMeasureExpectedPseudoRegret_isLittleO_natCast_succ
      model mu0 rewardKernel context mean varianceProxy defaultAction sigma2
      hcontext hmean law hvariance harmMean hsigma2).tendsto_div_nhds_zero
  convert hlimit using 1

end UCB
end BanditRLProof
