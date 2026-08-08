import BanditRLProof.OFULScheduledPowerOfTwoForcedScalarChargeBound
import BanditRLProof.OFULScheduledBoundedStoppingTimeExpectedRegretAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Asymptotic high-probability rate for power-of-two forced OFUL

This module packages the exact scalar all-horizon budget of the fixed
power-of-two forced policy and proves its fixed-model asymptotic growth. The
probability event, policy, canonical measure, and confidence budget are
inherited unchanged from the finite-horizon scalar theorem.
-/

namespace BanditRLProof.OFUL

open Filter Real MeasureTheory Set
open scoped ENNReal Topology

universe u

/-- The complete scalar budget displayed by the power-of-two forced tail. -/
noncomputable def powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  ((Nat.log2 horizon + 1 : Nat) : Real) *
      (2 * S * Real.sqrt L2) +
    telescopingHighProbabilityPseudoRegretBound
      (Feature := Feature) R delta lambda S horizon L2

/--
Increasing the outer confidence budget decreases the explicit telescoping
confidence logarithm.
-/
theorem telescopingHighProbabilityRegretLogBudget_anti_delta
    {Feature : Type u} [Fintype Feature]
    (lambda L2 : Real)
    {deltaSmall deltaLarge : Real}
    (hdeltaSmall : 0 < deltaSmall)
    (hdelta : deltaSmall <= deltaLarge)
    (horizon : Nat) :
    telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda deltaLarge horizon L2 <=
      telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda deltaSmall horizon L2 := by
  have hdeltaLarge : 0 < deltaLarge := hdeltaSmall.trans_le hdelta
  have hnum_nonneg :
      0 <=
        (((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) := by
    positivity
  have hnum_pos :
      0 <
        (((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) := by
    positivity
  have hratio :
      ((((horizon + 1 : Nat) : Real) *
            ((horizon + 2 : Nat) : Real)) / deltaLarge) <=
        ((((horizon + 1 : Nat) : Real) *
            ((horizon + 2 : Nat) : Real)) / deltaSmall) :=
    div_le_div_of_nonneg_left hnum_nonneg hdeltaSmall hdelta
  have hlog :
      Real.log
          ((((horizon + 1 : Nat) : Real) *
              ((horizon + 2 : Nat) : Real)) / deltaLarge) <=
        Real.log
          ((((horizon + 1 : Nat) : Real) *
              ((horizon + 2 : Nat) : Real)) / deltaSmall) :=
    Real.log_le_log (div_pos hnum_pos hdeltaLarge) hratio
  unfold telescopingHighProbabilityRegretLogBudget
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : Real) <= 2))

/--
For fixed positive `delta`, the explicit telescoping confidence logarithm is
`O(log (T + 1))`.
-/
theorem telescopingHighProbabilityRegretLogBudget_isBigO_log_succ
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (delta : Real) (hdelta : 0 < delta)
    (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda delta horizon L2) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) := by
  have hscheduled :
      (fun horizon : Nat =>
        telescopingStandardExpectedRegretLogBudget
          (Feature := Feature) lambda horizon L2) =O[atTop]
        (fun horizon : Nat =>
          Real.log (((horizon + 1 : Nat) : Real))) :=
    telescopingStandardExpectedRegretLogBudget_isBigO_log
      (Feature := Feature) lambda hlambda L2 hL2
  have hcompare :
      (fun horizon : Nat =>
        telescopingHighProbabilityRegretLogBudget
          (Feature := Feature) lambda delta horizon L2) =O[atTop]
        (fun horizon : Nat =>
          telescopingStandardExpectedRegretLogBudget
            (Feature := Feature) lambda horizon L2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    obtain ⟨threshold, hthreshold⟩ :=
      (exists_nat_gt (max (1 / delta) delta) : ∃ threshold : Nat,
        max (1 / delta) delta < threshold)
    filter_upwards [eventually_ge_atTop threshold] with horizon hhorizon
    have hthreshold_le :
        (threshold : Real) <= (((horizon + 1 : Nat) : Real)) := by
      exact_mod_cast le_trans hhorizon (Nat.le_add_right horizon 1)
    have hscale :
        1 / delta < (((horizon + 1 : Nat) : Real)) :=
      ((le_max_left (1 / delta) delta).trans_lt hthreshold).trans_le
        hthreshold_le
    have hdelta_succ :
        delta < (((horizon + 1 : Nat) : Real)) :=
      ((le_max_right (1 / delta) delta).trans_lt hthreshold).trans_le
        hthreshold_le
    have hshare :
        standardExpectedRegretDelta horizon <= delta := by
      unfold standardExpectedRegretDelta
      rw [div_le_iff₀ (by positivity :
        0 < (((horizon + 1 : Nat) : Real)))]
      have hmul :
          1 < (((horizon + 1 : Nat) : Real)) * delta :=
        (div_lt_iff₀ hdelta).mp hscale
      nlinarith
    have hfixed_nonneg :
        0 <=
          telescopingHighProbabilityRegretLogBudget
            (Feature := Feature) lambda delta horizon L2 := by
      have hdet :
          0 <= standardScalarLogDetBudget
            (Feature := Feature) lambda (horizon + 1) L2 :=
        standardScalarLogDetBudget_nonneg
          (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
      have hfirst_nonneg :
          0 <= (((horizon + 1 : Nat) : Real)) := by positivity
      have hsecond_one :
          (1 : Real) <= (((horizon + 2 : Nat) : Real)) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le (horizon + 1))
      have hdelta_prod :
          delta <=
            (((horizon + 1 : Nat) : Real) *
              ((horizon + 2 : Nat) : Real)) :=
        (le_of_lt hdelta_succ).trans
          (le_mul_of_one_le_right hfirst_nonneg hsecond_one)
      have hratio_one :
          (1 : Real) <=
            ((((horizon + 1 : Nat) : Real) *
                ((horizon + 2 : Nat) : Real)) / delta) := by
        rw [le_div_iff₀ hdelta]
        simpa using hdelta_prod
      unfold telescopingHighProbabilityRegretLogBudget
      exact add_nonneg hdet
        (mul_nonneg (by norm_num) (Real.log_nonneg hratio_one))
    have hscheduled_nonneg :
        0 <=
          telescopingStandardExpectedRegretLogBudget
            (Feature := Feature) lambda horizon L2 := by
      rw [←
        telescopingHighProbabilityRegretLogBudget_standardExpectedRegretDelta
          (Feature := Feature) lambda horizon L2]
      exact
        telescopingHighProbabilityRegretLogBudget_nonneg
          (Feature := Feature) lambda hlambda
          (standardExpectedRegretDelta horizon)
          (standardExpectedRegretDelta_pos horizon)
          (standardExpectedRegretDelta_le_one horizon)
          horizon L2 hL2
    have hbudget :
        telescopingHighProbabilityRegretLogBudget
            (Feature := Feature) lambda delta horizon L2 <=
          telescopingStandardExpectedRegretLogBudget
            (Feature := Feature) lambda horizon L2 := by
      rw [←
        telescopingHighProbabilityRegretLogBudget_standardExpectedRegretDelta
          (Feature := Feature) lambda horizon L2]
      exact
        telescopingHighProbabilityRegretLogBudget_anti_delta
          (Feature := Feature) lambda L2
          (standardExpectedRegretDelta_pos horizon) hshare horizon
    rw [Real.norm_eq_abs, abs_of_nonneg hfixed_nonneg,
      Real.norm_eq_abs, abs_of_nonneg hscheduled_nonneg, one_mul]
    exact hbudget
  exact hcompare.trans hscheduled

/--
For fixed model parameters and confidence level, the explicit telescoping
high-probability budget is `O(sqrt (T + 1) * log (T + 1))`.
-/
theorem
    telescopingHighProbabilityPseudoRegretBound_isBigO_sqrt_mul_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real)
    (delta : Real) (hdelta : 0 < delta)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2) =O[atTop]
      (fun horizon : Nat =>
        Real.sqrt (((horizon + 1 : Nat) : Real)) *
          Real.log (((horizon + 1 : Nat) : Real))) := by
  let n : Nat -> Real := fun horizon => (((horizon + 1 : Nat) : Real))
  let logN : Nat -> Real := fun horizon => Real.log (n horizon)
  let sqrtN : Nat -> Real := fun horizon => Real.sqrt (n horizon)
  let B : Nat -> Real := fun horizon =>
    standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2
  let C : Nat -> Real := fun horizon =>
    telescopingHighProbabilityRegretLogBudget
      (Feature := Feature) lambda delta horizon L2
  have hlog_nonneg :
      ∀ᶠ horizon in atTop, 0 <= logN horizon := by
    exact Filter.Eventually.of_forall fun horizon => by
      dsimp [logN, n]
      exact Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon))
  have hB : B =O[atTop] logN := by
    simpa [B, logN, n] using
      standardScalarLogDetBudget_isBigO_log
        (Feature := Feature) lambda hlambda L2 hL2
  have hC : C =O[atTop] logN := by
    simpa [C, logN, n] using
      telescopingHighProbabilityRegretLogBudget_isBigO_log_succ
        (Feature := Feature) lambda hlambda
        delta hdelta L2 hL2
  have hsqrtC :
      (fun horizon => Real.sqrt (C horizon)) =O[atTop]
        (fun horizon => Real.sqrt (logN horizon)) :=
    hC.sqrt hlog_nonneg
  have hsqrt2B :
      (fun horizon => Real.sqrt (2 * B horizon)) =O[atTop]
        (fun horizon => Real.sqrt (logN horizon)) :=
    (hB.const_mul_left 2).sqrt hlog_nonneg
  have hsqrtLogLog :
      (fun horizon => Real.sqrt (logN horizon)) =O[atTop] logN := by
    simpa [logN, n] using sqrt_log_succ_isBigO_log_succ
  have hsqrtN : sqrtN =O[atTop] sqrtN :=
    Asymptotics.isBigO_refl _ _
  have hsqrtN_sqrtLog_scale :
      (fun horizon => sqrtN horizon * Real.sqrt (logN horizon)) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) :=
    hsqrtN.mul hsqrtLogLog
  have hvariance :
      (fun horizon => sqrtN horizon * Real.sqrt (2 * B horizon)) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) :=
    (hsqrtN.mul hsqrt2B).trans hsqrtN_sqrtLog_scale
  have hconfidenceVariance :
      (fun horizon =>
        Real.sqrt (C horizon) *
          (sqrtN horizon * Real.sqrt (2 * B horizon))) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) := by
    have hproduct := hsqrtC.mul hsqrt2B
    have hproductLog :
        (fun horizon =>
          Real.sqrt (C horizon) * Real.sqrt (2 * B horizon)) =O[atTop]
          logN := by
      refine hproduct.congr' Filter.EventuallyEq.rfl ?_
      filter_upwards [hlog_nonneg] with horizon hlog
      exact Real.mul_self_sqrt hlog
    have hmul := hsqrtN.mul hproductLog
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hn_tendsto : Tendsto n atTop atTop := by
    dsimp [n]
    exact (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
  have hconstantLog :
      (fun _horizon : Nat => 2 * S * Real.sqrt L2) =o[atTop] logN := by
    change
      (fun _horizon : Nat => 2 * S * Real.sqrt L2) =o[atTop]
        (fun horizon => Real.log (n horizon))
    simpa only [Function.comp_apply] using
      (Real.isLittleO_const_log_atTop
        (c := 2 * S * Real.sqrt L2)).comp_tendsto hn_tendsto
  have hlogScale :
      logN =O[atTop] (fun horizon => sqrtN horizon * logN horizon) := by
    refine (Asymptotics.isBigO_refl logN atTop).trans_le ?_
    intro horizon
    have hn_one : 1 <= n horizon := by
      dsimp [n]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
    have hsqrt_one : 1 <= sqrtN horizon := by
      dsimp [sqrtN]
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hn_one
    have hlog : 0 <= logN horizon := by
      dsimp [logN]
      exact Real.log_nonneg hn_one
    rw [Real.norm_eq_abs, abs_of_nonneg hlog,
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hlog)]
    nlinarith
  have hconstant :
      (fun _horizon : Nat => 2 * S * Real.sqrt L2) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) :=
    hconstantLog.isBigO.trans hlogScale
  have hconfidenceTerm :
      (fun horizon =>
        2 * R *
          (Real.sqrt (C horizon) *
            (sqrtN horizon * Real.sqrt (2 * B horizon)))) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) :=
    hconfidenceVariance.const_mul_left (2 * R)
  have hbiasTerm :
      (fun horizon =>
        (2 * (Real.sqrt lambda * S)) *
          (sqrtN horizon * Real.sqrt (2 * B horizon))) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) :=
    hvariance.const_mul_left (2 * (Real.sqrt lambda * S))
  have hsum := hconstant.add (hconfidenceTerm.add hbiasTerm)
  refine hsum.congr (fun horizon => ?_) (fun _ => rfl)
  simp only [telescopingHighProbabilityPseudoRegretBound]
  dsimp [B, C, sqrtN, logN, n]
  ring

/-- The cast of `Nat.log2 T + 1` is `O(log (T + 1))`. -/
theorem natCast_log2_add_one_isBigO_log_succ :
    (fun horizon : Nat => ((Nat.log2 horizon + 1 : Nat) : Real)) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) := by
  rw [Asymptotics.isBigO_iff]
  let C : Real := 1 / Real.log 2 + 1 / Real.log 3
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with horizon hhorizon
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hhorizon_pos : 0 < (horizon : Real) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hhorizon
  have hhorizon_le_succ :
      (horizon : Real) <= (((horizon + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.le_add_right horizon 1
  have hthree_le_succ :
      (3 : Real) <= (((horizon + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ hhorizon
  have hlog_horizon_le :
      Real.log (horizon : Real) <=
        Real.log (((horizon + 1 : Nat) : Real)) :=
    Real.log_le_log hhorizon_pos hhorizon_le_succ
  have hlog_three_le :
      Real.log 3 <=
        Real.log (((horizon + 1 : Nat) : Real)) :=
    Real.log_le_log (by norm_num) hthree_le_succ
  have hnat_log :
      (Nat.log2 horizon : Real) <=
        Real.log (((horizon + 1 : Nat) : Real)) / Real.log 2 := by
    calc
      (Nat.log2 horizon : Real) <= Real.logb 2 horizon :=
        Real.log2_le_logb horizon
      _ = Real.log (horizon : Real) / Real.log 2 := by
        rfl
      _ <=
          Real.log (((horizon + 1 : Nat) : Real)) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlog2).2 hlog_horizon_le
  have hone :
      (1 : Real) <=
        Real.log (((horizon + 1 : Nat) : Real)) / Real.log 3 :=
    (le_div_iff₀ hlog3).2 (by simpa using hlog_three_le)
  have hbound :
      ((Nat.log2 horizon + 1 : Nat) : Real) <=
        C * Real.log (((horizon + 1 : Nat) : Real)) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hnat_log hone ⊢
    dsimp [C]
    calc
      (Nat.log2 horizon : Real) + 1 <=
          Real.log ((horizon : Real) + 1) / Real.log 2 +
            Real.log ((horizon : Real) + 1) / Real.log 3 :=
        add_le_add hnat_log hone
      _ =
          (1 / Real.log 2 + 1 / Real.log 3) *
            Real.log ((horizon : Real) + 1) := by
        ring
  have hleft_nonneg :
      0 <= ((Nat.log2 horizon + 1 : Nat) : Real) := by positivity
  have hright_log_nonneg :
      0 <= Real.log (((horizon + 1 : Nat) : Real)) := by
    exact Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon))
  have hC_nonneg : 0 <= C := by
    dsimp [C]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hright_log_nonneg]
  simpa only [Real.norm_eq_abs, abs_of_nonneg hC_nonneg] using hbound

/--
The exact scalar power-of-two forced budget is
`O(sqrt (T + 1) * log (T + 1))`.
-/
theorem
    powerOfTwoForcedScalarHighProbabilityPseudoRegretBound_isBigO_sqrt_mul_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real)
    (delta : Real) (hdelta : 0 < delta)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2) =O[atTop]
      (fun horizon : Nat =>
        Real.sqrt (((horizon + 1 : Nat) : Real)) *
          Real.log (((horizon + 1 : Nat) : Real))) := by
  let logN : Nat -> Real := fun horizon =>
    Real.log (((horizon + 1 : Nat) : Real))
  let sqrtN : Nat -> Real := fun horizon =>
    Real.sqrt (((horizon + 1 : Nat) : Real))
  have hforcedLog :
      (fun horizon : Nat => ((Nat.log2 horizon + 1 : Nat) : Real)) =O[atTop]
        logN := by
    simpa [logN] using natCast_log2_add_one_isBigO_log_succ
  have hlogScale :
      logN =O[atTop] (fun horizon => sqrtN horizon * logN horizon) := by
    refine (Asymptotics.isBigO_refl logN atTop).trans_le ?_
    intro horizon
    have hn_one : 1 <= (((horizon + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
    have hsqrt_one : 1 <= sqrtN horizon := by
      dsimp [sqrtN]
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hn_one
    have hlog : 0 <= logN horizon := by
      dsimp [logN]
      exact Real.log_nonneg hn_one
    rw [Real.norm_eq_abs, abs_of_nonneg hlog,
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hlog)]
    nlinarith
  have hforced :
      (fun horizon : Nat =>
        ((Nat.log2 horizon + 1 : Nat) : Real) *
          (2 * S * Real.sqrt L2)) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) := by
    have hforced' :=
      (hforcedLog.const_mul_left (2 * S * Real.sqrt L2)).trans hlogScale
    simpa [mul_comm] using hforced'
  have htelescoping :
      (fun horizon : Nat =>
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2) =O[atTop]
        (fun horizon => sqrtN horizon * logN horizon) := by
    simpa [sqrtN, logN] using
      telescopingHighProbabilityPseudoRegretBound_isBigO_sqrt_mul_log
        (Feature := Feature) R delta hdelta
        lambda hlambda S L2 hL2
  simpa [
    powerOfTwoForcedScalarHighProbabilityPseudoRegretBound,
    sqrtN,
    logN] using hforced.add htelescoping

/-- Named all-horizon violation event for the exact scalar asymptotic budget. -/
noncomputable def
    powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory | exists horizon,
    powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 <
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory}

/-- The asymptotic wrapper uses exactly the compiled scalar violation event. -/
theorem
    powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet_eq_scalar
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K) :
    powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best =
      powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretScalarAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best := by
  rfl

/--
Complete one-policy asymptotic high-probability theorem: the exact scalar
budget has the displayed fixed-model Big-O rate, complete pseudo-regret is
nonnegative, and the unchanged all-horizon violation event has probability at
most `delta`.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_asymptoticRate_nonneg_and_allHorizon_tail_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    ((fun horizon : Nat =>
      powerOfTwoForcedScalarHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2) =O[atTop]
      (fun horizon : Nat =>
        Real.sqrt (((horizon + 1 : Nat) : Real)) *
          Real.log (((horizon + 1 : Nat) : Real)))) ∧
      (forall horizon trajectory,
        0 <= canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory) ∧
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best) <=
        ENNReal.ofReal delta := by
  have hrate :=
    powerOfTwoForcedScalarHighProbabilityPseudoRegretBound_isBigO_sqrt_mul_log
      (Feature := Feature) R delta hdelta
      lambda hlambda S L2 hL2
  have htail :=
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_scalarAllHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS forcedAction environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
  refine ⟨hrate, htail.1, ?_⟩
  rw [
    powerOfTwoForcedCanonicalAsymptoticHighProbabilityPseudoRegretAllHorizonViolationSet_eq_scalar]
  exact htail.2

end BanditRLProof.OFUL
