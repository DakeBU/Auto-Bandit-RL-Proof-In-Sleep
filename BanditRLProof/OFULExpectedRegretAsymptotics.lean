import BanditRLProof.OFULExpectedRegretRate
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic OFUL expected pseudo-regret

This module upgrades the explicit finite-window canonical OFUL expected
pseudo-regret theorem to an `IsBigO` statement at `Filter.atTop`. The feature
dimension and model parameters are fixed while the horizon varies.
-/

namespace BanditRLProof.OFUL

open Filter Real MeasureTheory
open scoped Topology

universe u

theorem standardScalarLogDetBudget_isBigO_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      standardScalarLogDetBudget
        (Feature := Feature) lambda (horizon + 1) L2) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) := by
  rw [Asymptotics.isBigO_iff]
  let d : Real := Fintype.card Feature
  let c : Real := L2 / (d * lambda)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card Feature)
  have hc : 0 <= c := div_nonneg hL2 (mul_pos hd hlambda).le
  let n : Nat -> Real := fun horizon => (((horizon + 1 : Nat) : Real))
  have hn_tendsto : Tendsto n atTop atTop := by
    exact (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
  have hlog_tendsto : Tendsto (fun horizon => Real.log (n horizon)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_tendsto
  refine ⟨2 * d, ?_⟩
  filter_upwards
      [hlog_tendsto.eventually (eventually_ge_atTop (Real.log (1 + c))),
       hlog_tendsto.eventually (eventually_ge_atTop 0)]
      with horizon hconst hlog
  have hn_pos : 0 < n horizon := by
    dsimp [n]
    positivity
  have honec_pos : 0 < 1 + c := by linarith
  have harg :
      1 + n horizon * c <= n horizon * (1 + c) := by
    nlinarith [show 1 <= n horizon by
      dsimp [n]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)]
  have hlog_arg :
      Real.log (1 + n horizon * c) <=
        Real.log (n horizon) + Real.log (1 + c) := by
    calc
      Real.log (1 + n horizon * c)
          <= Real.log (n horizon * (1 + c)) :=
        Real.log_le_log (by positivity) harg
      _ = Real.log (n horizon) + Real.log (1 + c) :=
        Real.log_mul hn_pos.ne' honec_pos.ne'
  have hbudget_nonneg :
      0 <= standardScalarLogDetBudget
        (Feature := Feature) lambda (horizon + 1) L2 :=
    standardScalarLogDetBudget_nonneg
      (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
  rw [Real.norm_eq_abs, abs_of_nonneg hbudget_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hlog]
  have hfinal :
      d * Real.log (1 + n horizon * c) <=
        (2 * d) * Real.log (n horizon) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog_arg hd.le]
  simpa [standardScalarLogDetBudget, d, c, n, div_eq_mul_inv, mul_assoc] using hfinal

theorem standardExpectedRegretLogBudget_isBigO_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      standardExpectedRegretLogBudget
        (Feature := Feature) lambda horizon L2) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) := by
  have hdet :=
    standardScalarLogDetBudget_isBigO_log
      (Feature := Feature) lambda hlambda L2 hL2
  have hconfidence :
      (fun horizon : Nat =>
        4 * Real.log (((horizon + 1 : Nat) : Real))) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) :=
    (Asymptotics.isBigO_refl _ _).const_mul_left 4
  simpa [standardExpectedRegretLogBudget] using hdet.add hconfidence

theorem sqrt_log_succ_isBigO_log_succ :
    (fun horizon : Nat =>
      Real.sqrt (Real.log (((horizon + 1 : Nat) : Real)))) =O[atTop]
    (fun horizon : Nat =>
      Real.log (((horizon + 1 : Nat) : Real))) := by
  rw [Asymptotics.isBigO_iff]
  let n : Nat -> Real := fun horizon => (((horizon + 1 : Nat) : Real))
  have hn_tendsto : Tendsto n atTop atTop := by
    exact (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
  have hlog_tendsto : Tendsto (fun horizon => Real.log (n horizon)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_tendsto
  refine ⟨1, ?_⟩
  filter_upwards
      [hlog_tendsto.eventually (eventually_ge_atTop 1)]
      with horizon hlog
  have hsqrt_nonneg :
      0 <= Real.sqrt (Real.log (n horizon)) := Real.sqrt_nonneg _
  change
    |Real.sqrt (Real.log (n horizon))| <=
      1 * |Real.log (n horizon)|
  rw [abs_of_nonneg hsqrt_nonneg,
    abs_of_nonneg (le_trans zero_le_one hlog), one_mul]
  exact Real.sqrt_le_iff.mpr
    ⟨le_trans zero_le_one hlog, by nlinarith⟩

theorem standardExpectedPseudoRegretBound_isBigO_sqrt_mul_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      standardExpectedPseudoRegretBound
        (Feature := Feature) R lambda S horizon L2) =O[atTop]
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
    standardExpectedRegretLogBudget
      (Feature := Feature) lambda horizon L2
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
      standardExpectedRegretLogBudget_isBigO_log
        (Feature := Feature) lambda hlambda L2 hL2
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
      (fun _horizon : Nat => 4 * S * Real.sqrt L2) =o[atTop] logN := by
    change
      (fun _horizon : Nat => 4 * S * Real.sqrt L2) =o[atTop]
        (fun horizon => Real.log (n horizon))
    simpa only [Function.comp_apply] using
      (Real.isLittleO_const_log_atTop
        (c := 4 * S * Real.sqrt L2)).comp_tendsto hn_tendsto
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
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlog)]
    nlinarith
  have hconstant :
      (fun _horizon : Nat => 4 * S * Real.sqrt L2) =O[atTop]
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
  simp only [standardExpectedPseudoRegretBound]
  dsimp [B, C, sqrtN, logN, n]
  ring

noncomputable def canonicalStandardExpectedPseudoRegret
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (best : Fin K)
    (horizon : Nat) : Real :=
  integral
    (Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R
          (1 / (((horizon + 1 : Nat) : Real) ^ 2)) S)
      environment)
    (canonicalHistoryTrajectorySumRangeAllGap
      thetaStar actionFeature horizon (fun _t => best))

theorem canonicalStandardExpectedPseudoRegret_nonneg_and_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    0 <= canonicalStandardExpectedPseudoRegret
      hK lambda thetaStar actionFeature R S environment best horizon ∧
    canonicalStandardExpectedPseudoRegret
        hK lambda thetaStar actionFeature R S environment best horizon <=
      standardExpectedPseudoRegretBound
        (Feature := Feature) R lambda S horizon L2 := by
  simpa [canonicalStandardExpectedPseudoRegret] using
    integral_canonicalHistoryTrajectoryPseudoRegret_nonneg_and_le_explicitStandardExpectedBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR S hS environment
      horizon L2 hL2 hactionFeatureBound hL2lambda best hbest source

theorem canonicalStandardExpectedPseudoRegret_isBigO_sqrt_mul_log
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    (canonicalStandardExpectedPseudoRegret
      hK lambda thetaStar actionFeature R S environment best) =O[atTop]
      (fun horizon : Nat =>
        Real.sqrt (((horizon + 1 : Nat) : Real)) *
          Real.log (((horizon + 1 : Nat) : Real))) := by
  have hbound :=
    standardExpectedPseudoRegretBound_isBigO_sqrt_mul_log
      (Feature := Feature) R lambda hlambda S L2 hL2
  rw [Asymptotics.isBigO_iff] at hbound ⊢
  obtain ⟨c, hc⟩ := hbound
  refine ⟨c, ?_⟩
  filter_upwards [hc] with horizon hcbound
  have hpoint :=
    canonicalStandardExpectedPseudoRegret_nonneg_and_le
      hK lambda hlambda thetaStar actionFeature R hR S hS environment
      horizon L2 hL2 hactionFeatureBound hL2lambda best hbest source
  rw [Real.norm_eq_abs, abs_of_nonneg hpoint.1]
  exact hpoint.2.trans ((le_abs_self _).trans hcbound)

end BanditRLProof.OFUL
