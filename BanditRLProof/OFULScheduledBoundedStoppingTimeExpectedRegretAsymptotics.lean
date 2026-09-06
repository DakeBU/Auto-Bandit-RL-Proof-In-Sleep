import BanditRLProof.OFULExpectedRegretAsymptotics
import BanditRLProof.OFULScheduledBoundedStoppingTimeExpectedRegretRate

/-!
# Asymptotic bounded-stopping-time expected OFUL pseudo-regret

This module upgrades the explicit pointwise expected pseudo-regret bound for
the horizon-indexed telescoping-schedule policy and bounded stopping-time
family to an `IsBigO` statement at `Filter.atTop`.
-/

namespace BanditRLProof.OFUL

open Filter Real MeasureTheory
open scoped Topology

universe u

/--
The additional scheduled confidence logarithm at outer budget
`1 / (T + 1)` is `O(log (T + 1))`.
-/
theorem telescopingStandardExpectedConfidenceLog_isBigO_log_succ :
    (fun horizon : Nat =>
      2 * Real.log
        ((((horizon + 1 : Nat) : Real) ^ 2) *
          ((horizon + 2 : Nat) : Real))) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with horizon hhorizon
  let n : Real := (((horizon + 1 : Nat) : Real))
  have hn_two : 2 <= n := by
    dsimp [n]
    exact_mod_cast Nat.succ_le_succ hhorizon
  have hn_one : 1 <= n := le_trans (by norm_num) hn_two
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn_two
  have hnext :
      (((horizon + 2 : Nat) : Real)) = n + 1 := by
    dsimp [n]
    push_cast
    ring
  rw [hnext]
  change
    ‖2 * Real.log (n ^ 2 * (n + 1))‖ <=
      8 * ‖Real.log n‖
  have hnext_le_sq : n + 1 <= n ^ 2 := by
    nlinarith
  have hlog_next :
      Real.log (n + 1) <= 2 * Real.log n := by
    calc
      Real.log (n + 1) <= Real.log (n ^ 2) :=
        Real.log_le_log (by positivity) hnext_le_sq
      _ = 2 * Real.log n := by
        exact Real.log_pow n 2
  have hlog_n_nonneg : 0 <= Real.log n := Real.log_nonneg hn_one
  have hsquare_one : 1 <= n ^ 2 := by nlinarith
  have hnext_one : 1 <= n + 1 := by linarith
  have hproduct_one : 1 <= n ^ 2 * (n + 1) := by
    simpa only [one_mul] using
      mul_le_mul hsquare_one hnext_one zero_le_one
        (le_trans zero_le_one hsquare_one)
  have hlog_product_nonneg :
      0 <= Real.log (n ^ 2 * (n + 1)) :=
    Real.log_nonneg hproduct_one
  have hlog_product :
      Real.log (n ^ 2 * (n + 1)) =
        2 * Real.log n + Real.log (n + 1) := by
    rw [Real.log_mul (pow_ne_zero _ hn_pos.ne') (by positivity),
      Real.log_pow]
    norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hlog_product_nonneg),
    Real.norm_eq_abs, abs_of_nonneg hlog_n_nonneg, hlog_product]
  nlinarith

/--
The complete scheduled confidence log budget at outer budget
`1 / (T + 1)` is `O(log (T + 1))`.
-/
theorem telescopingStandardExpectedRegretLogBudget_isBigO_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      telescopingStandardExpectedRegretLogBudget
        (Feature := Feature) lambda horizon L2) =O[atTop]
      (fun horizon : Nat =>
        Real.log (((horizon + 1 : Nat) : Real))) := by
  have hdet :=
    standardScalarLogDetBudget_isBigO_log
      (Feature := Feature) lambda hlambda L2 hL2
  simpa [telescopingStandardExpectedRegretLogBudget] using
    hdet.add telescopingStandardExpectedConfidenceLog_isBigO_log_succ

/--
The explicit tuned bounded-stopping-time expected pseudo-regret budget is
`O(sqrt (T + 1) * log (T + 1))`.
-/
theorem
    telescopingStandardExpectedPseudoRegretBound_isBigO_sqrt_mul_log
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (L2 : Real) (hL2 : 0 <= L2) :
    (fun horizon : Nat =>
      telescopingStandardExpectedPseudoRegretBound
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
    telescopingStandardExpectedRegretLogBudget
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
      telescopingStandardExpectedRegretLogBudget_isBigO_log
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
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hlog)]
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
  simp only [telescopingStandardExpectedPseudoRegretBound]
  dsimp [B, C, sqrtN, logN, n]
  ring

/--
For fixed model parameters and any horizon-indexed canonical stopping-time
family bounded pointwise by its horizon, the named expected stopped
pseudo-regret is `O(sqrt (T + 1) * log (T + 1))`.
-/
theorem
    canonicalTelescopingStandardExpectedStoppedPseudoRegret_isBigO_sqrt_mul_log
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
      hK thetaStar actionFeature R S environment)
    (tau : Nat -> (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : forall maxHorizon,
      IsStoppingTime
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (tau maxHorizon))
    (htau_le : forall maxHorizon trajectory,
      tau maxHorizon trajectory <= (maxHorizon : WithTop Nat)) :
    (canonicalTelescopingStandardExpectedStoppedPseudoRegret
      hK lambda thetaStar actionFeature R S environment best tau) =O[atTop]
      (fun horizon : Nat =>
        Real.sqrt (((horizon + 1 : Nat) : Real)) *
          Real.log (((horizon + 1 : Nat) : Real))) := by
  have hbound :=
    telescopingStandardExpectedPseudoRegretBound_isBigO_sqrt_mul_log
      (Feature := Feature) R lambda hlambda S L2 hL2
  rw [Asymptotics.isBigO_iff] at hbound ⊢
  obtain ⟨c, hc⟩ := hbound
  refine ⟨c, ?_⟩
  filter_upwards [hc] with horizon hcbound
  have hpoint :=
    canonicalTelescopingStandardExpectedStoppedPseudoRegret_nonneg_and_le
      hK lambda hlambda thetaStar actionFeature R hR S hS environment
      L2 hL2 hactionFeatureBound hL2lambda best hbest source
      tau htau htau_le horizon
  rw [Real.norm_eq_abs, abs_of_nonneg hpoint.1]
  exact hpoint.2.trans ((le_abs_self _).trans hcbound)

end BanditRLProof.OFUL
