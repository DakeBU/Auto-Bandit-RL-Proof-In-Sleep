import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretRate

/-!
# Closed square-integrable unbounded stopping-time OFUL expected-regret rate

This module proves that the explicit telescoping OFUL budget grows at most
quadratically in the round count. The existing `L2` stopping-time contract
therefore supplies stopped-budget integrability automatically.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

/-- The scalar log-determinant budget is at most linear in the round count. -/
theorem standardScalarLogDetBudget_le_rounds_mul_div
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (rounds : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    standardScalarLogDetBudget (Feature := Feature) lambda rounds L2 <=
      (rounds : Real) * (L2 / lambda) := by
  have hcard_pos : 0 < (Fintype.card Feature : Real) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card Feature)
  have hdenom_pos :
      0 < (Fintype.card Feature : Real) * lambda :=
    mul_pos hcard_pos hlambda
  let x :=
    ((rounds : Real) * L2) /
      ((Fintype.card Feature : Real) * lambda)
  have hx_nonneg : 0 <= x := by
    dsimp only [x]
    positivity
  have hlog : Real.log (1 + x) <= x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
    linarith
  unfold standardScalarLogDetBudget
  change
    (Fintype.card Feature : Real) * Real.log (1 + x) <=
      (rounds : Real) * (L2 / lambda)
  calc
    (Fintype.card Feature : Real) * Real.log (1 + x) <=
        (Fintype.card Feature : Real) * x := by
      exact mul_le_mul_of_nonneg_left hlog hcard_pos.le
    _ = (rounds : Real) * (L2 / lambda) := by
      dsimp only [x]
      field_simp

/--
Parameter-only coefficient in the quadratic envelope for the explicit
telescoping pseudo-regret budget.
-/
noncomputable def telescopingHighProbabilityPseudoRegretQuadraticCoefficient
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S L2 : Real) : Real :=
  standardScalarInitialGapBound S L2 +
    2 *
      (R * Real.sqrt (L2 / lambda + 4 / delta) +
        Real.sqrt lambda * S) *
      Real.sqrt (2 * (L2 / lambda))

/-- The quadratic-envelope coefficient is nonnegative. -/
theorem
    telescopingHighProbabilityPseudoRegretQuadraticCoefficient_nonneg
    {Feature : Type u} [Fintype Feature]
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (hS : 0 <= S)
    (L2 : Real) (hL2 : 0 <= L2) :
    0 <=
      telescopingHighProbabilityPseudoRegretQuadraticCoefficient
        (Feature := Feature) R delta lambda S L2 := by
  unfold telescopingHighProbabilityPseudoRegretQuadraticCoefficient
  unfold standardScalarInitialGapBound
  positivity

/--
The telescoping confidence logarithm is bounded by a parameter-only
coefficient times the square of the round count.
-/
theorem
    telescopingHighProbabilityRegretLogBudget_le_rounds_sq_mul
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (delta : Real) (hdelta : 0 < delta)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda delta horizon L2 <=
      (((horizon + 1 : Nat) : Real) ^ 2) *
        (L2 / lambda + 4 / delta) := by
  let r : Real := ((horizon + 1 : Nat) : Real)
  have hr_one : 1 <= r := by
    dsimp only [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
  have hr_nonneg : 0 <= r := le_trans (by norm_num) hr_one
  have hD_nonneg : 0 <= L2 / lambda := div_nonneg hL2 hlambda.le
  have hdeltaInv_nonneg : 0 <= 4 / delta := by positivity
  have hdet :=
    standardScalarLogDetBudget_le_rounds_mul_div
      (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
  have hdet_sq :
      standardScalarLogDetBudget
          (Feature := Feature) lambda (horizon + 1) L2 <=
        r ^ 2 * (L2 / lambda) := by
    calc
      standardScalarLogDetBudget
          (Feature := Feature) lambda (horizon + 1) L2 <=
          r * (L2 / lambda) := by simpa [r] using hdet
      _ <= r ^ 2 * (L2 / lambda) := by
        apply mul_le_mul_of_nonneg_right _ hD_nonneg
        nlinarith
  let ratio : Real :=
    ((((horizon + 1 : Nat) : Real) *
        ((horizon + 2 : Nat) : Real)) / delta)
  have hratio_pos : 0 < ratio := by
    dsimp only [ratio]
    positivity
  have hlog_ratio : Real.log ratio <= ratio := by
    exact (Real.log_le_sub_one_of_pos hratio_pos).trans (by linarith)
  have hsucc_le : (((horizon + 2 : Nat) : Real)) <= 2 * r := by
    have hsucc_nat : horizon + 2 <= 2 * (horizon + 1) := by omega
    dsimp only [r]
    exact_mod_cast hsucc_nat
  have hratio_le :
      ratio <= 2 * r ^ 2 / delta := by
    dsimp only [ratio]
    rw [div_le_div_iff_of_pos_right hdelta]
    calc
      (((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) <=
          r * (2 * r) := by
        exact mul_le_mul_of_nonneg_left hsucc_le hr_nonneg
      _ = 2 * r ^ 2 := by ring
  have hlog_term :
      2 * Real.log ratio <= r ^ 2 * (4 / delta) := by
    calc
      2 * Real.log ratio <= 2 * ratio := by linarith
      _ <= 2 * (2 * r ^ 2 / delta) := by linarith
      _ = r ^ 2 * (4 / delta) := by ring
  unfold telescopingHighProbabilityRegretLogBudget
  change
    standardScalarLogDetBudget
          (Feature := Feature) lambda (horizon + 1) L2 +
        2 * Real.log ratio <=
      r ^ 2 * (L2 / lambda + 4 / delta)
  calc
    standardScalarLogDetBudget
          (Feature := Feature) lambda (horizon + 1) L2 +
        2 * Real.log ratio <=
        r ^ 2 * (L2 / lambda) + r ^ 2 * (4 / delta) := by
      exact add_le_add hdet_sq hlog_term
    _ = r ^ 2 * (L2 / lambda + 4 / delta) := by ring

/--
The explicit telescoping pseudo-regret budget grows at most quadratically in
the round count.
-/
theorem
    telescopingHighProbabilityPseudoRegretBound_le_rounds_sq_mul_coefficient
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 <=
      (((horizon + 1 : Nat) : Real) ^ 2) *
        telescopingHighProbabilityPseudoRegretQuadraticCoefficient
          (Feature := Feature) R delta lambda S L2 := by
  let r : Real := ((horizon + 1 : Nat) : Real)
  let D : Real := L2 / lambda
  let C : Real := D + 4 / delta
  let logBudget :=
    telescopingHighProbabilityRegretLogBudget
      (Feature := Feature) lambda delta horizon L2
  let detBudget :=
    standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2
  let radiusBase :=
    R * Real.sqrt C + Real.sqrt lambda * S
  let widthBase := Real.sqrt (2 * D)
  let initialGap := standardScalarInitialGapBound S L2
  have hr_one : 1 <= r := by
    dsimp only [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
  have hr_nonneg : 0 <= r := le_trans (by norm_num) hr_one
  have hD_nonneg : 0 <= D := by
    dsimp only [D]
    exact div_nonneg hL2 hlambda.le
  have hC_nonneg : 0 <= C := by
    dsimp only [C]
    positivity
  have hlogBudget_nonneg : 0 <= logBudget := by
    dsimp only [logBudget]
    exact
      telescopingHighProbabilityRegretLogBudget_nonneg
        (Feature := Feature) lambda hlambda delta hdelta hdelta_one
        horizon L2 hL2
  have hdetBudget_nonneg : 0 <= detBudget := by
    dsimp only [detBudget]
    exact
      standardScalarLogDetBudget_nonneg
        (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
  have hlogBudget :
      logBudget <= r ^ 2 * C := by
    dsimp only [logBudget, r, C, D]
    exact
      telescopingHighProbabilityRegretLogBudget_le_rounds_sq_mul
        (Feature := Feature) lambda hlambda delta hdelta horizon L2 hL2
  have hdetBudget :
      detBudget <= r * D := by
    dsimp only [detBudget, r, D]
    exact
      standardScalarLogDetBudget_le_rounds_mul_div
        (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
  have hsqrtLogBudget :
      Real.sqrt logBudget <= r * Real.sqrt C := by
    calc
      Real.sqrt logBudget <= Real.sqrt (r ^ 2 * C) :=
        Real.sqrt_le_sqrt hlogBudget
      _ = Real.sqrt (r ^ 2) * Real.sqrt C := by
        rw [Real.sqrt_mul (sq_nonneg r)]
      _ = r * Real.sqrt C := by rw [Real.sqrt_sq hr_nonneg]
  have hradiusBase_nonneg : 0 <= radiusBase := by
    dsimp only [radiusBase]
    positivity
  have hradius :
      R * Real.sqrt logBudget + Real.sqrt lambda * S <=
        r * radiusBase := by
    calc
      R * Real.sqrt logBudget + Real.sqrt lambda * S <=
          R * (r * Real.sqrt C) + Real.sqrt lambda * S := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsqrtLogBudget hR) le_rfl
      _ <= r * radiusBase := by
        dsimp only [radiusBase]
        have hsqrtLambdaS_nonneg : 0 <= Real.sqrt lambda * S := by
          positivity
        nlinarith
  have hwidth :
      Real.sqrt r * Real.sqrt (2 * detBudget) <=
        r * widthBase := by
    calc
      Real.sqrt r * Real.sqrt (2 * detBudget) <=
          Real.sqrt r * Real.sqrt (2 * (r * D)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt
            (mul_le_mul_of_nonneg_left hdetBudget (by norm_num)))
          (Real.sqrt_nonneg r)
      _ = Real.sqrt r * (Real.sqrt r * Real.sqrt (2 * D)) := by
        rw [show 2 * (r * D) = r * (2 * D) by ring]
        rw [Real.sqrt_mul hr_nonneg]
      _ = r * widthBase := by
        rw [← mul_assoc, Real.mul_self_sqrt hr_nonneg]
  have hinitialGap_nonneg : 0 <= initialGap := by
    dsimp only [initialGap, standardScalarInitialGapBound]
    positivity
  have hinitialGap :
      initialGap <= r ^ 2 * initialGap := by
    calc
      initialGap = 1 * initialGap := by ring
      _ <= r ^ 2 * initialGap := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg r])
          hinitialGap_nonneg
  have hproduct :
      2 *
          (R * Real.sqrt logBudget + Real.sqrt lambda * S) *
          (Real.sqrt r * Real.sqrt (2 * detBudget)) <=
        r ^ 2 * (2 * radiusBase * widthBase) := by
    calc
      2 *
          (R * Real.sqrt logBudget + Real.sqrt lambda * S) *
          (Real.sqrt r * Real.sqrt (2 * detBudget)) <=
          2 * (r * radiusBase) * (r * widthBase) := by
        have hradius_nonneg :
            0 <= R * Real.sqrt logBudget + Real.sqrt lambda * S := by
          positivity
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hradius (by norm_num))
          hwidth
          (mul_nonneg (Real.sqrt_nonneg r)
            (Real.sqrt_nonneg (2 * detBudget)))
          (mul_nonneg (by norm_num)
            (mul_nonneg hr_nonneg hradiusBase_nonneg))
      _ = r ^ 2 * (2 * radiusBase * widthBase) := by ring
  unfold telescopingHighProbabilityPseudoRegretBound
  change
    initialGap +
        2 *
          (R * Real.sqrt logBudget + Real.sqrt lambda * S) *
          (Real.sqrt r * Real.sqrt (2 * detBudget)) <=
      r ^ 2 *
        telescopingHighProbabilityPseudoRegretQuadraticCoefficient
          (Feature := Feature) R delta lambda S L2
  calc
    initialGap +
        2 *
          (R * Real.sqrt logBudget + Real.sqrt lambda * S) *
          (Real.sqrt r * Real.sqrt (2 * detBudget)) <=
        r ^ 2 * initialGap + r ^ 2 * (2 * radiusBase * widthBase) := by
      exact add_le_add hinitialGap hproduct
    _ =
        r ^ 2 *
          telescopingHighProbabilityPseudoRegretQuadraticCoefficient
            (Feature := Feature) R delta lambda S L2 := by
      dsimp only [initialGap, radiusBase, widthBase, C, D]
      unfold telescopingHighProbabilityPseudoRegretQuadraticCoefficient
      ring

/--
Square-integrability of the stopping-time round count automatically makes the
stopped explicit telescoping pseudo-regret budget integrable.
-/
theorem
    integrable_stoppedValue_telescopingHighProbabilityPseudoRegretBound_of_squareIntegrableFiniteStoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (mu : Measure (Nat -> Fin K × Real))
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (hS : 0 <= S)
    (L2 : Real) (hL2 : 0 <= L2)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau) :
    Integrable
      (stoppedValue
        (fun horizon (_trajectory : Nat -> Fin K × Real) =>
          telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S horizon L2)
        tau) mu := by
  let rounds : (Nat -> Fin K × Real) -> Real := fun trajectory =>
    (((tau trajectory).untopA + 1 : Nat) : Real)
  let coefficient :=
    telescopingHighProbabilityPseudoRegretQuadraticCoefficient
      (Feature := Feature) R delta lambda S L2
  have hquadratic :
      Integrable (fun trajectory => rounds trajectory ^ 2) mu := by
    simpa only [rounds] using hstop.memLp_rounds.integrable_sq
  have hdom :
      Integrable
        (fun trajectory => rounds trajectory ^ 2 * coefficient) mu :=
    hquadratic.mul_const coefficient
  apply Integrable.mono' hdom
    (measurable_stoppedValue_telescopingHighProbabilityPseudoRegretBound_of_stoppingTime
      (K := K) (Feature := Feature) R delta lambda S L2 tau htau).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun trajectory => by
    have hbudgetNonneg :=
      telescopingHighProbabilityPseudoRegretBound_nonneg
        (Feature := Feature) R hR delta hdelta hdelta_one
        lambda hlambda S hS (tau trajectory).untopA L2 hL2
    simp only [stoppedValue]
    rw [Real.norm_eq_abs, abs_of_nonneg hbudgetNonneg]
    simpa only [rounds, coefficient] using
      (telescopingHighProbabilityPseudoRegretBound_le_rounds_sq_mul_coefficient
        (Feature := Feature) R hR delta hdelta hdelta_one
        lambda hlambda S hS (tau trajectory).untopA L2 hL2)

/--
Canonical square-integrable unbounded-stopping expected pseudo-regret rate
with stopped-budget integrability discharged automatically.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_integral_stoppedBudget_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime_automaticBudgetIntegrability
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
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
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : SquareIntegrableFiniteStoppingTime
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      tau)
    (roundSecondMoment : Real)
    (hroundSecondMoment :
      integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment)
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        roundSecondMoment) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let stoppedRegret :=
      stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau
    let stoppedBudget :=
      stoppedValue
        (fun horizon (_trajectory : Nat -> Fin K × Real) =>
          telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S horizon L2)
        tau
    let bad :=
      telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau
    0 <= integral mu stoppedRegret ∧
      integral mu stoppedRegret <=
        integral mu stoppedBudget +
          standardScalarInitialGapBound S L2 *
            Real.sqrt roundSecondMoment * Real.sqrt delta ∧
      mu bad <= ENNReal.ofReal delta := by
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R delta S)
      environment
  have hbudgetIntegrable :
      Integrable
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau) mu := by
    exact
      integrable_stoppedValue_telescopingHighProbabilityPseudoRegretBound_of_squareIntegrableFiniteStoppingTime
        (Feature := Feature) mu R hR.le delta hdelta hdelta_one
        lambda hlambda S hS L2 hL2 tau htau hstop
  exact
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_integral_stoppedBudget_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source tau htau hstop
      roundSecondMoment hroundSecondMoment hbudgetIntegrable

end OFUL
end BanditRLProof
