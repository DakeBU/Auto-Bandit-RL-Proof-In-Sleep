import BanditRLProof.TsallisSqrtScheduleSelfBoundingRefinedScalar

/-!
# Refined square-root schedule tuning transport

This module transports the coefficient-aware scalar variables into the actual
finite-arm square-root schedule.  In particular, it identifies the continuous
floor threshold exactly as `2 * (T + 1) / beta`.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

theorem sum_one_div_lambda_mul_eq_div
    {Action : Type u} [DecidableEq Action]
    (actions : Finset Action) (gap : Action -> Real)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (hgap : ∀ action ∈ actions, gap action ≠ 0) :
    actions.sum (fun action => 1 / (lambda * gap action)) =
      actions.sum (fun action => 1 / gap action) / lambda := by
  calc
    actions.sum (fun action => 1 / (lambda * gap action)) =
        actions.sum (fun action => (1 / gap action) / lambda) := by
      apply Finset.sum_congr rfl
      intro action haction
      field_simp [hlambda, hgap action haction]
    _ = actions.sum (fun action => 1 / gap action) / lambda := by
      rw [Finset.sum_div]

/-- With the coefficient-aware alpha/lambda change of variables, the actual
continuous threshold used by the generated theorem is exactly
`2 * (horizon + 1) / beta`. -/
theorem sampledScheduledHalfTsallisSelfBoundingThreshold_refinedLocalLambda_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action}
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (horizon : Nat) (beta : Real)
    (hbetaLower : 2 <= beta)
    (hbetaUpper :
      beta <=
        (2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real))) /
          (25 * ((arms.erase best).sum
            (fun action => 1 / gap action)) ^ 2)) :
    sampledScheduledHalfTsallisSelfBoundingThreshold arms best gap
        (refinedLocalLambda
          (2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real)))
          ((arms.erase best).sum (fun action => 1 / gap action)) beta) =
      (2 * (((horizon + 1 : Nat) : Real))) / beta := by
  let actions := arms.erase best
  let card : Real := actions.card
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum (fun action => 1 / gap action)
  let scale := 2 * card * horizonMass
  let alpha := refinedLocalAlpha scale reciprocalGap beta
  let lambda := refinedLocalLambda scale reciprocalGap beta
  have hcard : 0 < card := by
    dsimp [card, actions]
    exact_mod_cast hsuboptimal.card_pos
  have hhorizonMass : 0 < horizonMass := by
    dsimp [horizonMass]
    positivity
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap, actions]
    exact sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal gap hgap
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hbetaPos : 0 < beta := zero_lt_two.trans_le hbetaLower
  have hbetaUpper' : beta <= scale / (25 * reciprocalGap ^ 2) := by
    simpa [scale, card, horizonMass, reciprocalGap, actions] using hbetaUpper
  have hlambda : lambda ∈ Set.Ioc (0 : Real) 1 := by
    exact refinedLocalLambda_mem_Ioc scale reciprocalGap beta
      hscale hreciprocalGap hbetaPos hbetaUpper'
  have halphaPos : 0 < alpha := by
    exact refinedLocalAlpha_pos scale reciprocalGap beta
      hscale hreciprocalGap hbetaPos
  have halphaLe : alpha <= 1 := by
    exact refinedLocalAlpha_le_one scale reciprocalGap beta
      hscale hreciprocalGap hbetaUpper'
  have halphaLtTwo : alpha < 2 := by linarith
  have halphaSq : alpha ^ 2 = 25 * reciprocalGap ^ 2 * beta / scale := by
    exact refinedLocalAlpha_sq scale reciprocalGap beta hscale hbetaPos.le
  have hsqrtCardPos : 0 < Real.sqrt card := Real.sqrt_pos.2 hcard
  have hsqrtCardSq : Real.sqrt card ^ 2 = card := Real.sq_sqrt hcard.le
  have hsum :
      actions.sum (fun action => 1 / (lambda * gap action)) =
        reciprocalGap / lambda := by
    exact sum_one_div_lambda_mul_eq_div actions gap lambda
      (ne_of_gt hlambda.1) (fun action haction => ne_of_gt (hgap action haction))
  have honeAdd : 1 + lambda = 2 / (2 - alpha) := by
    exact one_add_refinedLocalLambda_eq scale reciprocalGap beta halphaLtTwo
  have halphaRelation : 2 * lambda / (1 + lambda) = alpha := by
    exact two_mul_refinedLocalLambda_div_one_add_eq_alpha
      scale reciprocalGap beta halphaLtTwo
  have hratio : (1 + lambda) / lambda = 2 / alpha := by
    have hlambdaNe : lambda ≠ 0 := ne_of_gt hlambda.1
    have halphaNe : alpha ≠ 0 := ne_of_gt halphaPos
    have honeAddPos : 0 < 1 + lambda := by linarith [hlambda.1]
    field_simp [hlambdaNe, halphaNe, ne_of_gt honeAddPos] at halphaRelation ⊢
    nlinarith
  have hinside :
      5 * (1 + lambda) * (reciprocalGap / lambda) /
          (2 * Real.sqrt card) =
        5 * reciprocalGap / (alpha * Real.sqrt card) := by
    rw [div_eq_mul_inv (reciprocalGap) lambda]
    calc
      5 * (1 + lambda) * (reciprocalGap * lambda⁻¹) /
          (2 * Real.sqrt card) =
          (5 * reciprocalGap / (2 * Real.sqrt card)) *
            ((1 + lambda) / lambda) := by ring
      _ = (5 * reciprocalGap / (2 * Real.sqrt card)) *
            (2 / alpha) := by rw [hratio]
      _ = 5 * reciprocalGap / (alpha * Real.sqrt card) := by
        field_simp [ne_of_gt halphaPos, ne_of_gt hsqrtCardPos]
  have halphaSqMul :
      alpha ^ 2 * (2 * card * horizonMass) =
        25 * reciprocalGap ^ 2 * beta := by
    have := (eq_div_iff (ne_of_gt hscale)).1 halphaSq
    simpa [scale, mul_assoc, mul_left_comm, mul_comm] using this
  have hthresholdAlgebra :
      (5 * reciprocalGap / (alpha * Real.sqrt card)) ^ 2 =
        2 * horizonMass / beta := by
    field_simp [ne_of_gt halphaPos, ne_of_gt hsqrtCardPos,
      ne_of_gt hbetaPos]
    rw [hsqrtCardSq]
    nlinarith [halphaSqMul]
  unfold sampledScheduledHalfTsallisSelfBoundingThreshold
  dsimp only
  change
    (5 * (1 + lambda) *
        actions.sum (fun action => 1 / (lambda * gap action)) /
      (2 * Real.sqrt card)) ^ 2 = 2 * horizonMass / beta
  rw [hsum, hinside]
  exact hthresholdAlgebra

/-- The generated-regret scalar bound after substituting the coefficient-aware
beta-dependent learning-rate multiplier. -/
noncomputable def refinedLocalTunedRegretBound
    (scale horizonMass reciprocalGap corruption beta : Real) : Real :=
  let lambda := refinedLocalLambda scale reciprocalGap beta
  let amplitude := 5 * (1 + lambda)
  (1 + lambda) * ((1 + Real.log horizonMass) / 2) +
    lambda * corruption + amplitude ^ 2 * (reciprocalGap / lambda) +
    (amplitude ^ 2 / 4 * (reciprocalGap / lambda)) * Real.log beta

/-- The Lambert-free explicit estimate for the local tuned scalar bound. -/
theorem refinedLocalTunedRegretBound_le_explicit
    (scale horizonMass reciprocalGap corruption beta : Real)
    (hscale : 0 < scale) (hhorizonMass : 1 <= horizonMass)
    (hreciprocalGap : 0 < reciprocalGap)
    (hcorruption : 0 < corruption) (hbeta : 1 <= beta)
    (hbetaUpper : beta <= scale / (25 * reciprocalGap ^ 2))
    (hcorruptionUpper : corruption * reciprocalGap <= scale)
    (hroot : refinedLocalBetaEquation
      scale reciprocalGap corruption beta = 0) :
    refinedLocalTunedRegretBound
        scale horizonMass reciprocalGap corruption beta <=
      1 + Real.log horizonMass +
        10 * Real.sqrt (corruption * reciprocalGap) *
          (2 + Real.sqrt
            (Real.log (scale / (corruption * reciprocalGap)) + 1)) := by
  let alpha := refinedLocalAlpha scale reciprocalGap beta
  let lambda := refinedLocalLambda scale reciprocalGap beta
  let weight := corruption * reciprocalGap / scale * beta
  let logRadius := Real.log (scale / (corruption * reciprocalGap)) + 1
  have hbetaPos : 0 < beta := zero_lt_one.trans_le hbeta
  have halphaPos : 0 < alpha := by
    exact refinedLocalAlpha_pos scale reciprocalGap beta
      hscale hreciprocalGap hbetaPos
  have halphaLe : alpha <= 1 := by
    exact refinedLocalAlpha_le_one scale reciprocalGap beta
      hscale hreciprocalGap hbetaUpper
  have halphaLtTwo : alpha < 2 := by linarith
  have hdenomPos : 0 < 2 - alpha := by linarith
  have hlambda : lambda ∈ Set.Ioc (0 : Real) 1 := by
    exact refinedLocalLambda_mem_Ioc scale reciprocalGap beta
      hscale hreciprocalGap hbetaPos hbetaUpper
  have honeAdd : 1 + lambda = 2 / (2 - alpha) := by
    exact one_add_refinedLocalLambda_eq scale reciprocalGap beta halphaLtTwo
  have hweightEq : weight = Real.log beta + 2 := by
    dsimp [weight]
    unfold refinedLocalBetaEquation at hroot
    linarith
  have hweightOne : 1 <= weight := by
    have hlogBeta : 0 <= Real.log beta := Real.log_nonneg hbeta
    linarith
  have hweightPos : 0 < weight := zero_lt_one.trans_le hweightOne
  have hweightBounds := refinedLocalBetaWeight_bounds_of_eq_zero
    scale reciprocalGap corruption beta hscale hreciprocalGap hcorruption
      hbeta hcorruptionUpper hroot
  have hweightUpper :
      weight <= (1 + Real.sqrt logRadius) ^ 2 := by
    simpa [weight, logRadius] using hweightBounds.2
  have halphaSq :
      alpha ^ 2 = 25 * reciprocalGap ^ 2 * beta / scale := by
    exact refinedLocalAlpha_sq scale reciprocalGap beta hscale hbetaPos.le
  have hcorruptionAlphaSq :
      corruption * alpha ^ 2 = 25 * reciprocalGap * weight := by
    dsimp [weight]
    rw [halphaSq]
    field_simp [ne_of_gt hscale]
  have hlogBetaEq : Real.log beta = weight - 2 := by linarith
  have hscalarEq :
      lambda * corruption +
          (5 * (1 + lambda)) ^ 2 * (reciprocalGap / lambda) +
          ((5 * (1 + lambda)) ^ 2 / 4 *
              (reciprocalGap / lambda)) * Real.log beta =
        50 * reciprocalGap * (weight + 1) /
          (alpha * (2 - alpha)) := by
    have hlambdaEq : lambda = alpha / (2 - alpha) := by rfl
    rw [honeAdd, hlambdaEq, hlogBetaEq]
    field_simp [ne_of_gt halphaPos, ne_of_gt hdenomPos]
    nlinarith [hcorruptionAlphaSq]
  have hbase :
      (1 + lambda) * ((1 + Real.log horizonMass) / 2) <=
        1 + Real.log horizonMass := by
    have hlogNonneg : 0 <= Real.log horizonMass :=
      Real.log_nonneg hhorizonMass
    nlinarith [hlambda.2]
  have hscalarDenom :
      50 * reciprocalGap * (weight + 1) /
          (alpha * (2 - alpha)) <=
        50 * reciprocalGap * (weight + 1) / alpha := by
    have hnumerator : 0 <= 50 * reciprocalGap * (weight + 1) := by positivity
    have halphaDenom : alpha <= alpha * (2 - alpha) := by
      nlinarith [mul_nonneg halphaPos.le (sub_nonneg.2 halphaLe)]
    exact div_le_div_of_nonneg_left hnumerator halphaPos halphaDenom
  have hproductPos : 0 < corruption * reciprocalGap :=
    mul_pos hcorruption hreciprocalGap
  have hsqrtProductPos : 0 < Real.sqrt (corruption * reciprocalGap) :=
    Real.sqrt_pos.2 hproductPos
  have hsqrtWeightPos : 0 < Real.sqrt weight := Real.sqrt_pos.2 hweightPos
  have hsqrtWeightOne : 1 <= Real.sqrt weight :=
    Real.one_le_sqrt.mpr hweightOne
  have halphaSqrtProduct :
      alpha * Real.sqrt (corruption * reciprocalGap) =
        5 * reciprocalGap * Real.sqrt weight := by
    have hsqrtProductSq := Real.sq_sqrt hproductPos.le
    have hsqrtWeightSq := Real.sq_sqrt hweightPos.le
    have hleftNonneg :
        0 <= alpha * Real.sqrt (corruption * reciprocalGap) := by positivity
    have hrightNonneg :
        0 <= 5 * reciprocalGap * Real.sqrt weight := by positivity
    have hsquares :
        (alpha * Real.sqrt (corruption * reciprocalGap)) ^ 2 =
          (5 * reciprocalGap * Real.sqrt weight) ^ 2 := by
      calc
        (alpha * Real.sqrt (corruption * reciprocalGap)) ^ 2 =
            alpha ^ 2 * (corruption * reciprocalGap) := by
          rw [mul_pow, hsqrtProductSq]
        _ = (corruption * alpha ^ 2) * reciprocalGap := by ring
        _ = (25 * reciprocalGap * weight) * reciprocalGap := by
          rw [hcorruptionAlphaSq]
        _ = (5 * reciprocalGap * Real.sqrt weight) ^ 2 := by
          rw [mul_pow, mul_pow, hsqrtWeightSq]
          ring
    exact (sq_eq_sq₀ hleftNonneg hrightNonneg).1 hsquares
  have hscalarSqrtEq :
      50 * reciprocalGap * (weight + 1) / alpha =
        10 * Real.sqrt (corruption * reciprocalGap) *
          ((weight + 1) / Real.sqrt weight) := by
    apply (div_eq_iff (ne_of_gt halphaPos)).2
    calc
      50 * reciprocalGap * (weight + 1) =
          10 * (weight + 1) *
            (5 * reciprocalGap * Real.sqrt weight) /
              Real.sqrt weight := by
        field_simp [ne_of_gt hsqrtWeightPos]
        norm_num
      _ = 10 * (weight + 1) *
            (alpha * Real.sqrt (corruption * reciprocalGap)) /
              Real.sqrt weight := by rw [halphaSqrtProduct]
      _ = (10 * Real.sqrt (corruption * reciprocalGap) *
            ((weight + 1) / Real.sqrt weight)) * alpha := by
        field_simp [ne_of_gt hsqrtWeightPos]
  have hweightRatioEq :
      (weight + 1) / Real.sqrt weight =
        Real.sqrt weight + 1 / Real.sqrt weight := by
    rw [add_div]
    congr 1
    apply (div_eq_iff (ne_of_gt hsqrtWeightPos)).2
    simpa [pow_two] using (Real.sq_sqrt hweightPos.le).symm
  have hinvSqrtWeight : 1 / Real.sqrt weight <= 1 := by
    exact (div_le_one hsqrtWeightPos).2 hsqrtWeightOne
  have hlogRadiusNonneg : 0 <= logRadius := by
    have hproductPos' : 0 < corruption * reciprocalGap := hproductPos
    have hratioOne : 1 <= scale / (corruption * reciprocalGap) := by
      apply (le_div_iff₀ hproductPos').2
      simpa using hcorruptionUpper
    have := Real.log_nonneg hratioOne
    dsimp [logRadius]
    linarith
  have hsqrtWeightUpper :
      Real.sqrt weight <= 1 + Real.sqrt logRadius := by
    have hrightNonneg : 0 <= 1 + Real.sqrt logRadius := by positivity
    rw [← Real.sqrt_sq hrightNonneg]
    exact Real.sqrt_le_sqrt hweightUpper
  have hratioUpper :
      (weight + 1) / Real.sqrt weight <=
        2 + Real.sqrt logRadius := by
    rw [hweightRatioEq]
    linarith
  unfold refinedLocalTunedRegretBound
  dsimp only
  change
    (1 + lambda) * ((1 + Real.log horizonMass) / 2) +
        lambda * corruption +
      (5 * (1 + lambda)) ^ 2 * (reciprocalGap / lambda) +
      ((5 * (1 + lambda)) ^ 2 / 4 *
        (reciprocalGap / lambda)) * Real.log beta <= _
  calc
    (1 + lambda) * ((1 + Real.log horizonMass) / 2) +
          lambda * corruption +
        (5 * (1 + lambda)) ^ 2 * (reciprocalGap / lambda) +
        ((5 * (1 + lambda)) ^ 2 / 4 *
          (reciprocalGap / lambda)) * Real.log beta =
        (1 + lambda) * ((1 + Real.log horizonMass) / 2) +
          (lambda * corruption +
            (5 * (1 + lambda)) ^ 2 * (reciprocalGap / lambda) +
            ((5 * (1 + lambda)) ^ 2 / 4 *
              (reciprocalGap / lambda)) * Real.log beta) := by ring
    _ = (1 + lambda) * ((1 + Real.log horizonMass) / 2) +
        50 * reciprocalGap * (weight + 1) /
          (alpha * (2 - alpha)) := by rw [hscalarEq]
    _ <=
        1 + Real.log horizonMass +
          50 * reciprocalGap * (weight + 1) / alpha :=
      add_le_add hbase hscalarDenom
    _ = 1 + Real.log horizonMass +
          10 * Real.sqrt (corruption * reciprocalGap) *
            ((weight + 1) / Real.sqrt weight) := by rw [hscalarSqrtEq]
    _ <= 1 + Real.log horizonMass +
          10 * Real.sqrt (corruption * reciprocalGap) *
            (2 + Real.sqrt logRadius) := by gcongr
    _ = _ := by rfl

/-- The coefficient-aware scalar root now drives the actual generated theorem:
it constructs the beta-dependent lambda, discharges the floor-threshold window,
and rewrites the logarithmic tail as `log beta`. -/
theorem exists_integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedLocalTuned
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption : Real) (hcorruption : 0 < corruption)
    (hscalarLower :
      2 <=
        (2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real))) /
          (25 * ((arms.erase best).sum
            (fun action => 1 / gap action)) ^ 2))
    (hscalarThresholdOne :
      (2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real))) /
          (25 * ((arms.erase best).sum
            (fun action => 1 / gap action)) ^ 2) <=
        2 * (((horizon + 1 : Nat) : Real)))
    (hcorruptionUpper :
      2 * (corruption *
        (arms.erase best).sum (fun action => 1 / gap action)) <=
          2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real)))
    (hcorruptionLower :
      25 * ((arms.erase best).sum (fun action => 1 / gap action)) *
          (Real.log
              ((2 * ((arms.erase best).card : Real) *
                  (((horizon + 1 : Nat) : Real))) /
                (25 * ((arms.erase best).sum
                  (fun action => 1 / gap action)) ^ 2)) + 2) <=
        corruption)
    (hselfBounding :
      let selector :=
        canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
      let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms sampledScheduledHalfTsallisSqrtSchedule
          selector.finiteHistory loss.environment
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms sampledScheduledHalfTsallisSqrtSchedule
                t action)) - corruption <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
            (pointMass best) horizon)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment
    let reciprocalGap :=
      (arms.erase best).sum (fun action => 1 / gap action)
    let horizonMass : Real := ((horizon + 1 : Nat) : Real)
    let scale := 2 * ((arms.erase best).card : Real) * horizonMass
    exists beta,
      beta ∈ Set.Icc 2 (scale / (25 * reciprocalGap ^ 2)) ∧
        refinedLocalBetaEquation scale reciprocalGap corruption beta = 0 ∧
        let weight := corruption * reciprocalGap / scale * beta
        1 <= weight ∧
          weight <=
            (1 + Real.sqrt
              (Real.log (scale / (corruption * reciprocalGap)) + 1)) ^ 2 ∧
        refinedLocalLambda scale reciprocalGap beta ∈ Set.Ioc (0 : Real) 1 ∧
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
            arms harms sampledScheduledHalfTsallisSqrtSchedule loss
              (pointMass best) horizon) <=
          refinedLocalTunedRegretBound
            scale horizonMass reciprocalGap corruption beta := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let actions := arms.erase best
  let reciprocalGap := actions.sum (fun action => 1 / gap action)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let scale := 2 * (actions.card : Real) * horizonMass
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap, actions]
    exact sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal gap hgap
  have hhorizonMass : 0 < horizonMass := by
    dsimp [horizonMass]
    positivity
  have hcard : 0 < (actions.card : Real) := by
    dsimp [actions]
    exact_mod_cast hsuboptimal.card_pos
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hscalarLower' : 2 <= scale / (25 * reciprocalGap ^ 2) := by
    simpa [scale, reciprocalGap, horizonMass, actions] using hscalarLower
  have hscalarThresholdOne' :
      scale / (25 * reciprocalGap ^ 2) <= 2 * horizonMass := by
    simpa [scale, reciprocalGap, horizonMass, actions] using
      hscalarThresholdOne
  have hcorruptionUpper' : 2 * (corruption * reciprocalGap) <= scale := by
    simpa [scale, reciprocalGap, horizonMass, actions] using hcorruptionUpper
  have hcorruptionLower' :
      25 * reciprocalGap *
          (Real.log (scale / (25 * reciprocalGap ^ 2)) + 2) <=
        corruption := by
    simpa [scale, reciprocalGap, horizonMass, actions] using hcorruptionLower
  rcases exists_refinedLocalBetaEquation_eq_zero_and_weight_bounds
      scale reciprocalGap corruption hscale hreciprocalGap hcorruption
        hscalarLower' hcorruptionUpper' hcorruptionLower' with
    ⟨beta, hbeta, hroot, hweight⟩
  let lambda := refinedLocalLambda scale reciprocalGap beta
  have hbetaPos : 0 < beta := zero_lt_two.trans_le hbeta.1
  have hlambda : lambda ∈ Set.Ioc (0 : Real) 1 := by
    exact refinedLocalLambda_mem_Ioc scale reciprocalGap beta
      hscale hreciprocalGap hbetaPos hbeta.2
  have hthresholdEq :
      sampledScheduledHalfTsallisSelfBoundingThreshold arms best gap lambda =
        2 * horizonMass / beta := by
    simpa [lambda, scale, reciprocalGap, horizonMass, actions] using
      sampledScheduledHalfTsallisSelfBoundingThreshold_refinedLocalLambda_eq
        arms gap hsuboptimal hgap horizon beta hbeta.1
          (by simpa [scale, reciprocalGap, horizonMass, actions] using hbeta.2)
  have hbetaHorizon : beta <= 2 * horizonMass :=
    hbeta.2.trans hscalarThresholdOne'
  have hthresholdOne :
      1 <= sampledScheduledHalfTsallisSelfBoundingThreshold
        arms best gap lambda := by
    rw [hthresholdEq]
    exact (le_div_iff₀ hbetaPos).2 (by simpa using hbetaHorizon)
  have hthresholdHorizon :
      sampledScheduledHalfTsallisSelfBoundingThreshold
          arms best gap lambda <= horizonMass := by
    rw [hthresholdEq]
    rw [div_le_iff₀ hbetaPos]
    have hmul := mul_le_mul_of_nonneg_left hbeta.1 hhorizonMass.le
    nlinarith
  have hsum :
      actions.sum (fun action => 1 / (lambda * gap action)) =
        reciprocalGap / lambda := by
    exact sum_one_div_lambda_mul_eq_div actions gap lambda
      (ne_of_gt hlambda.1) (fun action haction => ne_of_gt (hgap action haction))
  have hlogRatio :
      Real.log
          ((2 * horizonMass) /
            sampledScheduledHalfTsallisSelfBoundingThreshold
              arms best gap lambda) =
        Real.log beta := by
    rw [hthresholdEq]
    congr 1
    field_simp [ne_of_gt hhorizonMass, ne_of_gt hbetaPos]
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingFloorCutoff
      prior arms harms loss hbest horizon gap hsuboptimal hgap
        corruption lambda hlambda hthresholdOne
          (by simpa [horizonMass] using hthresholdHorizon)
          (by simpa [selector, mu] using hselfBounding)
  dsimp only at hroute
  have hbound :
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
            (pointMass best) horizon) <=
        refinedLocalTunedRegretBound
          scale horizonMass reciprocalGap corruption beta := by
    rw [show (arms.erase best) = actions by rfl, hsum, hlogRatio] at hroute
    simpa [refinedLocalTunedRegretBound, lambda, horizonMass,
      reciprocalGap, actions, mu, selector] using hroute
  exact ⟨beta, hbeta, hroot, hweight.1, hweight.2, hlambda, hbound⟩

/-- The coefficient-aware generated route with the auxiliary root eliminated.
The constants reflect the local floor theorem's amplitude `5 * (1 + lambda)`;
this is intentionally not presented as the paper's sharper constant. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedLocalExplicit
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption : Real) (hcorruption : 0 < corruption)
    (hscalarLower :
      2 <=
        (2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real))) /
          (25 * ((arms.erase best).sum
            (fun action => 1 / gap action)) ^ 2))
    (hscalarThresholdOne :
      (2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real))) /
          (25 * ((arms.erase best).sum
            (fun action => 1 / gap action)) ^ 2) <=
        2 * (((horizon + 1 : Nat) : Real)))
    (hcorruptionUpper :
      2 * (corruption *
        (arms.erase best).sum (fun action => 1 / gap action)) <=
          2 * ((arms.erase best).card : Real) *
            (((horizon + 1 : Nat) : Real)))
    (hcorruptionLower :
      25 * ((arms.erase best).sum (fun action => 1 / gap action)) *
          (Real.log
              ((2 * ((arms.erase best).card : Real) *
                  (((horizon + 1 : Nat) : Real))) /
                (25 * ((arms.erase best).sum
                  (fun action => 1 / gap action)) ^ 2)) + 2) <=
        corruption)
    (hselfBounding :
      let selector :=
        canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
      let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms sampledScheduledHalfTsallisSqrtSchedule
          selector.finiteHistory loss.environment
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms sampledScheduledHalfTsallisSqrtSchedule
                t action)) - corruption <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
            (pointMass best) horizon)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment
    let reciprocalGap :=
      (arms.erase best).sum (fun action => 1 / gap action)
    let horizonMass : Real := ((horizon + 1 : Nat) : Real)
    let scale := 2 * ((arms.erase best).card : Real) * horizonMass
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      1 + Real.log horizonMass +
        10 * Real.sqrt (corruption * reciprocalGap) *
          (2 + Real.sqrt
            (Real.log (scale / (corruption * reciprocalGap)) + 1)) := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let reciprocalGap :=
    (arms.erase best).sum (fun action => 1 / gap action)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let scale := 2 * ((arms.erase best).card : Real) * horizonMass
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap]
    exact sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal gap hgap
  have hhorizonMass : 1 <= horizonMass := by
    dsimp [horizonMass]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
  have hcard : 0 < ((arms.erase best).card : Real) := by
    exact_mod_cast hsuboptimal.card_pos
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hcorruptionUpper' :
      2 * (corruption * reciprocalGap) <= scale := by
    simpa [scale, reciprocalGap, horizonMass] using hcorruptionUpper
  have hproductUpper : corruption * reciprocalGap <= scale := by
    linarith
  have hroute :=
    exists_integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedLocalTuned
      prior arms harms loss hbest horizon gap hsuboptimal hgap corruption
        hcorruption hscalarLower hscalarThresholdOne hcorruptionUpper
          hcorruptionLower hselfBounding
  dsimp only at hroute
  rcases hroute with
    ⟨beta, hbeta, hroot, _hweightOne, _hweightUpper, _hlambda, hbound⟩
  exact hbound.trans
    (refinedLocalTunedRegretBound_le_explicit
      scale horizonMass reciprocalGap corruption beta hscale hhorizonMass
        hreciprocalGap hcorruption (by linarith [hbeta.1]) hbeta.2
          hproductUpper hroot)
end Tsallis
end BanditRLProof
