import BanditRLProof.TsallisSelfBoundingBetaRoot

/-!
# Coefficient-aware refined self-bounding scalar tuning

The local refined stability envelope has coefficient `5`.  After the change
of variables used by the square-root schedule, its scalar objective therefore
has a beta equation with offset `2`, rather than the paper's idealized offset
`1`.  This module records the corrected root interval and an elementary root
estimate that does not require Lambert W.
-/

namespace BanditRLProof
namespace Tsallis

open Set

/-- The beta equation produced by the local coefficient-five envelope. -/
noncomputable def refinedLocalBetaEquation
    (scale reciprocalGap corruption beta : Real) : Real :=
  corruption * reciprocalGap / scale * beta - Real.log beta - 2

/-- The local beta equation is continuous on every interval bounded below by
one. -/
theorem continuousOn_refinedLocalBetaEquation
    (scale reciprocalGap corruption upper : Real) :
    ContinuousOn (refinedLocalBetaEquation scale reciprocalGap corruption)
      (Icc 1 upper) := by
  unfold refinedLocalBetaEquation
  apply ContinuousOn.sub
  · apply ContinuousOn.sub
    · fun_prop
    · exact Real.continuousOn_log.mono (by
        intro beta hbeta
        exact ne_of_gt (zero_lt_one.trans_le hbeta.1))
  · exact continuousOn_const

/-- The elementary inequality behind the Lambert-free beta estimate. -/
theorem sq_sqrt_sub_one_le_sub_log_sub_one
    (weight : Real) (hweight : 1 <= weight) :
    (Real.sqrt weight - 1) ^ 2 <=
      weight - Real.log weight - 1 := by
  have hweightNonneg : 0 <= weight := zero_le_one.trans hweight
  have hsqrtPos : 0 < Real.sqrt weight :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le hweight)
  have hlogSqrt := Real.log_le_sub_one_of_pos hsqrtPos
  have hlogSqrtEq :
      Real.log (Real.sqrt weight) = Real.log weight / 2 :=
    Real.log_sqrt hweightNonneg
  rw [hlogSqrtEq] at hlogSqrt
  nlinarith [Real.sq_sqrt hweightNonneg]

/-- A root of the coefficient-five equation admits the same kind of elementary
upper estimate as the paper's Lambert-W expression, with the offset correction
appearing as `+1` under the outer square root. -/
theorem refinedLocalBetaWeight_bounds_of_eq_zero
    (scale reciprocalGap corruption beta : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hcorruption : 0 < corruption) (hbeta : 1 <= beta)
    (hcorruptionUpper : corruption * reciprocalGap <= scale)
    (hroot : refinedLocalBetaEquation
      scale reciprocalGap corruption beta = 0) :
    let weight := corruption * reciprocalGap / scale * beta
    1 <= weight ∧
      weight <=
        (1 + Real.sqrt
          (Real.log (scale / (corruption * reciprocalGap)) + 1)) ^ 2 := by
  dsimp only
  let weight := corruption * reciprocalGap / scale * beta
  let ratio := scale / (corruption * reciprocalGap)
  have hproductPos : 0 < corruption * reciprocalGap :=
    mul_pos hcorruption hreciprocalGap
  have hratioPos : 0 < ratio := by
    dsimp [ratio]
    positivity
  have hratioOne : 1 <= ratio := by
    dsimp [ratio]
    apply (le_div_iff₀ hproductPos).2
    simpa using hcorruptionUpper
  have hlogBetaNonneg : 0 <= Real.log beta := Real.log_nonneg hbeta
  have hweightEq : weight = Real.log beta + 2 := by
    dsimp [weight]
    unfold refinedLocalBetaEquation at hroot
    linarith
  have hweightOne : 1 <= weight := by linarith
  have hweightPos : 0 < weight := zero_lt_one.trans_le hweightOne
  have hbetaEq : beta = ratio * weight := by
    dsimp [ratio, weight]
    field_simp
  have hlogBetaEq :
      Real.log beta = Real.log ratio + Real.log weight := by
    rw [hbetaEq, Real.log_mul (ne_of_gt hratioPos) (ne_of_gt hweightPos)]
  have hidentity :
      weight - Real.log weight - 2 = Real.log ratio := by
    calc
      weight - Real.log weight - 2 =
          Real.log beta - Real.log weight := by linarith
      _ = Real.log ratio := by rw [hlogBetaEq]; ring
  have hlower :=
    sq_sqrt_sub_one_le_sub_log_sub_one weight hweightOne
  have hsquare :
      (Real.sqrt weight - 1) ^ 2 <= Real.log ratio + 1 := by
    linarith
  have hlogRatioNonneg : 0 <= Real.log ratio := Real.log_nonneg hratioOne
  have hsqrtWeightOne : 1 <= Real.sqrt weight := by
    exact Real.one_le_sqrt.mpr hweightOne
  have hsqrtBound :
      Real.sqrt weight - 1 <= Real.sqrt (Real.log ratio + 1) := by
    have hrightNonneg : 0 <= Real.log ratio + 1 := by linarith
    have hsqrtRightSq := Real.sq_sqrt hrightNonneg
    have hleftNonneg : 0 <= Real.sqrt weight - 1 := by linarith
    have hsqrtRightNonneg := Real.sqrt_nonneg (Real.log ratio + 1)
    nlinarith
  have hweightNonneg : 0 <= weight := zero_le_one.trans hweightOne
  have hsqrtWeightSq := Real.sq_sqrt hweightNonneg
  have hfinal :
      weight <=
        (1 + Real.sqrt (Real.log ratio + 1)) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (Real.log ratio + 1)]
  exact ⟨hweightOne, by simpa [ratio] using hfinal⟩

/-- Under the coefficient-aware corruption window, the corrected beta equation
has a root in the interval that corresponds to `alpha` between the local
horizon threshold and one. -/
theorem exists_refinedLocalBetaEquation_eq_zero
    (scale reciprocalGap corruption : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hupper : 2 <= scale / (25 * reciprocalGap ^ 2))
    (hcorruptionUpper : 2 * (corruption * reciprocalGap) <= scale)
    (hcorruptionLower :
      25 * reciprocalGap *
          (Real.log (scale / (25 * reciprocalGap ^ 2)) + 2) <=
        corruption) :
    exists beta,
      beta ∈ Icc 2 (scale / (25 * reciprocalGap ^ 2)) ∧
        refinedLocalBetaEquation
          scale reciprocalGap corruption beta = 0 := by
  let upper := scale / (25 * reciprocalGap ^ 2)
  let g := refinedLocalBetaEquation scale reciprocalGap corruption
  have hgTwo : g 2 <= 0 := by
    have hdiv :
        corruption * reciprocalGap / scale <= 1 / 2 := by
      rw [div_le_iff₀ hscale]
      nlinarith
    have hlogTwo : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [g, refinedLocalBetaEquation]
    nlinarith
  have hgUpper : 0 <= g upper := by
    have hreciprocalGapNe : reciprocalGap ≠ 0 := ne_of_gt hreciprocalGap
    have hscaleNe : scale ≠ 0 := ne_of_gt hscale
    have hnormalize :
        corruption * reciprocalGap / scale * upper =
          corruption / (25 * reciprocalGap) := by
      dsimp [upper]
      field_simp
    have hdenomPos : 0 < 25 * reciprocalGap := by positivity
    have hdiv :
        Real.log upper + 2 <= corruption / (25 * reciprocalGap) := by
      apply (le_div_iff₀ hdenomPos).2
      simpa [upper, mul_assoc, mul_left_comm, mul_comm] using
        hcorruptionLower
    dsimp [g, refinedLocalBetaEquation]
    rw [hnormalize]
    linarith
  have hcontinuous : ContinuousOn g (Icc 2 upper) := by
    exact (continuousOn_refinedLocalBetaEquation
      scale reciprocalGap corruption upper).mono (by
        intro beta hbeta
        exact ⟨one_le_two.trans hbeta.1, hbeta.2⟩)
  have hzero : (0 : Real) ∈ Icc (g 2) (g upper) := ⟨hgTwo, hgUpper⟩
  rcases intermediate_value_Icc hupper hcontinuous hzero with
    ⟨beta, hbeta, hbetaZero⟩
  exact ⟨beta, hbeta, hbetaZero⟩

/-- The coefficient-aware corruption window yields a beta root together with
the elementary quantitative weight estimate needed by the refined regret
route. -/
theorem exists_refinedLocalBetaEquation_eq_zero_and_weight_bounds
    (scale reciprocalGap corruption : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hcorruption : 0 < corruption)
    (hupper : 2 <= scale / (25 * reciprocalGap ^ 2))
    (hcorruptionUpper : 2 * (corruption * reciprocalGap) <= scale)
    (hcorruptionLower :
      25 * reciprocalGap *
          (Real.log (scale / (25 * reciprocalGap ^ 2)) + 2) <=
        corruption) :
    exists beta,
      beta ∈ Icc 2 (scale / (25 * reciprocalGap ^ 2)) ∧
        refinedLocalBetaEquation
          scale reciprocalGap corruption beta = 0 ∧
        let weight := corruption * reciprocalGap / scale * beta
        1 <= weight ∧
          weight <=
            (1 + Real.sqrt
              (Real.log (scale / (corruption * reciprocalGap)) + 1)) ^ 2 := by
  rcases exists_refinedLocalBetaEquation_eq_zero
      scale reciprocalGap corruption hscale hreciprocalGap hupper
        hcorruptionUpper hcorruptionLower with
    ⟨beta, hbeta, hroot⟩
  have hupperSimple : corruption * reciprocalGap <= scale := by linarith
  have hbounds := refinedLocalBetaWeight_bounds_of_eq_zero
    scale reciprocalGap corruption beta hscale hreciprocalGap hcorruption
      (one_le_two.trans hbeta.1) hupperSimple hroot
  exact ⟨beta, hbeta, hroot, hbounds⟩

/-- The coefficient-aware change of variables from beta to alpha. -/
noncomputable def refinedLocalAlpha
    (scale reciprocalGap beta : Real) : Real :=
  Real.sqrt (25 * reciprocalGap ^ 2 * beta / scale)

/-- The inverse of `alpha = 2 * lambda / (1 + lambda)`. -/
noncomputable def refinedLocalLambda
    (scale reciprocalGap beta : Real) : Real :=
  let alpha := refinedLocalAlpha scale reciprocalGap beta
  alpha / (2 - alpha)

theorem refinedLocalAlpha_sq
    (scale reciprocalGap beta : Real)
    (hscale : 0 < scale) (hbeta : 0 <= beta) :
    refinedLocalAlpha scale reciprocalGap beta ^ 2 =
      25 * reciprocalGap ^ 2 * beta / scale := by
  unfold refinedLocalAlpha
  rw [Real.sq_sqrt]
  positivity

theorem refinedLocalAlpha_pos
    (scale reciprocalGap beta : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hbeta : 0 < beta) :
    0 < refinedLocalAlpha scale reciprocalGap beta := by
  unfold refinedLocalAlpha
  rw [Real.sqrt_pos]
  positivity

theorem refinedLocalAlpha_le_one
    (scale reciprocalGap beta : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hbeta : beta <= scale / (25 * reciprocalGap ^ 2)) :
    refinedLocalAlpha scale reciprocalGap beta <= 1 := by
  have hdenom : 0 < 25 * reciprocalGap ^ 2 := by positivity
  have hmul : 25 * reciprocalGap ^ 2 * beta <= scale := by
    have := (le_div_iff₀ hdenom).1 hbeta
    nlinarith
  unfold refinedLocalAlpha
  rw [Real.sqrt_le_one]
  exact (div_le_one hscale).2 hmul

theorem refinedLocalLambda_mem_Ioc
    (scale reciprocalGap beta : Real)
    (hscale : 0 < scale) (hreciprocalGap : 0 < reciprocalGap)
    (hbetaPos : 0 < beta)
    (hbetaUpper : beta <= scale / (25 * reciprocalGap ^ 2)) :
    refinedLocalLambda scale reciprocalGap beta ∈ Set.Ioc (0 : Real) 1 := by
  let alpha := refinedLocalAlpha scale reciprocalGap beta
  have halphaPos : 0 < alpha :=
    refinedLocalAlpha_pos scale reciprocalGap beta
      hscale hreciprocalGap hbetaPos
  have halphaLe : alpha <= 1 :=
    refinedLocalAlpha_le_one scale reciprocalGap beta
      hscale hreciprocalGap hbetaUpper
  have hdenom : 0 < 2 - alpha := by linarith
  constructor
  · dsimp [refinedLocalLambda, alpha]
    positivity
  · dsimp [refinedLocalLambda, alpha]
    exact (div_le_one hdenom).2 (by linarith)

theorem one_add_refinedLocalLambda_eq
    (scale reciprocalGap beta : Real)
    (halpha : refinedLocalAlpha scale reciprocalGap beta < 2) :
    1 + refinedLocalLambda scale reciprocalGap beta =
      2 / (2 - refinedLocalAlpha scale reciprocalGap beta) := by
  unfold refinedLocalLambda
  dsimp only
  field_simp [ne_of_gt (sub_pos.2 halpha)]
  ring

theorem two_mul_refinedLocalLambda_div_one_add_eq_alpha
    (scale reciprocalGap beta : Real)
    (halpha : refinedLocalAlpha scale reciprocalGap beta < 2) :
    2 * refinedLocalLambda scale reciprocalGap beta /
        (1 + refinedLocalLambda scale reciprocalGap beta) =
      refinedLocalAlpha scale reciprocalGap beta := by
  have hdenom : 0 < 2 - refinedLocalAlpha scale reciprocalGap beta :=
    sub_pos.2 halpha
  have honeAdd :
      1 + refinedLocalLambda scale reciprocalGap beta =
        2 / (2 - refinedLocalAlpha scale reciprocalGap beta) :=
    one_add_refinedLocalLambda_eq scale reciprocalGap beta halpha
  rw [honeAdd]
  unfold refinedLocalLambda
  dsimp only
  field_simp [ne_of_gt hdenom]

end Tsallis
end BanditRLProof
