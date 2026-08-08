import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeInverseSqrtCalibration
import BanditRLProof.TsallisSqrtScheduleSelfBoundingOptimization

/-!
# Explicit adaptive cumulative inverse-square-root calibration and rate

This module constructs the two-scale path calibration from deterministic
episode and scale inequalities.  It also sums the resulting capped
inverse-square-root round envelopes and feeds the closed form into the existing
optimism/recommended-policy expected-regret terminal.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveEpisodeBatchSource

/-- The logarithmic factor shared by every queried cumulative prefix. -/
noncomputable def cumulativeInverseSqrtLogFactor
    (mdp : MDP State Action) (rounds : Nat) (delta : Real) : Real :=
  Real.log (2 / cumulativeCountLocalDelta mdp rounds delta)

/-- The deterministic coefficient multiplying each cumulative count radius. -/
noncomputable def cumulativeInverseSqrtCoverCoefficient
    (mdp : MDP State Action) (rewardBound budget : Real) : Real :=
  2 * (Fintype.card State : Real) * (mdp.horizon : Real) *
    (rewardBound + budget)

/--
A sufficient episode threshold for both a half expected-visit margin and the
budget branch of the capped transition-radius cover.
-/
noncomputable def cumulativeInverseSqrtCalibrationEpisodeThreshold
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor rewardBound budget : Real) : Real :=
  max
    (2 * cumulativeInverseSqrtLogFactor mdp rounds delta / visitFloor ^ 2)
    (2 * (cumulativeInverseSqrtCoverCoefficient mdp rewardBound budget) ^ 2 *
      cumulativeInverseSqrtLogFactor mdp rounds delta /
        (budget ^ 2 * visitFloor ^ 2))

/-- Exact square of one cumulative coordinate confidence radius. -/
theorem cumulativeCoordinateConfidenceRadius_sq_eq
    (mdp : MDP State Action) {episodes rounds prefixRounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta : Real} (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (cumulativeCoordinateConfidenceRadius episodes prefixRounds
        (cumulativeCountLocalDelta mdp rounds delta)) ^ 2 =
      (prefixRounds : Real) * (episodes : Real) / 2 *
        cumulativeInverseSqrtLogFactor mdp rounds delta := by
  letI : Nonempty (Fin rounds × CountCoordinate mdp) :=
    cumulativeCountIndex_nonempty hhorizon hrounds
  have hlocalPos : 0 < cumulativeCountLocalDelta mdp rounds delta :=
    cumulativeCountLocalDelta_pos inferInstance hdelta
  have hlocalLeOne : cumulativeCountLocalDelta mdp rounds delta <= 1 :=
    cumulativeCountLocalDelta_le_one inferInstance hdelta hdelta_le_one
  rw [cumulativeCoordinateConfidenceRadius,
    Concentration.subGaussianSumConfidenceRadius_sq _ _ hlocalPos hlocalLeOne]
  have hvariance :
      (((cumulativeCoordinateVarianceProxy episodes prefixRounds : NNReal) : Real)) =
        (prefixRounds : Real) * (episodes : Real) / 4 := by
    rw [cumulativeCoordinateVarianceProxy]
    simp only [Finset.sum_const, Finset.card_range]
    rw [MarkovPolicy.iidBernoulliVarianceProxy_eq]
    push_cast
    ring
  rw [hvariance]
  unfold cumulativeInverseSqrtLogFactor
  ring

/-- The shared logarithmic factor is nonnegative at a valid global delta. -/
theorem cumulativeInverseSqrtLogFactor_nonneg
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta : Real} (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    0 <= cumulativeInverseSqrtLogFactor mdp rounds delta := by
  letI : Nonempty (Fin rounds × CountCoordinate mdp) :=
    cumulativeCountIndex_nonempty hhorizon hrounds
  have hlocalPos : 0 < cumulativeCountLocalDelta mdp rounds delta :=
    cumulativeCountLocalDelta_pos inferInstance hdelta
  have hlocalLeOne : cumulativeCountLocalDelta mdp rounds delta <= 1 :=
    cumulativeCountLocalDelta_le_one inferInstance hdelta hdelta_le_one
  unfold cumulativeInverseSqrtLogFactor
  apply Real.log_nonneg
  rw [le_div_iff₀ hlocalPos]
  linarith

/--
The episode threshold leaves at least half of the predictable expected visits
after subtracting the cumulative confidence radius, uniformly over prefixes.
-/
theorem half_cumulativePathVisitExpectedFloor_lt_lowerMargin_of_episodeThreshold
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) {delta visitFloor rewardBound budget : Real}
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor)
    (hthreshold :
      cumulativeInverseSqrtCalibrationEpisodeThreshold mdp rounds delta
          visitFloor rewardBound budget < (episodes : Real))
    (round : Fin rounds) :
    (round + 1 : Real) * (episodes : Real) * visitFloor / 2 <
      cumulativePathVisitLowerMargin mdp episodes rounds delta visitFloor round := by
  let prefixRounds : Nat := round + 1
  let radius := cumulativeCoordinateConfidenceRadius episodes prefixRounds
    (cumulativeCountLocalDelta mdp rounds delta)
  let logarithm := cumulativeInverseSqrtLogFactor mdp rounds delta
  have hlogThreshold : 2 * logarithm / visitFloor ^ 2 < (episodes : Real) := by
    exact (lt_of_le_of_lt (le_max_left _ _) hthreshold)
  have hvisitFloorSq : 0 < visitFloor ^ 2 := sq_pos_of_pos hvisitFloor
  have hscaledLog : 2 * logarithm < (episodes : Real) * visitFloor ^ 2 :=
    (div_lt_iff₀ hvisitFloorSq).mp hlogThreshold
  have hprefixPos : 0 < prefixRounds := by
    dsimp [prefixRounds]
    omega
  have hprefixOne : (1 : Real) <= prefixRounds := by
    exact_mod_cast hprefixPos
  have hprefixNonneg : (0 : Real) <= prefixRounds := le_trans zero_le_one hprefixOne
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hradiusNonneg : 0 <= radius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hradiusSq : radius ^ 2 =
      (prefixRounds : Real) * (episodes : Real) / 2 * logarithm := by
    simpa [radius, logarithm] using
      cumulativeCoordinateConfidenceRadius_sq_eq mdp hhorizon hrounds
        hdelta hdelta_le_one (episodes := episodes) (prefixRounds := prefixRounds)
  have hhalfPos :
      0 < (prefixRounds : Real) * (episodes : Real) * visitFloor / 2 := by
    positivity
  have hsquare : radius ^ 2 <
      ((prefixRounds : Real) * (episodes : Real) * visitFloor / 2) ^ 2 := by
    have hmultiplier :
        0 < (prefixRounds : Real) * (episodes : Real) / 4 := by positivity
    have hscaled := mul_lt_mul_of_pos_left hscaledLog hmultiplier
    have hprefixSq : (prefixRounds : Real) <= (prefixRounds : Real) ^ 2 := by
      nlinarith
    have hcoefficient :
        0 <= (episodes : Real) ^ 2 * visitFloor ^ 2 / 4 := by positivity
    calc
      radius ^ 2 =
          ((prefixRounds : Real) * (episodes : Real) / 4) *
            (2 * logarithm) := by rw [hradiusSq]; ring
      _ < ((prefixRounds : Real) * (episodes : Real) / 4) *
            ((episodes : Real) * visitFloor ^ 2) := hscaled
      _ = (prefixRounds : Real) *
            ((episodes : Real) ^ 2 * visitFloor ^ 2 / 4) := by ring
      _ <= (prefixRounds : Real) ^ 2 *
            ((episodes : Real) ^ 2 * visitFloor ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right hprefixSq hcoefficient
      _ = ((prefixRounds : Real) * (episodes : Real) * visitFloor / 2) ^ 2 := by
        ring
  have hradiusLt : radius <
      (prefixRounds : Real) * (episodes : Real) * visitFloor / 2 :=
    (sq_lt_sq₀ hradiusNonneg hhalfPos.le).mp hsquare
  unfold cumulativePathVisitLowerMargin
  unfold cumulativePathVisitExpectedFloor
  norm_num [prefixRounds, radius, Nat.cast_add, Nat.cast_one] at hradiusLt ⊢
  linarith

/--
The explicit episode threshold and scale-square condition construct the full
two-scale path calibration; no roundwise cover premise remains.
-/
theorem cumulativeInverseSqrtPathCalibration_of_episodeThreshold
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) {delta visitFloor rewardBound budget scale : Real}
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor) (hrewardBound : 0 <= rewardBound)
    (hbudget : 0 < budget) (hscale : 0 <= scale)
    (hscaleCover :
      (cumulativeInverseSqrtCoverCoefficient mdp rewardBound budget) ^ 2 *
          cumulativeInverseSqrtLogFactor mdp rounds delta <=
        scale ^ 2 * visitFloor)
    (hthreshold :
      cumulativeInverseSqrtCalibrationEpisodeThreshold mdp rounds delta
          visitFloor rewardBound budget < (episodes : Real)) :
    CumulativeInverseSqrtPathCalibration mdp episodes rounds delta visitFloor
      rewardBound budget scale := by
  let coefficient := cumulativeInverseSqrtCoverCoefficient mdp rewardBound budget
  have hcoefficient : 0 <= coefficient := by
    dsimp [coefficient, cumulativeInverseSqrtCoverCoefficient]
    positivity
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hlogNonneg :
      0 <= cumulativeInverseSqrtLogFactor mdp rounds delta :=
    cumulativeInverseSqrtLogFactor_nonneg mdp hhorizon hrounds hdelta hdelta_le_one
  refine
    { visitFloor_pos := hvisitFloor
      rewardBound_nonneg := hrewardBound
      budget_nonneg := hbudget.le
      scale_nonneg := hscale
      lowerMargin_pos := ?_
      coverBudget := ?_
      coverScale := ?_ }
  · intro round
    have hmargin :=
      half_cumulativePathVisitExpectedFloor_lt_lowerMargin_of_episodeThreshold
        mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor
        hthreshold round
    have hhalfPos :
        0 < (round + 1 : Real) * (episodes : Real) * visitFloor / 2 := by
      positivity
    linarith
  · intro round
    let prefixRounds : Nat := round + 1
    let radius := cumulativeCoordinateConfidenceRadius episodes prefixRounds
      (cumulativeCountLocalDelta mdp rounds delta)
    let logarithm := cumulativeInverseSqrtLogFactor mdp rounds delta
    let halfFloor :=
      (prefixRounds : Real) * (episodes : Real) * visitFloor / 2
    let margin := cumulativePathVisitLowerMargin
      mdp episodes rounds delta visitFloor round
    have hbudgetThreshold :
        2 * coefficient ^ 2 * logarithm /
            (budget ^ 2 * visitFloor ^ 2) < (episodes : Real) := by
      exact lt_of_le_of_lt (le_max_right _ _) hthreshold
    have hdenominator : 0 < budget ^ 2 * visitFloor ^ 2 := by positivity
    have hscaled :
        2 * coefficient ^ 2 * logarithm <
          (episodes : Real) * (budget ^ 2 * visitFloor ^ 2) :=
      (div_lt_iff₀ hdenominator).mp hbudgetThreshold
    have hprefixPos : 0 < prefixRounds := by
      dsimp [prefixRounds]
      omega
    have hprefixOne : (1 : Real) <= prefixRounds := by exact_mod_cast hprefixPos
    have hradiusNonneg : 0 <= radius :=
      Concentration.subGaussianSumConfidenceRadius_nonneg _ _
    have hradiusSq : radius ^ 2 =
        (prefixRounds : Real) * (episodes : Real) / 2 * logarithm := by
      simpa [radius, logarithm] using
        cumulativeCoordinateConfidenceRadius_sq_eq mdp hhorizon hrounds
          hdelta hdelta_le_one (episodes := episodes) (prefixRounds := prefixRounds)
    have hmargin : halfFloor < margin := by
      simpa [halfFloor, margin, prefixRounds] using
        half_cumulativePathVisitExpectedFloor_lt_lowerMargin_of_episodeThreshold
          mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor
          hthreshold round
    have hhalfPos : 0 < halfFloor := by
      dsimp [halfFloor]
      positivity
    have hmultiplier :
        0 < (prefixRounds : Real) * (episodes : Real) / 4 := by positivity
    have hscaledPrefix := mul_lt_mul_of_pos_left hscaled hmultiplier
    have hprefixSq : (prefixRounds : Real) <= (prefixRounds : Real) ^ 2 := by
      nlinarith
    have hpositiveCoefficient :
        0 <= (episodes : Real) ^ 2 * budget ^ 2 * visitFloor ^ 2 / 4 := by
      positivity
    have hsquare : (coefficient * radius) ^ 2 < (budget * halfFloor) ^ 2 := by
      calc
        (coefficient * radius) ^ 2 =
            ((prefixRounds : Real) * (episodes : Real) / 4) *
              (2 * coefficient ^ 2 * logarithm) := by
          rw [mul_pow, hradiusSq]
          ring
        _ < ((prefixRounds : Real) * (episodes : Real) / 4) *
              ((episodes : Real) * (budget ^ 2 * visitFloor ^ 2)) :=
          hscaledPrefix
        _ = (prefixRounds : Real) *
              ((episodes : Real) ^ 2 * budget ^ 2 * visitFloor ^ 2 / 4) := by
          ring
        _ <= (prefixRounds : Real) ^ 2 *
              ((episodes : Real) ^ 2 * budget ^ 2 * visitFloor ^ 2 / 4) :=
          mul_le_mul_of_nonneg_right hprefixSq hpositiveCoefficient
        _ = (budget * halfFloor) ^ 2 := by
          dsimp [halfFloor]
          ring
    have hcoefficientRadiusLt : coefficient * radius < budget * halfFloor :=
      (sq_lt_sq₀ (mul_nonneg hcoefficient hradiusNonneg)
        (mul_nonneg hbudget.le hhalfPos.le)).mp hsquare
    have hbudgetMargin : budget * halfFloor < budget * margin :=
      mul_lt_mul_of_pos_left hmargin hbudget
    calc
      (Fintype.card State : Real) * (2 * radius) *
          ((mdp.horizon : Real) * (rewardBound + budget)) =
        coefficient * radius := by
          dsimp [coefficient, cumulativeInverseSqrtCoverCoefficient]
          ring
      _ <= budget * margin := (hcoefficientRadiusLt.trans hbudgetMargin).le
  · intro round
    let prefixRounds : Nat := round + 1
    let radius := cumulativeCoordinateConfidenceRadius episodes prefixRounds
      (cumulativeCountLocalDelta mdp rounds delta)
    let logarithm := cumulativeInverseSqrtLogFactor mdp rounds delta
    let halfFloor :=
      (prefixRounds : Real) * (episodes : Real) * visitFloor / 2
    let margin := cumulativePathVisitLowerMargin
      mdp episodes rounds delta visitFloor round
    have hprefixPos : 0 < prefixRounds := by
      dsimp [prefixRounds]
      omega
    have hradiusNonneg : 0 <= radius :=
      Concentration.subGaussianSumConfidenceRadius_nonneg _ _
    have hradiusSq : radius ^ 2 =
        (prefixRounds : Real) * (episodes : Real) / 2 * logarithm := by
      simpa [radius, logarithm] using
        cumulativeCoordinateConfidenceRadius_sq_eq mdp hhorizon hrounds
          hdelta hdelta_le_one (episodes := episodes) (prefixRounds := prefixRounds)
    have hmargin : halfFloor < margin := by
      simpa [halfFloor, margin, prefixRounds] using
        half_cumulativePathVisitExpectedFloor_lt_lowerMargin_of_episodeThreshold
          mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor
          hthreshold round
    have hmarginNonneg : 0 <= margin := by
      have hhalfPos : 0 < halfFloor := by
        dsimp [halfFloor]
        positivity
      linarith
    have hscaledPrefix :
        coefficient ^ 2 *
            ((prefixRounds : Real) * (episodes : Real) / 2 * logarithm) <=
          scale ^ 2 * halfFloor := by
      have hmultiplier :
          0 <= (prefixRounds : Real) * (episodes : Real) / 2 := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hscaleCover hmultiplier
      dsimp [halfFloor, logarithm, coefficient] at hscaled ⊢
      nlinarith
    have hsquare : (coefficient * radius) ^ 2 <=
        (scale * Real.sqrt margin) ^ 2 := by
      rw [mul_pow, hradiusSq, mul_pow, Real.sq_sqrt hmarginNonneg]
      calc
        coefficient ^ 2 *
              ((prefixRounds : Real) * (episodes : Real) / 2 * logarithm) <=
            scale ^ 2 * halfFloor := hscaledPrefix
        _ <= scale ^ 2 * margin :=
          mul_le_mul_of_nonneg_left hmargin.le (sq_nonneg scale)
    have hcoefficientRadiusLe : coefficient * radius <=
        scale * Real.sqrt margin :=
      (sq_le_sq₀ (mul_nonneg hcoefficient hradiusNonneg)
        (mul_nonneg hscale (Real.sqrt_nonneg _))).mp hsquare
    calc
      (Fintype.card State : Real) * (2 * radius) *
          ((mdp.horizon : Real) * (rewardBound + budget)) =
        coefficient * radius := by
          dsimp [coefficient, cumulativeInverseSqrtCoverCoefficient]
          ring
      _ <= scale * Real.sqrt margin := hcoefficientRadiusLe

/-- Closed-form cap-versus-square-root bound for the complete round sum. -/
noncomputable def cumulativeInverseSqrtEnvelopeSumBound
    (episodes rounds : Nat) (visitFloor budget scale : Real) : Real :=
  min ((rounds : Real) * budget)
    (2 * scale * Real.sqrt (rounds : Real) /
      Real.sqrt ((episodes : Real) * visitFloor / 2))

/--
The round-indexed capped inverse-square-root envelopes sum to the minimum of
the linear cap and an explicit square-root-in-rounds bound.
-/
theorem sum_cumulativeInverseSqrtRadiusEnvelope_le_explicit
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) {delta visitFloor rewardBound budget scale : Real}
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor) (hscale : 0 <= scale)
    (hthreshold :
      cumulativeInverseSqrtCalibrationEpisodeThreshold mdp rounds delta
          visitFloor rewardBound budget < (episodes : Real)) :
    (∑ round : Fin rounds,
        cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
          visitFloor budget scale round) <=
      cumulativeInverseSqrtEnvelopeSumBound episodes rounds visitFloor budget scale := by
  let baseFloor := (episodes : Real) * visitFloor / 2
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hbaseFloor : 0 < baseFloor := by
    dsimp [baseFloor]
    positivity
  have hlinear :
      (∑ round : Fin rounds,
          cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round) <=
        (rounds : Real) * budget := by
    calc
      (∑ round : Fin rounds,
          cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round) <=
          ∑ _round : Fin rounds, budget := by
            apply Finset.sum_le_sum
            intro round _hround
            exact min_le_left _ _
      _ = (rounds : Real) * budget := by simp
  have hsqrt :
      (∑ round : Fin rounds,
          cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round) <=
        2 * scale * Real.sqrt (rounds : Real) / Real.sqrt baseFloor := by
    calc
      (∑ round : Fin rounds,
          cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round) <=
          ∑ round : Fin rounds,
            (scale / Real.sqrt baseFloor) *
              (1 / Real.sqrt (((round.val + 1 : Nat) : Real))) := by
        apply Finset.sum_le_sum
        intro round _hround
        let prefixRounds : Nat := round.val + 1
        let halfFloor := (prefixRounds : Real) * (episodes : Real) * visitFloor / 2
        let margin := cumulativePathVisitLowerMargin
          mdp episodes rounds delta visitFloor round
        have hmargin : halfFloor < margin := by
          simpa [halfFloor, margin, prefixRounds] using
            half_cumulativePathVisitExpectedFloor_lt_lowerMargin_of_episodeThreshold
              mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor
              hthreshold round
        have hprefixPos : 0 < prefixRounds := by
          dsimp [prefixRounds]
          omega
        have hhalfFloor : 0 < halfFloor := by
          dsimp [halfFloor]
          positivity
        have hsqrtLe : Real.sqrt halfFloor <= Real.sqrt margin :=
          Real.sqrt_le_sqrt hmargin.le
        have hdivLe : scale / Real.sqrt margin <= scale / Real.sqrt halfFloor :=
          div_le_div_of_nonneg_left hscale (Real.sqrt_pos.2 hhalfFloor) hsqrtLe
        calc
          cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
              visitFloor budget scale round <=
            scale / Real.sqrt margin := by
              exact min_le_right _ _
          _ <= scale / Real.sqrt halfFloor := hdivLe
          _ = (scale / Real.sqrt baseFloor) *
              (1 / Real.sqrt (((round.val + 1 : Nat) : Real))) := by
            have hsqrtPrefix : 0 < Real.sqrt (prefixRounds : Real) := by positivity
            have hsqrtBase : 0 < Real.sqrt baseFloor := Real.sqrt_pos.2 hbaseFloor
            have hhalfEq : halfFloor = (prefixRounds : Real) * baseFloor := by
              dsimp [halfFloor, baseFloor]
              ring
            rw [hhalfEq, Real.sqrt_mul (by positivity : (0 : Real) <= prefixRounds)]
            dsimp [prefixRounds]
            field_simp
    _ = (scale / Real.sqrt baseFloor) *
          (∑ round : Fin rounds,
            1 / Real.sqrt (((round.val + 1 : Nat) : Real))) := by
      rw [Finset.mul_sum]
    _ = (scale / Real.sqrt baseFloor) *
          (Finset.range rounds).sum (fun round =>
            1 / Real.sqrt (((round + 1 : Nat) : Real))) := by
      rw [Fin.sum_univ_eq_sum_range (fun round : Nat =>
        1 / Real.sqrt (((round + 1 : Nat) : Real)))]
    _ <= (scale / Real.sqrt baseFloor) *
          (2 * Real.sqrt (rounds : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (Tsallis.sum_range_one_div_sqrt_natSucc_le_two_sqrt rounds)
        (div_nonneg hscale (Real.sqrt_nonneg _))
    _ = 2 * scale * Real.sqrt (rounds : Real) / Real.sqrt baseFloor := by
      ring
  exact le_min hlinear (by simpa [baseFloor] using hsqrt)

/-- Explicit closed form replacing the terminal's unsimplified round sum. -/
noncomputable def cumulativeInverseSqrtRecommendedExpectedRegretBound
    (mdp : MDP State Action) (episodes rounds : Nat)
    (visitFloor budget scale : Real) : Real :=
  2 * (mdp.horizon : Real) *
    cumulativeInverseSqrtEnvelopeSumBound episodes rounds visitFloor budget scale

/-- The terminal's horizon-weighted finite sum is bounded by the closed form. -/
theorem sum_horizon_mul_two_cumulativeInverseSqrtRadiusEnvelope_le_explicit
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) {delta visitFloor rewardBound budget scale : Real}
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor) (hscale : 0 <= scale)
    (hthreshold :
      cumulativeInverseSqrtCalibrationEpisodeThreshold mdp rounds delta
          visitFloor rewardBound budget < (episodes : Real)) :
    (∑ round : Fin rounds,
        (mdp.horizon : Real) *
          (2 * cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round)) <=
      cumulativeInverseSqrtRecommendedExpectedRegretBound mdp episodes rounds
        visitFloor budget scale := by
  have hsum := sum_cumulativeInverseSqrtRadiusEnvelope_le_explicit
    mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor hscale hthreshold
  calc
    (∑ round : Fin rounds,
        (mdp.horizon : Real) *
          (2 * cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round)) =
      (2 * (mdp.horizon : Real)) *
        ∑ round : Fin rounds,
          cumulativeInverseSqrtRadiusEnvelope mdp episodes rounds delta
            visitFloor budget scale round := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro round _hround
      ring
    _ <= (2 * (mdp.horizon : Real)) *
        cumulativeInverseSqrtEnvelopeSumBound episodes rounds visitFloor budget scale :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = cumulativeInverseSqrtRecommendedExpectedRegretBound mdp episodes rounds
        visitFloor budget scale := rfl

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
Closed-form route endpoint: deterministic episode and scale inequalities
construct the capped calibration and replace the round sum by an explicit
minimum of a linear cap and a square-root-in-rounds rate.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_closedFormRecommendedExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (rewardBound budget scale : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hbudget : 0 < budget) (hscale : 0 <= scale)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor)
    (hscaleCover :
      (AdaptiveEpisodeBatchSource.cumulativeInverseSqrtCoverCoefficient
          mdp rewardBound budget) ^ 2 *
          AdaptiveEpisodeBatchSource.cumulativeInverseSqrtLogFactor
            mdp rounds delta <=
        scale ^ 2 * visitFloor)
    (hthreshold :
      AdaptiveEpisodeBatchSource.cumulativeInverseSqrtCalibrationEpisodeThreshold
          mdp rounds delta visitFloor rewardBound budget < (episodes : Real)) :
    let countRadius := TransitionCountRadius.cappedInverseSqrt
      budget scale hbudget.le hscale
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate hexplorationRate
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRecommendedExpectedRegretBound
            mdp episodes rounds visitFloor budget scale := by
  have hrewardBoundNonneg : 0 <= rewardBound := by
    let state : State := Classical.choice inferInstance
    let action : Action := Classical.choice inferInstance
    exact (abs_nonneg (mdp.reward state action)).trans
      (hrewardBound state action)
  let calibration :=
    AdaptiveEpisodeBatchSource.cumulativeInverseSqrtPathCalibration_of_episodeThreshold
      mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor
      hrewardBoundNonneg hbudget hscale hscaleCover hthreshold
  let countRadius := TransitionCountRadius.cappedInverseSqrt
    budget scale hbudget.le hscale
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate hexplorationRate
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_explicitRecommendedExpectedRegret
      mdp initialState episodes rounds initialTable defaultState explorationRate
      hexplorationRate support visitFloor hfloor rewardBound budget scale
      hrewardBound hhorizon hrounds hepisodes delta hdelta hdelta_le_one calibration
  have hsum :=
    AdaptiveEpisodeBatchSource.sum_horizon_mul_two_cumulativeInverseSqrtRadiusEnvelope_le_explicit
      mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor hscale hthreshold
  change MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRecommendedExpectedRegretBound
            mdp episodes rounds visitFloor budget scale
  have hparent' :
      MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
        source.trajectoryMeasure
            (source.adaptiveCumulativeCountBadEvent rounds delta) <=
          ENNReal.ofReal delta /\
        forall trajectory,
          trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
          (forall round : Fin rounds, forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              (adaptiveCumulativeEmpiricalOptimisticPlanAt
                trajectory defaultState countRadius round).upperValueRemaining
                  mdp.horizon le_rfl state) /\
          adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
              (initialState := initialState) trajectory defaultState countRadius rounds <=
            ∑ round : Fin rounds,
              (mdp.horizon : Real) *
                (2 * AdaptiveEpisodeBatchSource.cumulativeInverseSqrtRadiusEnvelope
                  mdp episodes rounds delta visitFloor budget scale round) := by
    simpa [source, countRadius, calibration] using hparent
  refine ⟨hparent'.1, hparent'.2.1, ?_⟩
  intro trajectory htrajectory
  exact ⟨(hparent'.2.2 trajectory htrajectory).1,
    (hparent'.2.2 trajectory htrajectory).2.trans hsum⟩

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
