import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIProbabilityBudget

/-! Tuned Bellman-innovation tail for canonical recurrent UCBVI-CH. -/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- Bellman-martingale charge used in the frozen `20/250` terminal. -/
noncomputable def bellmanInnovationThreshold
    (mdp : MDP State Action) (episodes : Nat) (delta : Real) : Real :=
  (11 / 8 : Real) * mdp.horizon *
    Real.sqrt ((mdp.horizon : Real) * episodes) *
    logFactor (State := State) (Action := Action) mdp episodes delta

/-- Chernoff tilt optimized for the deterministic `K H^3` variance budget. -/
noncomputable def bellmanInnovationTilt
    (mdp : MDP State Action) (episodes : Nat) (delta : Real) : Real :=
  4 * bellmanInnovationThreshold (State := State) (Action := Action)
      mdp episodes delta /
    ((episodes : Real) * ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2))

theorem bellmanInnovationThreshold_nonneg
    (mdp : MDP State Action) (episodes : Nat) (delta : Real) :
    0 <= bellmanInnovationThreshold (State := State) (Action := Action)
      mdp episodes delta := by
  unfold bellmanInnovationThreshold
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg mdp.horizon))
      (Real.sqrt_nonneg _))
    (logFactor_nonneg mdp episodes delta)

theorem bellmanInnovationTilt_pos
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    0 < bellmanInnovationTilt (State := State) (Action := Action)
      mdp episodes delta := by
  unfold bellmanInnovationTilt
  apply div_pos
  · apply mul_pos (by norm_num)
    unfold bellmanInnovationThreshold
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) (by exact_mod_cast hhorizon))
        (Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hhorizon)
          (by exact_mod_cast hepisodes))))
      (lt_of_lt_of_le zero_lt_one
        (one_le_logFactor mdp episodes delta hhorizon hepisodes
          hdelta hdelta_le_one))
  · positivity

theorem bellmanInnovationTilt_exponent_le_neg_two_logFactor
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    -bellmanInnovationTilt (State := State) (Action := Action)
          mdp episodes delta *
        bellmanInnovationThreshold (State := State) (Action := Action)
          mdp episodes delta +
      (bellmanInnovationTilt (State := State) (Action := Action)
          mdp episodes delta ^ 2 / 8) *
        ((episodes : Real) *
          ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)) <=
      -2 * logFactor (State := State) (Action := Action)
        mdp episodes delta := by
  let H : Real := mdp.horizon
  let K : Real := episodes
  let L := logFactor (State := State) (Action := Action) mdp episodes delta
  let threshold : Real := (11 / 8 : Real) * H * Real.sqrt (H * K) * L
  let variance : Real := K * (H * H ^ 2)
  have hH : 0 < H := by dsimp [H]; exact_mod_cast hhorizon
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hepisodes
  have hL : 1 <= L := one_le_logFactor mdp episodes delta
    hhorizon hepisodes hdelta hdelta_le_one
  have hHK : 0 <= H * K := mul_nonneg hH.le hK.le
  have hsqrtSq : Real.sqrt (H * K) ^ 2 = H * K := Real.sq_sqrt hHK
  have hvariance : 0 < variance := by dsimp [variance]; positivity
  have hexact :
      -(4 * threshold / variance) * threshold +
          ((4 * threshold / variance) ^ 2 / 8) * variance =
        -(121 / 32 : Real) * L ^ 2 := by
    dsimp [threshold, variance]
    field_simp
    nlinarith
  change -(4 * threshold / variance) * threshold +
      ((4 * threshold / variance) ^ 2 / 8) * variance <= -2 * L
  rw [hexact]
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) (zero_le_one.trans hL)]

/-- The tuned Bellman-innovation tail consumes at most one fifth of `delta`. -/
theorem recurrentSource_trajectoryMeasure_bellmanInnovation_sum_ge_threshold_le_fifth
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let source := recurrentSource mdp initialState defaultState episodes delta
    source.trajectoryMeasure
        {trajectory |
          bellmanInnovationThreshold (State := State) (Action := Action)
              mdp episodes delta <=
            (Finset.range episodes).sum (fun round =>
              recurrentBellmanInnovationProcess mdp defaultState episodes delta
                round trajectory)} <=
      ENNReal.ofReal (delta / 5) := by
  dsimp only
  let threshold := bellmanInnovationThreshold
    (State := State) (Action := Action) mdp episodes delta
  let tilt := bellmanInnovationTilt
    (State := State) (Action := Action) mdp episodes delta
  let L := logFactor (State := State) (Action := Action) mdp episodes delta
  let B : Real := confidenceNumerator (State := State) (Action := Action)
    mdp episodes
  have htail := trajectoryMeasure_recurrentBellmanInnovation_sum_ge_le
    (mdp := mdp) (initialState := initialState) defaultState episodes delta
    hhorizon tilt threshold
    (bellmanInnovationTilt_pos mdp episodes delta hhorizon hepisodes
      hdelta hdelta_le_one)
  have hexponent :
      -tilt * threshold + (tilt ^ 2 / 8) *
          ((episodes : Real) *
            ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)) <=
        -2 * L := by
    dsimp [tilt, threshold, L]
    exact bellmanInnovationTilt_exponent_le_neg_two_logFactor
      mdp episodes delta hhorizon hepisodes hdelta hdelta_le_one
  have hexp : Real.exp (-2 * L) = (delta / B) ^ 2 := by
    dsimp [L, B]
    exact exp_neg_two_mul_logFactor_eq mdp episodes delta
      hhorizon hepisodes hdelta hdelta_le_one
  have hBfive : 5 <= B := by
    dsimp [B]
    exact_mod_cast (show 5 <= confidenceNumerator
      (State := State) (Action := Action) mdp episodes by
        unfold confidenceNumerator totalSteps
        have hproduct : 1 <=
            mdp.horizon * Fintype.card State * Fintype.card Action *
              (episodes * mdp.horizon) := by
          have hpos : 0 <
              mdp.horizon * Fintype.card State * Fintype.card Action *
                (episodes * mdp.horizon) := by positivity
          omega
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 5 hproduct)
  have hreal : Real.exp (-2 * L) <= delta / 5 := by
    rw [hexp]
    have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hBfive
    have hdeltaB : delta <= B := hdelta_le_one.trans
      ((show (1 : Real) <= 5 by norm_num).trans hBfive)
    have hfiveDelta : 5 * delta <= B ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hBfive) hBpos.le]
    field_simp
    nlinarith
  exact htail.trans <| calc
    ENNReal.ofReal (Real.exp
        (-tilt * threshold + (tilt ^ 2 / 8) *
          ((episodes : Real) *
            ((mdp.horizon : Real) * (mdp.horizon : Real) ^ 2)))) <=
      ENNReal.ofReal (Real.exp (-2 * L)) := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.exp_le_exp.mpr hexponent
    _ <= ENNReal.ofReal (delta / 5) := ENNReal.ofReal_le_ofReal hreal

end AdaptiveCumulativeHoeffdingUCBVI
end BanditRLProof.FiniteHorizonRL
