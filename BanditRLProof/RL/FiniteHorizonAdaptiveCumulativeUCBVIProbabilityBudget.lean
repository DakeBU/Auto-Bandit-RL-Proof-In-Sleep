import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVISimultaneousConfidence
import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIAlignment

/-! Paper-scale probability arithmetic for canonical recurrent UCBVI-CH. -/

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

namespace AdaptiveCumulativeHoeffdingUCBVI

theorem card_bernsteinCoordinateIndex
    (mdp : MDP State Action) (episodes : Nat) :
    Fintype.card (BernsteinCoordinateIndex mdp episodes) =
      episodes * Fintype.card State * Fintype.card Action *
        Fintype.card State * (episodes * mdp.horizon) := by
  let e : BernsteinCoordinateIndex mdp episodes ≃
      Fin episodes × State × Action × State × Fin (episodes * mdp.horizon) := {
    toFun := fun i => (i.round, i.state, i.action, i.nextState, i.count)
    invFun := fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2⟩
    left_inv := by intro i; cases i; rfl
    right_inv := by
      intro i
      rcases i with ⟨round, state, action, nextState, count⟩
      rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem card_optimalTailIndex
    (mdp : MDP State Action) (episodes : Nat) :
    Fintype.card (OptimalTailIndex mdp episodes) =
      episodes * mdp.horizon * Fintype.card State *
      Fintype.card Action * (episodes * mdp.horizon) := by
  let e : OptimalTailIndex mdp episodes ≃
      Fin episodes × Fin mdp.horizon × State × Action ×
        Fin (episodes * mdp.horizon) := {
    toFun := fun i => (i.round, i.stage, i.state, i.action, i.count)
    invFun := fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2⟩
    left_inv := by intro i; cases i; rfl
    right_inv := by
      intro i
      rcases i with ⟨round, stage, state, action, count⟩
      rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Exact exponential simplification at the paper logarithmic factor. -/
theorem exp_neg_two_mul_logFactor_eq
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    Real.exp (-2 * logFactor (State := State) (Action := Action)
        mdp episodes delta) =
      (delta /
        (confidenceNumerator (State := State) (Action := Action)
          mdp episodes : Nat)) ^ 2 := by
  let Q := (confidenceNumerator (State := State) (Action := Action)
    mdp episodes : Nat) / delta
  have hQ : 0 < Q := by
    dsimp [Q]
    apply div_pos _ hdelta
    exact_mod_cast (show 0 < confidenceNumerator
      (State := State) (Action := Action) mdp episodes by
        unfold confidenceNumerator totalSteps
        positivity)
  rw [logFactor_eq_paper mdp episodes delta hhorizon hepisodes
    hdelta hdelta_le_one]
  change Real.exp (-2 * Real.log Q) = _
  rw [show -2 * Real.log Q = -(2 * Real.log Q) by ring]
  rw [Real.exp_neg]
  rw [show (2 : Real) * Real.log Q = (2 : Nat) * Real.log Q by norm_num]
  rw [Real.exp_nat_mul, Real.exp_log hQ]
  dsimp [Q]
  field_simp

/-- The optimal-tail scalar term is no larger than the coordinate term because
the task log factor is at least one. -/
theorem exp_neg_two_mul_logFactor_sq_le
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    Real.exp (-2 * logFactor (State := State) (Action := Action)
        mdp episodes delta ^ 2) <=
      Real.exp (-2 * logFactor (State := State) (Action := Action)
        mdp episodes delta) := by
  apply Real.exp_le_exp.mpr
  have hL := one_le_logFactor mdp episodes delta hhorizon hepisodes
    hdelta hdelta_le_one
  nlinarith

private theorem ofReal_card_mul_two_mul_exp_le
    (card : Nat) (x budget : Real)
    (hx : 0 <= x) (hbudget : 0 <= budget)
    (h : (card : Real) * (2 * x) <= budget) :
    (card : ENNReal) * (2 * ENNReal.ofReal x) <= ENNReal.ofReal budget := by
  calc
    _ = ENNReal.ofReal ((card : Real) * (2 * x)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg card),
        ENNReal.ofReal_natCast]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2)]
      norm_num
    _ <= _ := ENNReal.ofReal_le_ofReal h

/-- The complete coordinate-plus-optimal-tail confidence family consumes at
most one fifth of `delta`. -/
theorem simultaneousTransitionTailBudget_le_fifth
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (Fintype.card (BernsteinCoordinateIndex mdp episodes) : ENNReal) *
          (2 * ENNReal.ofReal (Real.exp (-2 *
            logFactor (State := State) (Action := Action)
              mdp episodes delta))) +
        (Fintype.card (OptimalTailIndex mdp episodes) : ENNReal) *
          (2 * ENNReal.ofReal (Real.exp (-2 *
            logFactor (State := State) (Action := Action)
              mdp episodes delta ^ 2))) <=
      ENNReal.ofReal (delta / 5) := by
  let H : Real := mdp.horizon
  let K : Real := episodes
  let S : Real := Fintype.card State
  let A : Real := Fintype.card Action
  let B : Real := confidenceNumerator (State := State) (Action := Action)
    mdp episodes
  let L := logFactor (State := State) (Action := Action) mdp episodes delta
  have hH : 1 <= H := by
    dsimp [H]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hhorizon.ne'
  have hK : 1 <= K := by
    dsimp [K]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hepisodes.ne'
  have hS : 1 <= S := by
    dsimp [S]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := State))
  have hA : 1 <= A := by
    dsimp [A]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Action))
  have hB : B = 5 * H * S * A * (K * H) := by
    dsimp [B, H, K, S, A]
    norm_num [confidenceNumerator, totalSteps]
  have hexp : Real.exp (-2 * L) = (delta / B) ^ 2 := by
    dsimp [L, B]
    exact exp_neg_two_mul_logFactor_eq mdp episodes delta
      hhorizon hepisodes hdelta hdelta_le_one
  have hexpSq : Real.exp (-2 * L ^ 2) <= (delta / B) ^ 2 := by
    rw [← hexp]
    dsimp [L]
    exact exp_neg_two_mul_logFactor_sq_le mdp episodes delta
      hhorizon hepisodes hdelta hdelta_le_one
  have hcoordCard :
      (Fintype.card (BernsteinCoordinateIndex mdp episodes) : Real) =
        K * S * A * S * (K * H) := by
    rw [card_bernsteinCoordinateIndex]
    dsimp [H, K, S, A]
    norm_num only [Nat.cast_mul]
  have htailCard :
      (Fintype.card (OptimalTailIndex mdp episodes) : Real) =
        (K * H) * S * A * (K * H) := by
    rw [card_optimalTailIndex]
    dsimp [H, K, S, A]
    norm_num only [Nat.cast_mul]
  have hdeltaNonneg : 0 <= delta := hdelta.le
  have hcoordReal :
      (Fintype.card (BernsteinCoordinateIndex mdp episodes) : Real) *
          (2 * Real.exp (-2 * L)) <= 2 * delta / 25 := by
    rw [hcoordCard, hexp, hB]
    have hdenom : 0 < 5 * H * S * A * (K * H) := by positivity
    have hscale : delta <= A * H ^ 3 := by
      have hH3 : 1 <= H ^ 3 := one_le_pow₀ hH
      have hone : 1 <= A * H ^ 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hA)
          (zero_le_one.trans hH3)]
      exact hdelta_le_one.trans hone
    field_simp
    nlinarith
  have htailReal :
      (Fintype.card (OptimalTailIndex mdp episodes) : Real) *
          (2 * Real.exp (-2 * L ^ 2)) <= 2 * delta / 25 := by
    calc
      _ <= ((K * H) * S * A * (K * H)) *
          (2 * (delta / B) ^ 2) := by
        rw [htailCard]
        gcongr
      _ <= 2 * delta / 25 := by
        rw [hB]
        have hdenom : 0 < 5 * H * S * A * (K * H) := by positivity
        have hscale : delta <= H ^ 2 * S * A := by
          have hH2 : 1 <= H ^ 2 := one_le_pow₀ hH
          have hHS : 1 <= H ^ 2 * S := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hS)
              (zero_le_one.trans hH2)]
          have hone : 1 <= H ^ 2 * S * A := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hA)
              (zero_le_one.trans hHS)]
          exact hdelta_le_one.trans hone
        field_simp
        nlinarith
  have hcoordENN := ofReal_card_mul_two_mul_exp_le
    (Fintype.card (BernsteinCoordinateIndex mdp episodes))
    (Real.exp (-2 * L)) (2 * delta / 25) (Real.exp_pos _).le
    (div_nonneg (mul_nonneg (by norm_num) hdelta.le) (by norm_num)) hcoordReal
  have htailENN := ofReal_card_mul_two_mul_exp_le
    (Fintype.card (OptimalTailIndex mdp episodes))
    (Real.exp (-2 * L ^ 2)) (2 * delta / 25) (Real.exp_pos _).le
    (div_nonneg (mul_nonneg (by norm_num) hdelta.le) (by norm_num)) htailReal
  calc
    _ <= ENNReal.ofReal (2 * delta / 25) +
        ENNReal.ofReal (2 * delta / 25) := add_le_add hcoordENN htailENN
    _ = ENNReal.ofReal (4 * delta / 25) := by
      have hsmall : 0 <= 2 * delta / 25 :=
        div_nonneg (mul_nonneg (by norm_num) hdelta.le) (by norm_num)
      rw [← ENNReal.ofReal_add hsmall hsmall]
      congr 1
      ring
    _ <= ENNReal.ofReal (delta / 5) := by
      apply ENNReal.ofReal_le_ofReal
      have hfour : 4 * delta <= 5 * delta :=
        mul_le_mul_of_nonneg_right (by norm_num) hdelta.le
      nlinarith

/-- Specialized same-source confidence event probability. -/
theorem recurrentSource_trajectoryMeasure_simultaneousTransitionFailureEvent_le_fifth
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hreward : ∀ state action, |mdp.reward state action| <= 1) :
    let source := recurrentSource mdp initialState defaultState episodes delta
    source.trajectoryMeasure
        (AdaptiveEpisodeBatchSource.simultaneousTransitionFailureEvent source episodes
          (logFactor (State := State) (Action := Action)
            mdp episodes delta)) <= ENNReal.ofReal (delta / 5) := by
  dsimp only
  let source := recurrentSource mdp initialState defaultState episodes delta
  exact (AdaptiveEpisodeBatchSource.trajectoryMeasure_simultaneousTransitionFailureEvent_le
    source hreward
    episodes (logFactor (State := State) (Action := Action)
      mdp episodes delta)
    (lt_of_lt_of_le zero_lt_one
      (one_le_logFactor mdp episodes delta hhorizon hepisodes
        hdelta hdelta_le_one))).trans
    (simultaneousTransitionTailBudget_le_fifth mdp episodes delta
      hhorizon hepisodes hdelta hdelta_le_one)

end AdaptiveCumulativeHoeffdingUCBVI
end BanditRLProof.FiniteHorizonRL
