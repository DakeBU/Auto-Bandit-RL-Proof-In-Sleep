import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIEpisodeRegret

/-!
# Exact singleton-coordinate alignment for the recurrent UCBVI source

This file turns the variance-sensitive residual stored by the simultaneous
same-source event into the literal empirical transition mass used by the
planner.  The denominator is the actual pooled generated visit count.
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

namespace TransitionCountSummary

/-- At a positive pooled count, the singleton mass of the planner's empirical
kernel is exactly the pooled numerator divided by the pooled denominator. -/
theorem aggregateEmpiricalTransitionKernel_real_singleton_of_pos
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (state : State) (action : Action)
    (nextState : State)
    (hpos : 0 < summary.aggregateVisitCount state action) :
    (summary.aggregateEmpiricalTransitionKernel defaultState
        (state, action)).real {nextState} =
      (summary.aggregateTransitionCount state action nextState : Real) /
        (summary.aggregateVisitCount state action : Real) := by
  change
    ((summary.aggregateEmpiricalTransitionPMF defaultState state action).toMeasure).real
        {nextState} = _
  rw [Measure.real,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton nextState)]
  rw [summary.aggregateEmpiricalTransitionPMF_apply_of_aggregateVisitCount_pos
    defaultState state action nextState hpos]
  simp [ENNReal.toReal_div, ENNReal.toReal_natCast]

end TransitionCountSummary

namespace AdaptiveCumulativeHoeffdingUCBVI

theorem bernsteinCoordinateThreshold_mul_probability_div_le
    {probability logBudget visits : Real}
    (hprobability : probability ∈ Set.Icc (0 : Real) 1)
    (hlog : 0 <= logBudget) (hvisits : 0 < visits) :
    bernsteinCoordinateThreshold logBudget
          (probability * (1 - probability) * visits) / visits <=
      2 * Real.sqrt (2 * logBudget / visits) * Real.sqrt probability +
        2 * logBudget / visits := by
  let leftRoot := Real.sqrt
    (2 * (probability * (1 - probability) * visits) * logBudget) / visits
  let rightRoot := Real.sqrt (2 * logBudget / visits) * Real.sqrt probability
  have hvariance : 0 <= probability * (1 - probability) * visits :=
    mul_nonneg (mul_nonneg hprobability.1 (sub_nonneg.mpr hprobability.2))
      hvisits.le
  have hleftRoot : 0 <= leftRoot :=
    div_nonneg (Real.sqrt_nonneg _) hvisits.le
  have hrightRoot : 0 <= rightRoot :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hleftSq : leftRoot ^ 2 =
      2 * probability * (1 - probability) * logBudget / visits := by
    dsimp [leftRoot]
    rw [div_pow, Real.sq_sqrt]
    · field_simp
    · positivity
  have hrightSq : rightRoot ^ 2 =
      2 * probability * logBudget / visits := by
    dsimp [rightRoot]
    rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt]
    · ring
    · exact hprobability.1
    · positivity
  have hroot : leftRoot <= rightRoot := by
    apply (sq_le_sq₀ hleftRoot hrightRoot).mp
    rw [hleftSq, hrightSq]
    have honeMinus : 0 <= 1 - probability := sub_nonneg.mpr hprobability.2
    have hmul : probability * (1 - probability) <= probability := by
      have hOneMinusLe : 1 - probability <= 1 := by linarith [hprobability.1]
      simpa using mul_le_mul_of_nonneg_left hOneMinusLe hprobability.1
    have hcoefficient : 0 <= 2 * logBudget / visits := by positivity
    calc
      2 * probability * (1 - probability) * logBudget / visits =
          (2 * logBudget / visits) * (probability * (1 - probability)) := by ring
      _ <= (2 * logBudget / visits) * probability :=
        mul_le_mul_of_nonneg_left hmul hcoefficient
      _ = 2 * probability * logBudget / visits := by ring
  unfold bernsteinCoordinateThreshold
  rw [add_div]
  have hleftRewrite :
      2 * Real.sqrt
          (2 * (probability * (1 - probability) * visits) * logBudget) /
            visits = 2 * leftRoot := by
    dsimp [leftRoot]
    ring
  have hrightRewrite :
      2 * Real.sqrt (2 * logBudget / visits) * Real.sqrt probability =
        2 * rightRoot := by
    dsimp [rightRoot]
    ring
  rw [hleftRewrite, hrightRewrite]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : Real) <= 2)) le_rfl

/-- A finite weighted Bernstein coordinate family controls a bounded
continuation value.  The small `z/(32H)` term is the self-bounding part used by
the Bellman recursion; the remaining term is harmonic in the actual count. -/
theorem abs_sum_weight_mul_massError_le_transitionValue_div_thirtyTwo_add
    (probability empirical value : State -> Real)
    (horizon logBudget visits : Real)
    (hhorizon : 1 <= horizon) (hlog : 0 <= logBudget)
    (hvisits : 0 < visits)
    (hprobability : forall state, 0 <= probability state)
    (hvalue : forall state, value state ∈ Set.Icc (0 : Real) horizon)
    (hcoordinate : forall state,
      |empirical state - probability state| <=
        2 * Real.sqrt (2 * logBudget / visits) *
            Real.sqrt (probability state) +
          2 * logBudget / visits) :
    |∑ state : State, value state *
        (empirical state - probability state)| <=
      (∑ state : State, value state * probability state) / (32 * horizon) +
        66 * Fintype.card State * horizon ^ 2 * logBudget / visits := by
  let z : Real := ∑ state : State, value state * probability state
  let c : Real := Real.sqrt (2 * logBudget / visits)
  let cardH : Real := Fintype.card State * horizon
  have hhorizonPos : 0 < horizon := lt_of_lt_of_le (by norm_num) hhorizon
  have hz : 0 <= z := by
    exact Finset.sum_nonneg fun state _ =>
      mul_nonneg (hvalue state).1 (hprobability state)
  have hsumValue : (∑ state : State, value state) <= cardH := by
    calc
      (∑ state : State, value state) <=
          ∑ _state : State, horizon :=
        Finset.sum_le_sum fun state _ => (hvalue state).2
      _ = cardH := by simp [cardH]
  have hcardH : 0 <= cardH := by
    exact mul_nonneg (Nat.cast_nonneg _) hhorizonPos.le
  have hweightedSqrt :
      (∑ state : State, value state * Real.sqrt (probability state)) <=
        Real.sqrt z * Real.sqrt cardH := by
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset State)
      (fun state => mul_nonneg (hprobability state) (hvalue state).1)
      (fun state => (hvalue state).1)
    have hleft :
        (∑ state : State,
            Real.sqrt (probability state * value state) *
              Real.sqrt (value state)) =
          ∑ state : State, value state * Real.sqrt (probability state) := by
      apply Finset.sum_congr rfl
      intro state _
      rw [Real.sqrt_mul (hprobability state)]
      have hsquare := Real.sq_sqrt (hvalue state).1
      nlinarith [Real.sqrt_nonneg (probability state),
        Real.sqrt_nonneg (value state)]
    rw [hleft] at hcs
    have hright :
        (∑ state : State, probability state * value state) = z := by
      simp only [z]
      apply Finset.sum_congr rfl
      intro state _
      ring
    rw [hright] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hsumValue) (Real.sqrt_nonneg z))
  have hc : 0 <= c := Real.sqrt_nonneg _
  have hcSq : c ^ 2 = 2 * logBudget / visits := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hlog) hvisits.le)
  have hcardHSq : Real.sqrt cardH ^ 2 = cardH := Real.sq_sqrt hcardH
  let b : Real := c * Real.sqrt cardH
  have hb : 0 <= b := mul_nonneg hc (Real.sqrt_nonneg _)
  have hbSq : b ^ 2 = 2 * Fintype.card State * horizon * logBudget / visits := by
    dsimp [b]
    rw [mul_pow, hcSq, hcardHSq]
    field_simp
    ring
  have hsqrtZSq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz
  have hyoung :
      2 * c * (Real.sqrt z * Real.sqrt cardH) <=
        z / (32 * horizon) +
          64 * Fintype.card State * horizon ^ 2 * logBudget / visits := by
    have hrhs :
        z / (32 * horizon) +
            64 * Fintype.card State * horizon ^ 2 * logBudget / visits =
          (z + 2048 * Fintype.card State * horizon ^ 3 * logBudget / visits) /
            (32 * horizon) := by
      field_simp
      ring
    rw [hrhs, le_div_iff₀ (mul_pos (by norm_num) hhorizonPos)]
    have hsquare := sq_nonneg (Real.sqrt z - 32 * horizon * b)
    rw [show 2 * c * (Real.sqrt z * Real.sqrt cardH) =
        2 * Real.sqrt z * b by simp [b]; ring]
    ring_nf at hsquare
    rw [hbSq, hsqrtZSq] at hsquare
    ring_nf at hsquare ⊢
    nlinarith
  have hfirst :
      2 * c *
          (∑ state : State, value state * Real.sqrt (probability state)) <=
        z / (32 * horizon) +
          64 * Fintype.card State * horizon ^ 2 * logBudget / visits :=
    (mul_le_mul_of_nonneg_left hweightedSqrt
      (mul_nonneg (by norm_num) hc)).trans hyoung
  have hsecond :
      (2 * logBudget / visits) * (∑ state : State, value state) <=
        2 * Fintype.card State * horizon ^ 2 * logBudget / visits := by
    have hcoefficient : 0 <= 2 * logBudget / visits :=
      div_nonneg (mul_nonneg (by norm_num) hlog) hvisits.le
    calc
      (2 * logBudget / visits) * (∑ state : State, value state) <=
          (2 * logBudget / visits) * cardH :=
        mul_le_mul_of_nonneg_left hsumValue hcoefficient
      _ <= 2 * Fintype.card State * horizon ^ 2 * logBudget / visits := by
        dsimp [cardH]
        have hhorizonSq : horizon <= horizon ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_left hhorizon hhorizonPos.le
          nlinarith
        have hfactor :
            0 <= 2 * Fintype.card State * logBudget / visits := by
          positivity
        calc
          (2 * logBudget / visits) *
              (Fintype.card State * horizon) =
              (2 * Fintype.card State * logBudget / visits) * horizon := by ring
          _ <= (2 * Fintype.card State * logBudget / visits) * horizon ^ 2 :=
            mul_le_mul_of_nonneg_left hhorizonSq hfactor
          _ = _ := by ring
  calc
    |∑ state : State, value state *
        (empirical state - probability state)| <=
        ∑ state : State,
          |value state * (empirical state - probability state)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ state : State,
        value state * |empirical state - probability state| := by
      apply Finset.sum_congr rfl
      intro state _
      rw [abs_mul, abs_of_nonneg (hvalue state).1]
    _ <= ∑ state : State,
        value state *
          (2 * c * Real.sqrt (probability state) +
            2 * logBudget / visits) := by
      apply Finset.sum_le_sum
      intro state _
      exact mul_le_mul_of_nonneg_left
        (by simpa [c, mul_assoc] using hcoordinate state)
        (hvalue state).1
    _ = 2 * c *
          (∑ state : State, value state * Real.sqrt (probability state)) +
        (2 * logBudget / visits) * (∑ state : State, value state) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro state _
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro state _
        ring
    _ <= z / (32 * horizon) +
          64 * Fintype.card State * horizon ^ 2 * logBudget / visits +
        2 * Fintype.card State * horizon ^ 2 * logBudget / visits :=
      add_le_add hfirst hsecond
    _ = (∑ state : State, value state * probability state) /
          (32 * horizon) +
        66 * Fintype.card State * horizon ^ 2 * logBudget / visits := by
      simp only [z]
      ring

end AdaptiveCumulativeHoeffdingUCBVI

namespace AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource

/-- The simultaneous singleton event controls the exact empirical mass error
at the actual positive count.  No expected count or auxiliary sample appears. -/
theorem abs_empiricalTransitionMass_sub_lt_bernstein
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {logBudget : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes logBudget)
    (defaultState : State) (index : BernsteinCoordinateIndex mdp episodes)
    (hactual : adaptiveCumulativeAggregateVisitCountAt trajectory index.round
        index.state index.action = index.count + 1) :
    |((adaptiveCumulativeEmpiricalModelStateAt trajectory index.round).1
          |>.aggregateEmpiricalTransitionKernel defaultState
            (index.state, index.action)).real {index.nextState} -
        (mdp.transition (index.state, index.action)).real {index.nextState}| <
      bernsteinCoordinateThreshold logBudget
          (mdp.transitionCoordinateVariance
            index.state index.action index.nextState * (index.count + 1 : Nat)) /
        (index.count + 1 : Nat) := by
  let summary := (adaptiveCumulativeEmpiricalModelStateAt trajectory index.round).1
  let visits : Real := (index.count + 1 : Nat)
  let truth : Real :=
    (mdp.transition (index.state, index.action)).real {index.nextState}
  have hpos : 0 < summary.aggregateVisitCount index.state index.action := by
    change 0 < adaptiveCumulativeAggregateVisitCountAt trajectory index.round
      index.state index.action
    rw [hactual]
    exact Nat.succ_pos _
  have hvisitSum :
      (∑ i ∈ Finset.range (index.round + 1),
          source.aggregateVisitIncrement index.state index.action i trajectory) =
        (index.count + 1 : Nat) := by
    rw [source.sum_aggregateVisitIncrement_eq_prefixAggregateVisitCount]
    exact_mod_cast hactual
  have hresidual :=
    abs_coordinateResidual_lt_of_not_mem_simultaneousTransitionFailureEvent
      source htrajectory index hvisitSum
  rw [source.sum_aggregateTransitionResidualIncrement_eq_prefixAggregateResidual]
      at hresidual
  have hmass := summary.aggregateEmpiricalTransitionKernel_real_singleton_of_pos
    defaultState index.state index.action index.nextState hpos
  have hcount :
      summary.aggregateTransitionCount index.state index.action index.nextState =
        adaptiveCumulativeAggregateTransitionCountAt trajectory index.round
          index.state index.action index.nextState := rfl
  have hvisit :
      summary.aggregateVisitCount index.state index.action =
        adaptiveCumulativeAggregateVisitCountAt trajectory index.round
          index.state index.action := rfl
  have hvisitPos : 0 < visits := by
    change 0 < ((index.count + 1 : Nat) : Real)
    positivity
  rw [hmass, hcount, hvisit, hactual]
  change |(adaptiveCumulativeAggregateTransitionCountAt trajectory index.round
      index.state index.action index.nextState : Real) / visits - truth| < _
  have hrewrite :
      (adaptiveCumulativeAggregateTransitionCountAt trajectory index.round
          index.state index.action index.nextState : Real) / visits - truth =
        ((adaptiveCumulativeAggregateTransitionCountAt trajectory index.round
            index.state index.action index.nextState : Real) - visits * truth) /
          visits := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hvisitPos]
  apply (div_lt_div_iff_of_pos_right hvisitPos).2
  simpa [visits, truth, hactual] using hresidual

/-- The exact generated singleton family yields the self-bounding transition
value estimate used in the UCBVI recursion. -/
theorem abs_empiricalTransition_integral_sub_le_transitionValue_div_thirtyTwo_add
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    {episodes : Nat} {logBudget : Real}
    {trajectory : EpisodeBatchTrajectory mdp 1}
    (htrajectory : trajectory ∉
      simultaneousTransitionFailureEvent source episodes logBudget)
    (defaultState : State) (round : Fin episodes)
    (state : State) (action : Action)
    (count : Fin (episodes * mdp.horizon))
    (hactual : adaptiveCumulativeAggregateVisitCountAt trajectory round
        state action = count + 1)
    (value : State -> Real)
    (hvalue : forall nextState,
      value nextState ∈ Set.Icc (0 : Real) mdp.horizon)
    (hhorizon : 0 < mdp.horizon) (hlog : 0 <= logBudget) :
    |(∫ nextState, value nextState
          ∂TransitionCountSummary.aggregateEmpiricalTransitionKernel
            (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
            defaultState (state, action)) -
        mdp.transitionValue value state action| <=
      mdp.transitionValue value state action / (32 * mdp.horizon) +
        66 * Fintype.card State * (mdp.horizon : Real) ^ 2 * logBudget /
          (count + 1 : Nat) := by
  let summary := (adaptiveCumulativeEmpiricalModelStateAt trajectory round).1
  let empiricalMeasure :=
    summary.aggregateEmpiricalTransitionKernel defaultState (state, action)
  let truthMeasure := mdp.transition (state, action)
  let empiricalMass : State -> Real := fun nextState =>
    empiricalMeasure.real {nextState}
  let truthMass : State -> Real := fun nextState =>
    truthMeasure.real {nextState}
  let visits : Real := (count + 1 : Nat)
  have hhorizonReal : (1 : Real) <= mdp.horizon := by
    exact_mod_cast hhorizon
  have hvisits : 0 < visits := by
    change 0 < ((count + 1 : Nat) : Real)
    positivity
  have hcoordinate : forall nextState,
      |empiricalMass nextState - truthMass nextState| <=
        2 * Real.sqrt (2 * logBudget / visits) *
            Real.sqrt (truthMass nextState) +
          2 * logBudget / visits := by
    intro nextState
    let index : BernsteinCoordinateIndex mdp episodes :=
      { round := round
        state := state
        action := action
        nextState := nextState
        count := count }
    have hraw := abs_empiricalTransitionMass_sub_lt_bernstein
      source htrajectory defaultState index hactual
    have hmass : truthMass nextState ∈ Set.Icc (0 : Real) 1 :=
      ⟨measureReal_nonneg, measureReal_le_one⟩
    have htune := bernsteinCoordinateThreshold_mul_probability_div_le
      hmass hlog hvisits
    exact (le_of_lt (by simpa [index, visits, truthMass, empiricalMass,
      empiricalMeasure, truthMeasure, MDP.transitionCoordinateVariance,
      mul_assoc] using hraw)).trans (by
        simpa [visits, truthMass, MDP.transitionCoordinateVariance,
          mul_assoc] using htune)
  have hanalytic :=
    abs_sum_weight_mul_massError_le_transitionValue_div_thirtyTwo_add
      truthMass empiricalMass value (mdp.horizon : Real) logBudget visits
      hhorizonReal hlog hvisits (fun _ => measureReal_nonneg) hvalue hcoordinate
  letI : IsProbabilityMeasure empiricalMeasure := by
    dsimp [empiricalMeasure]
    exact (summary.aggregateEmpiricalTransitionKernel_isMarkov defaultState)
      |>.isProbabilityMeasure (state, action)
  have hempiricalIntegrable : Integrable value empiricalMeasure :=
    integrable_of_fintype _ _ (measurable_of_finite _)
  have hempirical :
      (∫ nextState, value nextState ∂empiricalMeasure) =
        ∑ nextState : State,
          empiricalMass nextState * value nextState := by
    rw [integral_fintype hempiricalIntegrable]
    rfl
  have htruth :
      mdp.transitionValue value state action =
        ∑ nextState : State,
          value nextState * truthMass nextState := by
    simpa [truthMass, truthMeasure] using
      mdp.transitionValue_eq_sum_measureReal value state action
  rw [hempirical, htruth]
  have hleft :
      (∑ nextState : State,
          empiricalMass nextState * value nextState) -
          ∑ nextState : State, value nextState * truthMass nextState =
        ∑ nextState : State,
          value nextState * (empiricalMass nextState - truthMass nextState) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro nextState _
    ring
  rw [hleft]
  simpa [visits] using hanalytic

end AdaptiveCumulativeHoeffdingUCBVI.AdaptiveEpisodeBatchSource

end BanditRLProof.FiniteHorizonRL
