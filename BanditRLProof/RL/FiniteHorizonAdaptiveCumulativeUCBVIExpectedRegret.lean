import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVITerminal

/-!
# Expected regret of the canonical generated Hoeffding UCBVI-CH source

This file first closes the small measurability bridge from the recurrent
finite table to policy-value pseudo-regret.  It then integrates the compiled
high-probability terminal, charging the deterministic `K H` envelope only on
the measurable hull of the proved failure event.  The resulting corollary
therefore retains the required `K H delta` term.
-/

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

theorem measurable_generatedPolicyTable
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real) (episode : Nat) :
    Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      generatedPolicyTable mdp defaultState episodes delta trajectory episode) := by
  cases episode with
  | zero =>
      change Measurable (fun _ : EpisodeBatchTrajectory mdp 1 =>
        recurrentInitialTable mdp)
      exact measurable_const
  | succ episode =>
      change Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
        recurrentSuccessorTable defaultState
          (scale (State := State) (Action := Action) mdp episodes delta)
          episode (Preorder.frestrictLe episode trajectory))
      exact (measurable_recurrentSuccessorTable defaultState
        (scale (State := State) (Action := Action) mdp episodes delta)
        episode).comp (Preorder.measurable_frestrictLe episode)

theorem measurable_generatedEpisodeInitialState
    (mdp : MDP State Action) (defaultState : State) :
    Measurable (generatedEpisodeInitialState mdp defaultState) := by
  unfold generatedEpisodeInitialState
  split_ifs with hhorizon
  ·
    exact EpisodeStep.measurable_state.comp
      ((measurable_pi_apply (⟨0, hhorizon⟩ : Fin mdp.horizon)).comp
        (measurable_pi_apply (0 : Fin 1)))
  ·
    exact measurable_const

theorem measurable_generatedEpisodePseudoRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (episode : Nat) :
    Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      generatedEpisodePseudoRegret
        (recurrentSource mdp initialState defaultState episodes delta)
        defaultState trajectory episode) := by
  let state : EpisodeBatchTrajectory mdp 1 → State := fun trajectory =>
    generatedEpisodeInitialState mdp defaultState (trajectory episode)
  have hstate : Measurable state :=
    (measurable_generatedEpisodeInitialState mdp defaultState).comp
      (measurable_pi_apply episode)
  let regretOf : DeterministicMarkovPolicyTable mdp × State → Real :=
    fun pair =>
      mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) pair.2 -
        pair.1.toMarkovPolicy.valueAt 0
          (Nat.zero_le mdp.horizon) pair.2
  have hregretOf : Measurable regretOf := measurable_of_countable _
  have hpair : Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      (generatedPolicyTable mdp defaultState episodes delta trajectory episode,
        state trajectory)) :=
    (measurable_generatedPolicyTable mdp defaultState episodes delta episode).prodMk
      hstate
  simpa only [generatedEpisodePseudoRegret,
    recurrentSource_policyAt_eq_generatedPolicyTable, state, regretOf] using
    hregretOf.comp hpair

theorem measurable_cumulativeEpisodePseudoRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real) :
    Measurable (fun trajectory : EpisodeBatchTrajectory mdp 1 =>
      cumulativeEpisodePseudoRegret
        (recurrentSource mdp initialState defaultState episodes delta)
        defaultState episodes trajectory) := by
  unfold cumulativeEpisodePseudoRegret
  exact Finset.measurable_sum Finset.univ fun episode _ =>
    measurable_generatedEpisodePseudoRegret mdp initialState defaultState
      episodes delta episode

/-- Canonical finite-time expected pseudo-regret.  The `K H delta` summand is
the explicit contribution of the proved terminal failure event. -/
theorem integral_cumulativeEpisodePseudoRegret_recurrentSource_le_canonicalRegretBound_add_failure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace (EpisodeBatch mdp 1)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp 1)]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (hhorizon : 0 < mdp.horizon) (hepisodes : 0 < episodes)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1) :
    let source := recurrentSource mdp initialState defaultState episodes delta
    ∫ trajectory, cumulativeEpisodePseudoRegret source defaultState episodes trajectory
        ∂source.trajectoryMeasure <=
      canonicalRegretBound (State := State) (Action := Action)
          mdp episodes delta +
        (episodes : Real) * mdp.horizon * delta := by
  dsimp only
  let source := recurrentSource mdp initialState defaultState episodes delta
  let μ := source.trajectoryMeasure
  let regret : EpisodeBatchTrajectory mdp 1 → Real := fun trajectory =>
    cumulativeEpisodePseudoRegret source defaultState episodes trajectory
  let bound := canonicalRegretBound (State := State) (Action := Action)
    mdp episodes delta
  let envelope : Real := episodes * mdp.horizon
  let failure := canonicalFailureEvent (mdp := mdp) (initialState := initialState)
    defaultState episodes delta
  let bad := toMeasurable μ failure
  let overflow : EpisodeBatchTrajectory mdp 1 → Real :=
    bad.indicator (fun _ => envelope)
  have hregretMeasurable : Measurable regret :=
    measurable_cumulativeEpisodePseudoRegret mdp initialState defaultState
      episodes delta
  have hregretBound : ∀ trajectory, |regret trajectory| <= envelope := by
    intro trajectory
    have hmem := cumulativeEpisodePseudoRegret_mem_Icc source defaultState
      episodes trajectory hrewardNonneg hrewardOne
    rw [abs_of_nonneg hmem.1]
    exact hmem.2
  have hregretIntegrable : Integrable regret μ := by
    exact (integrable_const envelope).mono'
      hregretMeasurable.aestronglyMeasurable (ae_of_all μ hregretBound)
  have hbad : MeasurableSet bad := measurableSet_toMeasurable _ _
  have hoverflow : Integrable overflow μ :=
    (integrable_const envelope).indicator hbad
  have hbound : 0 <= bound := canonicalRegretBound_nonneg mdp episodes delta
  have hpoint : ∀ trajectory, regret trajectory <= bound + overflow trajectory := by
    intro trajectory
    by_cases htrajectory : trajectory ∈ bad
    · have hupper := (cumulativeEpisodePseudoRegret_mem_Icc source defaultState
        episodes trajectory hrewardNonneg hrewardOne).2
      calc
        regret trajectory <= envelope := hupper
        _ <= bound + envelope := le_add_of_nonneg_left hbound
        _ = bound + overflow trajectory := by
          simp [overflow, Set.indicator_of_mem htrajectory]
    · have hnotFailure : trajectory ∉ failure := by
        intro hfailure
        exact htrajectory (subset_toMeasurable μ failure hfailure)
      have hgood := cumulativeEpisodePseudoRegret_le_canonicalRegretBound_of_not_mem
        mdp initialState defaultState episodes delta hhorizon hepisodes
          hdelta hdelta_le_one hrewardNonneg hrewardOne trajectory hnotFailure
      calc
        regret trajectory <= bound := hgood
        _ = bound + overflow trajectory := by
          simp [overflow, Set.indicator_of_notMem htrajectory]
  have htail : μ failure <= ENNReal.ofReal delta :=
    recurrentSource_trajectoryMeasure_canonicalFailureEvent_le
      mdp initialState defaultState episodes delta hhorizon hepisodes
        hdelta hdelta_le_one hrewardNonneg hrewardOne
  have htailReal : μ.real bad <= delta := by
    rw [Measure.real, measure_toMeasurable]
    calc
      (μ failure).toReal <= (ENNReal.ofReal delta).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
      _ = delta := ENNReal.toReal_ofReal hdelta.le
  change integral μ regret <= bound + envelope * delta
  calc
    integral μ regret <= integral μ (fun trajectory =>
        bound + overflow trajectory) := by
      exact integral_mono hregretIntegrable
        ((integrable_const bound).add hoverflow) hpoint
    _ = bound + integral μ overflow := by
      rw [integral_add (integrable_const bound) hoverflow, integral_const]
      simp [MeasureTheory.probReal_univ]
    _ = bound + envelope * μ.real bad := by
      congr 1
      change integral μ (bad.indicator (fun _ => envelope)) =
        envelope * μ.real bad
      rw [integral_indicator hbad, setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]
    _ <= bound + envelope * delta := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left htailReal (by positivity))

end AdaptiveCumulativeHoeffdingUCBVI
end BanditRLProof.FiniteHorizonRL
