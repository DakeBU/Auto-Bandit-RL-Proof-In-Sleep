import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIRecurrentOptimism

/-! Generated episode pseudo-regret for the canonical recurrent source. -/

open MeasureTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MarkovPolicy

/-- Nonnegative deterministic rewards give nonnegative finite-horizon policy
values. -/
theorem valueRemaining_nonneg_of_reward_nonneg
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (hreward : ∀ state action, 0 <= mdp.reward state action) :
    ∀ remaining (hremaining : remaining <= mdp.horizon) state,
      0 <= policy.valueRemaining remaining hremaining state := by
  intro remaining
  induction remaining with
  | zero => simp [valueRemaining]
  | succ remaining ih =>
      intro hremaining state
      rw [valueRemaining]
      apply integral_nonneg
      intro action
      unfold MDP.bellmanQ MDP.transitionValue
      exact add_nonneg (hreward state action)
        (integral_nonneg fun nextState => ih (by omega) nextState)

end MarkovPolicy

namespace AdaptiveCumulativeHoeffdingUCBVI

/-- The recurrent Q table used at generated episode coordinate `episode`:
exactly the strict prefix `0,...,episode-1` is folded. -/
noncomputable def generatedQTable
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (episode : Nat) : QTable mdp :=
  recurrentQTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta) episode
    (fun i => (trajectory i).transitionCountSummary)

/-- The deterministic argmax table of that exact generated Q table. -/
noncomputable def generatedPolicyTable
    (mdp : MDP State Action) (defaultState : State)
    (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (episode : Nat) :
    DeterministicMarkovPolicyTable mdp :=
  recurrentPolicyTableOfSummaries mdp defaultState
    (scale (State := State) (Action := Action) mdp episodes delta) episode
    (fun i => (trajectory i).transitionCountSummary)

/-- The canonical source policy at every coordinate is definitionally the
argmax of `generatedQTable` built from its strict prefix. -/
theorem recurrentSource_policyAt_eq_generatedPolicyTable
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (episodes : Nat) (delta : Real)
    (trajectory : EpisodeBatchTrajectory mdp 1) (episode : Nat) :
    (recurrentSource mdp initialState defaultState episodes delta).policyAt
        trajectory episode =
      DeterministicMarkovPolicyTable.toMarkovPolicy
        (generatedPolicyTable mdp defaultState episodes delta trajectory episode) := by
  cases episode with
  | zero => rfl
  | succ episode => rfl

/-- Totalized initial state of one generated single-episode batch.  On the
canonical positive-horizon domain it is literally stage zero's state. -/
def generatedEpisodeInitialState
    (mdp : MDP State Action) (defaultState : State)
    (batch : EpisodeBatch mdp 1) : State :=
  if hhorizon : 0 < mdp.horizon then
    (batch 0 ⟨0, hhorizon⟩).state
  else defaultState

/-- Pathwise policy-value pseudo-regret of one generated coordinate. -/
noncomputable def generatedEpisodePseudoRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (defaultState : State) (trajectory : EpisodeBatchTrajectory mdp 1)
    (episode : Nat) : Real :=
  let state := generatedEpisodeInitialState mdp defaultState (trajectory episode)
  mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state -
    (source.policyAt trajectory episode).valueAt 0
      (Nat.zero_le mdp.horizon) state

/-- Raw generated cumulative episode pseudo-regret over exactly coordinates
`0,...,K-1`; coordinate zero is included and never hidden. -/
noncomputable def cumulativeEpisodePseudoRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (defaultState : State) (episodes : Nat)
    (trajectory : EpisodeBatchTrajectory mdp 1) : Real :=
  ∑ episode : Fin episodes,
    generatedEpisodePseudoRegret source defaultState trajectory episode

/-- Every generated policy-value pseudo-regret lies in `[0,H]` under rewards
in `[0,1]`. -/
theorem generatedEpisodePseudoRegret_mem_Icc
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (defaultState : State) (trajectory : EpisodeBatchTrajectory mdp 1)
    (episode : Nat)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1) :
    generatedEpisodePseudoRegret source defaultState trajectory episode ∈
      Set.Icc (0 : Real) mdp.horizon := by
  let state := generatedEpisodeInitialState mdp defaultState (trajectory episode)
  let policy := source.policyAt trajectory episode
  have hpolicyLe := policy.valueAt_le_optimalValueAt 0
    (Nat.zero_le mdp.horizon) state
  have hpolicyNonneg : 0 <= policy.valueAt 0
      (Nat.zero_le mdp.horizon) state := by
    exact policy.valueRemaining_nonneg_of_reward_nonneg hrewardNonneg
      mdp.horizon le_rfl state
  have hoptUpper : mdp.optimalValueAt 0 (Nat.zero_le mdp.horizon) state <=
      (mdp.horizon : Real) := by
    rw [← mdp.optimalPolicy_valueAt_eq_optimalValueAt]
    exact (le_abs_self _).trans (by
      simpa using mdp.optimalPolicy.valueRemaining_abs_le_of_rewardBound
        (1 : NNReal) (by
          intro state action
          rw [abs_of_nonneg (hrewardNonneg state action)]
          exact hrewardOne state action)
        mdp.horizon le_rfl state)
  change _ ∈ Set.Icc (0 : Real) mdp.horizon
  constructor <;> dsimp [generatedEpisodePseudoRegret, state, policy] <;> linarith

/-- Consequently the exact `K`-episode raw pseudo-regret lies in `[0,K H]`;
this is the envelope later used only on the terminal failure event. -/
theorem cumulativeEpisodePseudoRegret_mem_Icc
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState]
    (source : AdaptiveEpisodeBatchSource mdp initialState 1)
    (defaultState : State) (episodes : Nat)
    (trajectory : EpisodeBatchTrajectory mdp 1)
    (hrewardNonneg : ∀ state action, 0 <= mdp.reward state action)
    (hrewardOne : ∀ state action, mdp.reward state action <= 1) :
    cumulativeEpisodePseudoRegret source defaultState episodes trajectory ∈
      Set.Icc (0 : Real) ((episodes : Real) * mdp.horizon) := by
  constructor
  · exact Finset.sum_nonneg fun episode _ =>
      (generatedEpisodePseudoRegret_mem_Icc source defaultState trajectory episode
        hrewardNonneg hrewardOne).1
  · calc
      cumulativeEpisodePseudoRegret source defaultState episodes trajectory <=
          ∑ _episode : Fin episodes, (mdp.horizon : Real) := by
        exact Finset.sum_le_sum fun episode _ =>
          (generatedEpisodePseudoRegret_mem_Icc source defaultState trajectory episode
            hrewardNonneg hrewardOne).2
      _ = (episodes : Real) * mdp.horizon := by simp

end AdaptiveCumulativeHoeffdingUCBVI

end BanditRLProof.FiniteHorizonRL
