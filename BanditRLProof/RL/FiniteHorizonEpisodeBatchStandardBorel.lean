import BanditRLProof.RL.FiniteHorizonAdaptiveEpisodeBatchLaw
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration

/-!
# Standard Borel instances for finite-horizon episode batches

`EpisodeStep` uses an explicit product-coordinate `MeasurableSpace.comap`, so
the generic product instance is not visible to typeclass search.  This module
transports a Polish topology through the coordinate equivalence and then
installs the corresponding Standard Borel instance.  The deterministic and
stochastic infinite batch trajectories are countable products of their finite
batch spaces.

The episode-step instance needs only measurable Standard Borel state and action
spaces.  The stochastic batch-trajectory wrapper additionally inherits finite
state and action spaces from the finite-horizon aliases.  These instances close
a regularity boundary only.  They do not supply any probability law,
independence, support, concentration, or regret property.
-/

namespace BanditRLProof.FiniteHorizonRL

universe u v

namespace EpisodeStep

variable {State : Type u} {Action : Type v}

/-- Product coordinates underlying the measurable structure on `EpisodeStep`. -/
def toProdEquiv : EpisodeStep State Action ≃ State × Action × Real × State where
  toFun step := (step.state, step.action, step.reward, step.nextState)
  invFun data :=
    { state := data.1
      action := data.2.1
      reward := data.2.2.1
      nextState := data.2.2.2 }
  left_inv step := by cases step; rfl
  right_inv data := by rcases data with ⟨state, action, reward, nextState⟩; rfl

/--
The product-coordinate measurable structure on an episode step is Standard
Borel whenever the state and action spaces are Standard Borel.
-/
noncomputable instance instStandardBorelSpace
    [MeasurableSpace State] [MeasurableSpace Action]
    [StandardBorelSpace State] [StandardBorelSpace Action] :
    StandardBorelSpace (EpisodeStep State Action) := by
  let e := toProdEquiv (State := State) (Action := Action)
  letI := upgradeStandardBorel (State × Action × Real × State)
  letI : TopologicalSpace (EpisodeStep State Action) :=
    TopologicalSpace.induced e inferInstance
  have hemb : MeasurableEmbedding e := by
    rw [MeasurableEmbedding.iff_comap_eq]
    exact ⟨e.injective, rfl, by simp⟩
  letI : BorelSpace (EpisodeStep State Action) :=
    hemb.borelSpace (Topology.IsInducing.induced e)
  letI : PolishSpace (EpisodeStep State Action) := e.polishSpace_induced
  infer_instance

end EpisodeStep

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

/-- A stochastic infinite batch trajectory is a countable Borel product. -/
noncomputable instance instStochasticEpisodeBatchTrajectoryStandardBorelSpace
    {mdp : MDP State Action} {episodes : Nat}
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)] :
    StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes) := by
  letI : ∀ _ : Nat, StandardBorelSpace (StochasticEpisodeBatch mdp episodes) :=
    fun _ => inferInstance
  exact StandardBorelSpace.pi_countable

end BanditRLProof.FiniteHorizonRL
