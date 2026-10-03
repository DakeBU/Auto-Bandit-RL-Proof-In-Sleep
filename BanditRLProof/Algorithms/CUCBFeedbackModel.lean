import BanditRLProof.Algorithms.CUCBDeterministicTrigger
import BanditRLProof.Algorithms.CUCBNiceEvent

/-! Finite feasible superarms and primitive triggered-feedback laws.
Trigger minima are computed from actual environment probabilities. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

structure FeedbackModel (A : Type*) [MeasurableSpace A] (m : ℕ) where
  selected : A → Finset (Fin m)
  selected_injective : Function.Injective selected
  possible : A → Finset (Fin m)
  possible_nonempty : ∀a, (possible a).Nonempty
  selected_subset : ∀a, selected a⊆possible a
  triggerable : ∀i, ∃a, i∈possible a
  environment : Kernel A (Feedback m)
  environment_markov : IsMarkovKernel environment
  laws : Fin m → Measure UnitOutcome
  laws_probability : ∀i, IsProbabilityMeasure (laws i)
  observation_compatible : ∀a i, ObservationCompatible (environment a) (laws i) i
  possible_iff_positive : ∀a i, i∈possible a ↔ 0<(environment a (observedSet i)).toReal
  selected_observed : ∀a i, i∈selected a → environment a (observedSet i)=1
  reward_nonneg : ∀a, ∀ᵐ z ∂environment a, 0≤z.2.2
  reward_integrable : ∀a, Integrable (fun z => z.2.2) (environment a)

namespace FeedbackModel
variable {A : Type*} [MeasurableSpace A] {m : ℕ} (M : FeedbackModel A m)

instance environment_isMarkov : IsMarkovKernel M.environment := M.environment_markov
instance law_isProbability (i : Fin m) : IsProbabilityMeasure (M.laws i) := M.laws_probability i

noncomputable def trueInput : Input m := fun i => ⟨marginalMean (M.laws i), marginalMean_mem _⟩
noncomputable def expectedReward (a : A) : ℝ := ∫z, z.2.2 ∂M.environment a
noncomputable def triggerProbability (a : A) (i : Fin m) : ℝ :=
  (M.environment a (observedSet i)).toReal

theorem expectedReward_nonneg (a : A) : 0≤M.expectedReward a :=
  integral_nonneg_of_ae (M.reward_nonneg a)

theorem triggerProbability_le_one (a : A) (i : Fin m) : M.triggerProbability a i≤1 :=
  measureReal_le_one

theorem triggerProbability_pos (a : A) (i : Fin m) (hi : i∈M.possible a) :
    0<M.triggerProbability a i := (M.possible_iff_positive a i).1 hi

variable [Fintype A]

noncomputable def triggerActions (i : Fin m) : Finset A :=
  Finset.univ.filter (fun a => i∈M.possible a)

theorem mem_triggerActions (a : A) (i : Fin m) : a∈M.triggerActions i ↔ i∈M.possible a := by
  classical
  simp [triggerActions]

theorem triggerActions_nonempty (i : Fin m) : (M.triggerActions i).Nonempty := by
  obtain ⟨a, ha⟩ := M.triggerable i
  exact ⟨a, (M.mem_triggerActions a i).2 ha⟩

noncomputable def minTrigger (i : Fin m) : ℝ :=
  (M.triggerActions i).inf' (M.triggerActions_nonempty i) (fun a => M.triggerProbability a i)

theorem minTrigger_pos (i : Fin m) : 0<M.minTrigger i := by
  apply (Finset.lt_inf'_iff (M.triggerActions_nonempty i)).mpr
  intro a ha
  exact M.triggerProbability_pos a i ((M.mem_triggerActions a i).1 ha)

theorem minTrigger_le (a : A) (i : Fin m) (hi : i∈M.possible a) :
    M.minTrigger i≤M.triggerProbability a i :=
  Finset.inf'_le _ ((M.mem_triggerActions a i).2 hi)

theorem minTrigger_le_one (i : Fin m) : M.minTrigger i≤1 := by
  obtain ⟨a, ha⟩ := M.triggerable i
  exact (M.minTrigger_le a i ha).trans (M.triggerProbability_le_one a i)

/-- Source gaps will supply the two analysis fields; the trigger lower bound
is already fixed to the actual environment minimum, with its proof below. -/
noncomputable def chargeData (bad : A → Bool) (inverseGap : A → ℝ) : ChargeData A m where
  bad := bad
  triggers := M.possible
  nonempty := M.possible_nonempty
  inverseGap := inverseGap
  triggerLower := M.minTrigger

theorem chargeData_trigger_bound (bad : A → Bool) (inverseGap : A → ℝ) (i : Fin m) :
    ∀a, i∈(M.chargeData bad inverseGap).triggers a →
      (M.chargeData bad inverseGap).triggerLower i≤(M.environment a (observedSet i)).toReal :=
  fun a ha => M.minTrigger_le a i ha

variable [MeasurableSingletonClass A]

theorem deterministic_counter_bound (oracle : Kernel (Input m) A) [IsMarkovKernel oracle]
    (bad : A → Bool) (inverseGap : A → ℝ) (i : Fin m) (hp : M.minTrigger i=1) :
    ∀ᵐ Y ∂cucbTrajectory oracle M.environment, ∀n,
      (M.chargeData bad inverseGap).counters (fun t => (Y t).1) n i≤
        observationCount (fun t => (Y t).2) n i :=
  (M.chargeData bad inverseGap).counters_le_observations_ae_of_one oracle M.environment i
    (M.chargeData_trigger_bound bad inverseGap i) hp

variable [StandardBorelSpace A] [Nonempty A]

theorem charged_observation_tail (oracle : Kernel (Input m) A) [IsMarkovKernel oracle]
    (bad : A → Bool) (inverseGap : A → ℝ) (i : Fin m) (n : ℕ) (k : ℝ) (hk : 0≤k) :
    (cucbTrajectory oracle M.environment) {Y |
      k≤((M.chargeData bad inverseGap).counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k*M.minTrigger i/2} ≤
        ENNReal.ofReal (Real.exp (-k*M.minTrigger i/8)) :=
  (M.chargeData bad inverseGap).observation_below_charged_half oracle M.environment i
    (M.chargeData_trigger_bound bad inverseGap i) n k hk (M.minTrigger_pos i).le

omit [Fintype A] [MeasurableSingletonClass A] in
theorem nice_event_probability (oracle : Kernel (Input m) A) [IsMarkovKernel oracle] (n : ℕ) :
    (cucbTrajectory oracle M.environment) (NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ ≤
      ENNReal.ofReal (2*(m:ℝ)/((n:ℝ)+1)^2) :=
  niceEvent_complement_probability oracle M.environment M.laws M.observation_compatible n

end FeedbackModel
end BanditRLProof.CUCB
