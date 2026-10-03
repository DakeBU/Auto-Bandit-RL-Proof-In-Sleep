import BanditRLProof.Algorithms.CUCBChargedConcentration

/-! Deterministic triggering on the actual CUCB law, including all horizons.
No claim is made about feedback records in null sets. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

variable {A : Type*} [MeasurableSpace A] {m : ℕ}

theorem cucbTrajectory_ae_round_property
    (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
    [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (s : Set (Round A m)) (hs : MeasurableSet s)
    (hround : ∀v, ∀ᵐ z ∂roundKernel oracle environment v, z∈s) :
    ∀ᵐ Y ∂cucbTrajectory oracle environment, ∀n, Y n∈s := by
  apply (ae_all_iff).2
  intro n
  cases n with
  | zero =>
    have h : ∀ᵐ z ∂(cucbTrajectory oracle environment).map (fun Y => Y 0), z∈s := by
      rw [cucbTrajectory_initial_law]
      exact hround _
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h
  | succ n =>
    have h : ∀ᵐ p ∂((cucbTrajectory oracle environment).map (Preorder.frestrictLe n) ⊗ₘ
        cucbStepKernel oracle environment n), p.2∈s := by
      apply Measure.ae_compProd_of_ae_ae (hs.preimage measurable_snd)
      apply Filter.Eventually.of_forall
      intro h
      exact hround (oracleInput (feedbackExtension n h) (n+1))
    rw [cucbTrajectory_prefix_compProd] at h
    exact ae_of_ae_map
      ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))).aemeasurable h

namespace ChargeData
variable (C : ChargeData A m) [Countable A] [MeasurableSingletonClass A]

def triggerSupport (i : Fin m) : Set (Round A m) :=
  {z | i∈C.triggers z.1 → z.2.1 i=true}

theorem measurableSet_triggerSupport (i : Fin m) : MeasurableSet (C.triggerSupport i) := by
  have ha : Measurable (fun a : A => decide (i∈C.triggers a)) := measurable_of_countable _
  have hm : MeasurableSet {z : Round A m | i∈C.triggers z.1} := by
    have he : {z : Round A m | i∈C.triggers z.1} =
        ((fun a : A => decide (i∈C.triggers a)) ∘ Prod.fst) ⁻¹' {true} := by
      ext z
      simp
    rw [he]
    exact (ha.comp measurable_fst) (measurableSet_singleton true)
  have ho := (measurableSet_observedSet i).preimage (show Measurable (Prod.snd : Round A m → Feedback m) from measurable_snd)
  convert hm.compl.union ho using 1
  ext z
  simp [triggerSupport, observedSet]
  tauto

omit [Countable A] [MeasurableSingletonClass A] in
theorem environment_ae_observed_of_one
    (environment : Kernel A (Feedback m)) [IsMarkovKernel environment]
    (i : Fin m) (htrigger : ∀a, i∈C.triggers a →
      C.triggerLower i≤(environment a (observedSet i)).toReal)
    (hp : C.triggerLower i=1) (a : A) (ha : i∈C.triggers a) :
    ∀ᵐ z ∂environment a, z.1 i=true := by
  have hlo := htrigger a ha
  rw [hp] at hlo
  have hq : environment a (observedSet i)=1 :=
    (ENNReal.toReal_eq_one_iff _).mp (le_antisymm measureReal_le_one hlo)
  exact (mem_ae_iff_prob_eq_one (measurableSet_observedSet i)).2 hq

theorem roundKernel_ae_triggerSupport_of_one
    (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
    [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (i : Fin m) (htrigger : ∀a, i∈C.triggers a →
      C.triggerLower i≤(environment a (observedSet i)).toReal)
    (hp : C.triggerLower i=1) (v : Input m) :
    ∀ᵐ z ∂roundKernel oracle environment v, z∈C.triggerSupport i := by
  apply Kernel.ae_compProd_of_ae_ae (C.measurableSet_triggerSupport i)
  apply Filter.Eventually.of_forall
  intro a
  by_cases ha : i∈C.triggers a
  · filter_upwards [C.environment_ae_observed_of_one environment i htrigger hp a ha] with z hz
    exact fun _ => hz
  · exact Filter.Eventually.of_forall (fun _ => fun h => (ha h).elim)

theorem counters_le_observations_ae_of_one
    (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
    [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (i : Fin m) (htrigger : ∀a, i∈C.triggers a →
      C.triggerLower i≤(environment a (observedSet i)).toReal)
    (hp : C.triggerLower i=1) :
    ∀ᵐ Y ∂cucbTrajectory oracle environment, ∀n,
      C.counters (fun t => (Y t).1) n i≤observationCount (fun t => (Y t).2) n i := by
  have h := cucbTrajectory_ae_round_property oracle environment (C.triggerSupport i)
    (C.measurableSet_triggerSupport i)
    (C.roundKernel_ae_triggerSupport_of_one oracle environment i htrigger hp)
  filter_upwards [h] with Y hY
  intro n
  apply C.counters_le_observations_of_always_triggered
  intro t ht hc
  exact hY t (C.choose_mem _ _ _ hc).2

end ChargeData
end BanditRLProof.CUCB
