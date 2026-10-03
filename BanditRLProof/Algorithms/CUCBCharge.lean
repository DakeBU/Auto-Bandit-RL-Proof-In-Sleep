import BanditRLProof.Algorithms.CUCBThreshold
import BanditRLProof.Algorithms.CUCBTrajectory

/-! Integer analysis counters for the repaired source charging rule.
These counters use only actions and fixed instance data, never current feedback.
They are analysis objects, not an additional learner input. -/
namespace BanditRLProof.CUCB
open MeasureTheory
set_option autoImplicit false

/-- Fixed inputs to the analysis rule. Full source model obligations are separate. -/
structure ChargeData (A : Type*) (m : ℕ) where
  bad : A → Bool
  triggers : A → Finset (Fin m)
  nonempty : ∀a, (triggers a).Nonempty
  inverseGap : A → ℝ
  triggerLower : Fin m → ℝ

instance chargeOptionMeasurableSpace (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
instance chargeOptionMeasurableSingletonClass (m : ℕ) :
    MeasurableSingletonClass (Option (Fin m)) := ⟨fun _ => trivial⟩

namespace ChargeData
variable {A : Type*} {m : ℕ} (C : ChargeData A m)

noncomputable def choose (N : Fin m → ℕ) (a : A) : Option (Fin m) :=
  if C.bad a then some (normalizedCharge (C.triggers a) (C.nonempty a)
    (fun i => (N i : ℝ)) (fun i => thresholdCoefficient (C.inverseGap a) (C.triggerLower i)))
  else none

noncomputable def counters (actions : ℕ → A) : ℕ → Fin m → ℕ
  | 0 => fun _ => 0
  | n+1 => fun i => counters actions n i +
      if C.choose (counters actions n) (actions n) = some i then 1 else 0

theorem counters_zero (actions : ℕ → A) (i : Fin m) : C.counters actions 0 i=0 := rfl

theorem counters_succ (actions : ℕ → A) (n : ℕ) (i : Fin m) :
    C.counters actions (n+1) i=C.counters actions n i+
      if C.choose (C.counters actions n) (actions n)=some i then 1 else 0 := rfl

theorem choose_mem (N : Fin m → ℕ) (a : A) (i : Fin m)
    (h : C.choose N a=some i) : C.bad a=true ∧ i∈C.triggers a := by
  unfold choose at h
  split_ifs at h with hb
  · have hi := Option.some.inj h
    exact ⟨hb, hi ▸ (normalizedCharge_spec _ _ _ _).1⟩

theorem choose_sufficient (N : Fin m → ℕ) (a : A) (i : Fin m)
    (h : C.choose N a=some i) (hu : 0<C.inverseGap a)
    (hp : ∀j∈C.triggers a, 0<C.triggerLower j) (n : ℕ)
    (hi : samplingThreshold n (C.inverseGap a) (C.triggerLower i)<N i) :
    ∀j∈C.triggers a, samplingThreshold n (C.inverseGap a) (C.triggerLower j)<N j := by
  have hb := (C.choose_mem N a i h).1
  simp only [choose, hb, if_true, Option.some.injEq] at h
  subst i
  exact normalizedCharge_sufficient _ _ _ _
    (fun j hj => thresholdCoefficient_pos hu (hp j hj)) (Real.log n) hi

theorem counters_le_time (actions : ℕ → A) (n : ℕ) (i : Fin m) :
    C.counters actions n i≤n := by
  induction n with
  | zero => simp [counters]
  | succ n ih => rw [counters_succ]; split_ifs <;> omega

theorem counters_mono_step (actions : ℕ → A) (n : ℕ) (i : Fin m) :
    C.counters actions n i≤C.counters actions (n+1) i := by
  rw [counters_succ]
  exact Nat.le_add_right _ _

theorem counters_causal (actions actions' : ℕ → A) (n : ℕ)
    (h : ∀t<n, actions t=actions' t) : C.counters actions n=C.counters actions' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun t ht => h t (by omega))
    funext i
    simp only [counters_succ, he, h n (by omega)]

/-- The charge may use the current action but not its sampled feedback. -/
theorem charge_before_feedback (Y Z : ℕ → Round A m) (n : ℕ)
    (hpast : ∀t<n, (Y t).1=(Z t).1) (hcurrent : (Y n).1=(Z n).1) :
    C.choose (C.counters (fun t => (Y t).1) n) (Y n).1 =
      C.choose (C.counters (fun t => (Z t).1) n) (Z n).1 := by
  rw [C.counters_causal _ _ n hpast, hcurrent]

theorem counters_sum (actions : ℕ → A) (n : ℕ) :
    ∑i:Fin m, C.counters actions n i = ∑t∈Finset.range n, if C.bad (actions t) then 1 else 0 := by
  classical
  induction n with
  | zero => simp [counters]
  | succ n ih =>
    simp only [counters_succ, Finset.sum_add_distrib, ih, Finset.sum_range_succ]
    congr 1
    cases hb : C.bad (actions n)
    · simp [choose, hb]
    · simp [choose, hb, eq_comm]

theorem counters_eq_sum (actions : ℕ → A) (n : ℕ) (i : Fin m) :
    C.counters actions n i = ∑t∈Finset.range n,
      if C.choose (C.counters actions t) (actions t)=some i then 1 else 0 := by
  induction n with
  | zero => simp [counters]
  | succ n ih => rw [counters_succ, Finset.sum_range_succ, ih]

noncomputable def chargedObservations (Y : ℕ → Round A m) (n : ℕ) (i : Fin m) : ℕ :=
  ∑t∈Finset.range n, if C.choose (C.counters (fun s => (Y s).1) t) (Y t).1=some i ∧
    (Y t).2.1 i=true then 1 else 0

theorem chargedObservations_le_observationCount (Y : ℕ → Round A m) (n : ℕ) (i : Fin m) :
    C.chargedObservations Y n i≤observationCount (fun t => (Y t).2) n i := by
  apply Finset.sum_le_sum
  intro t ht
  split_ifs <;> simp_all

theorem chargedObservations_le_counters (Y : ℕ → Round A m) (n : ℕ) (i : Fin m) :
    C.chargedObservations Y n i≤C.counters (fun t => (Y t).1) n i := by
  rw [counters_eq_sum]
  apply Finset.sum_le_sum
  intro t ht
  split_ifs <;> simp_all

/-- Deterministic triggering is recovered without a probabilistic tail bound. -/
theorem counters_le_observations_of_always_triggered (Y : ℕ → Round A m) (n : ℕ) (i : Fin m)
    (h : ∀t<n, C.choose (C.counters (fun s => (Y s).1) t) (Y t).1=some i →
      (Y t).2.1 i=true) :
    C.counters (fun t => (Y t).1) n i≤observationCount (fun t => (Y t).2) n i := by
  rw [counters_eq_sum]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hc : C.choose (C.counters (fun s => (Y s).1) t) (Y t).1=some i
  · simp [hc, h t (Finset.mem_range.mp ht) hc]
  · simp [hc]

variable [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

theorem measurable_choose : Measurable (fun p : (Fin m → ℕ) × A => C.choose p.1 p.2) :=
  measurable_of_countable _

theorem measurable_counters (n : ℕ) : Measurable (fun actions : ℕ → A => C.counters actions n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_pi_lambda
    intro i
    have hc := C.measurable_choose.comp (ih.prodMk (measurable_pi_apply n))
    exact ((measurable_pi_apply i).comp ih).add
      (measurable_const.ite (hc (measurableSet_singleton (some i))) measurable_const)

theorem measurable_path_charge (n : ℕ) : Measurable (fun Y : ℕ → Round A m =>
    C.choose (C.counters (fun t => (Y t).1) n) (Y n).1) := by
  have ha : Measurable (fun Y : ℕ → Round A m => fun t => (Y t).1) := by fun_prop
  exact C.measurable_choose.comp (((C.measurable_counters n).comp ha).prodMk (by fun_prop))

end ChargeData
end BanditRLProof.CUCB



