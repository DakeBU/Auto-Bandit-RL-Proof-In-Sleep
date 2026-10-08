import BanditRLProof.OnlineGuessingRandomizedIID
import Tests.OnlineGuessingIIDBenchmarkCanary

noncomputable section
open MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
open Tests.OnlineGuessingIIDBenchmark
open scoped ENNReal

namespace Tests.OnlineGuessingRandomizedIID

/-- A genuinely random private tape independent of an infinite IID target sequence. -/
def seededLaw : Measure (ℝ × (ℕ → ℝ)) := coinLaw.prod iidLaw

instance seededLaw_probability : IsProbabilityMeasure seededLaw := by
  unfold seededLaw
  infer_instance

def seed (ω : ℝ × (ℕ → ℝ)) : ℝ := ω.1
def target (t : ℕ) (ω : ℝ × (ℕ → ℝ)) : ℝ := ω.2 t

theorem seed_measurable : Measurable seed := measurable_fst
theorem target_measurable (t : ℕ) : Measurable (target t) :=
  (measurable_pi_apply t).comp measurable_snd

theorem seed_has_coinLaw : IdentDistrib seed (fun x : ℝ => x) seededLaw coinLaw := by
  refine ⟨seed_measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
  change (coinLaw.prod iidLaw).map Prod.fst = coinLaw.map (fun x : ℝ => x)
  simp

theorem target_has_coinLaw (t : ℕ) :
    IdentDistrib (target t) (fun x : ℝ => x) seededLaw coinLaw := by
  have h : IdentDistrib (target t) (observation t) seededLaw iidLaw := by
    refine ⟨(target_measurable t).aemeasurable, (observation_measurable t).aemeasurable, ?_⟩
    change seededLaw.map (observation t ∘ Prod.snd) = iidLaw.map (observation t)
    rw [← Measure.map_map (observation_measurable t) measurable_snd]
    simp [seededLaw]
  exact h.trans (observation_has_coinLaw t)

theorem target_sameLaw (t : ℕ) : IdentDistrib (target t) (target 0) seededLaw seededLaw :=
  (target_has_coinLaw t).trans (target_has_coinLaw 0).symm

theorem target_support (t : ℕ) : ∀ᵐ ω ∂seededLaw, target t ω ∈ Set.Icc (0 : ℝ) 1 :=
  (target_has_coinLaw t).symm.ae_mem_snd measurableSet_Icc coinLaw_support

theorem target_independent : iIndepFun target seededLaw := by
  have hm (t : ℕ) : seededLaw.map (target t) = coinLaw := by
    simpa using (target_has_coinLaw t).map_eq
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map target_measurable).2
  simp_rw [hm]
  change seededLaw.map Prod.snd = iidLaw
  simp [seededLaw]

theorem seed_independent_whole_process :
    IndepFun seed (fun ω t => target t ω) seededLaw := by
  exact indepFun_prod (μ := coinLaw) (ν := iidLaw) measurable_id measurable_id

theorem target_mean (t : ℕ) : (∫ ω, target t ω ∂seededLaw) = 1 / 2 := by
  rw [(target_has_coinLaw t).integral_eq, coinLaw_integral]
  norm_num

theorem target_variance (t : ℕ) : variance (target t) seededLaw = 1 / 4 := by
  rw [(target_has_coinLaw t).variance_eq,
    variance_eq_integral (X := fun x : ℝ => x) (μ := coinLaw) measurable_id.aemeasurable,
    coinLaw_integral, coinLaw_integral]
  norm_num

/-- Every seed value gives a feasible first prediction; the supported tape produces a fair bit. -/
def seedBit (s : ℝ) : ℝ := if s ≤ 1 / 2 then 0 else 1

theorem seedBit_measurable : Measurable seedBit := by
  unfold seedBit
  exact measurable_const.ite measurableSet_Iic measurable_const

theorem seedBit_feasible (s : ℝ) : seedBit s ∈ Set.Icc (0 : ℝ) 1 := by
  unfold seedBit
  split_ifs <;> norm_num

def seededPolicy (t : ℕ) (q : ℝ × ((↑(Finset.range t) : Type) → ℝ)) : ℝ :=
  if t = 0 then seedBit q.1 else lastPolicy t q.2

theorem seededPolicy_measurable (t : ℕ) : Measurable (seededPolicy t) := by
  unfold seededPolicy
  split_ifs
  · exact seedBit_measurable.comp measurable_fst
  · exact (lastPolicy_measurable t).comp measurable_snd

theorem seededPolicy_legal (t : ℕ) (s : ℝ) (z : (↑(Finset.range t) : Type) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) : seededPolicy t (s, z) ∈ Set.Icc (0 : ℝ) 1 := by
  unfold seededPolicy
  split_ifs
  · exact seedBit_feasible s
  · exact lastPolicy_legal t z hz

theorem policy_not_off_cube_bounded :
    ¬ (∀ t s z, seededPolicy t (s, z) ∈ Set.Icc (0 : ℝ) 1) := by
  intro h
  have bad := h 1 0 (fun _ => 2)
  norm_num [seededPolicy, lastPolicy] at bad

theorem actual_information_monotone : Monotone (privateSeedPastInformation seed target) :=
  privateSeedPastInformation_monotone seed target

theorem actual_seed_history_independent (t : ℕ) :
    IndepFun (fun ω => (seed ω, fun i : (↑(Finset.range t) : Type) => target i ω))
      (target t) seededLaw :=
  private_seed_past_independent seededLaw target target_measurable target_independent
    seed seed_measurable seed_independent_whole_process t

theorem actual_policy_current_independent (t : ℕ) :
    IndepFun (fun ω => seededPolicy t (seed ω, fun i => target i ω)) (target t) seededLaw :=
  randomized_history_policy_independent seededLaw target target_measurable target_independent
    seed seed_measurable seed_independent_whole_process seededPolicy seededPolicy_measurable t

theorem actual_randomized_excess_nonnegative (T : ℕ) :
    0 ≤ expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) T :=
  (randomized_history_policy_expectedFixed_excess seededLaw target target_measurable target_sameLaw
    target_support target_independent seed seed_measurable seed_independent_whole_process
    seededPolicy seededPolicy_measurable seededPolicy_legal T).2

theorem actual_general_information_excess_nonnegative (T : ℕ) :
    0 ≤ expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) T := by
  have hp (t : ℕ) : Measurable[privateSeedPastInformation seed target t]
      (fun ω => seededPolicy t (seed ω, fun i => target i ω)) := by
    change Measurable[MeasurableSpace.comap
      (fun ω => (seed ω, fun i : (↑(Finset.range t) : Type) => target i ω)) inferInstance] _
    exact (seededPolicy_measurable t).comp (comap_measurable _)
  have hall : ∀ᵐ ω ∂seededLaw, ∀ t, target t ω ∈ Set.Icc (0 : ℝ) 1 := ae_all_iff.2 target_support
  have hb (t : ℕ) : ∀ᵐ ω ∂seededLaw,
      seededPolicy t (seed ω, fun i => target i ω) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hall] with ω hω
    exact seededPolicy_legal t (seed ω) _ (fun i => hω i)
  exact (predictable_private_seed_expectedFixed_excess seededLaw target target_measurable target_sameLaw
    target_support target_independent seed seed_measurable seed_independent_whole_process
    (privateSeedPastInformation seed target) (fun _ => le_rfl)
    (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) hp hb T).2

theorem actual_empty_excess :
    expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) 0 = 0 := by
  have h := (randomized_history_policy_expectedFixed_excess seededLaw target target_measurable target_sameLaw
    target_support target_independent seed seed_measurable seed_independent_whole_process
    seededPolicy seededPolicy_measurable seededPolicy_legal 0).1
  simpa using h

theorem actual_two_round_excess :
    expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) 2 = 1 / 2 := by
  have hfirst : (∫ ω, (seedBit (seed ω) - 1 / 2)^2 ∂seededLaw) = 1 / 4 := by
    have hm : Measurable (fun x : ℝ => (seedBit x - 1 / 2)^2) :=
      (seedBit_measurable.sub measurable_const).pow_const 2
    have he : (∫ ω, (seedBit (seed ω) - 1 / 2)^2 ∂seededLaw) =
        ∫ x, (seedBit x - 1 / 2)^2 ∂coinLaw := by
      simpa only [Function.comp_def] using (seed_has_coinLaw.comp hm).integral_eq
    rw [he, coinLaw_integral]
    norm_num [seedBit]
  have hsecond : (∫ ω, (target 0 ω - 1 / 2)^2 ∂seededLaw) = 1 / 4 := by
    have h := variance_eq_integral (μ := seededLaw) (target_measurable 0).aemeasurable
    rw [target_mean] at h
    exact h.symm.trans (target_variance 0)
  have he := (randomized_history_policy_expectedFixed_excess seededLaw target target_measurable target_sameLaw
    target_support target_independent seed seed_measurable seed_independent_whole_process
    seededPolicy seededPolicy_measurable seededPolicy_legal 2).1
  apply he.trans
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change (∫ ω, (seedBit (seed ω) - ∫ ω, target 0 ω ∂seededLaw)^2 ∂seededLaw) +
    (∫ ω, (target 0 ω - ∫ ω, target 0 ω ∂seededLaw)^2 ∂seededLaw) = 1 / 2
  rw [target_mean, hfirst, hsecond]
  norm_num

theorem current_target_not_private_information :
    ¬ Measurable[privateSeedPastInformation seed target 0] (target 0) := by
  intro hp
  have hi := predictable_private_seed_independent seededLaw target target_measurable target_independent
    seed seed_measurable seed_independent_whole_process 0 (privateSeedPastInformation seed target 0)
    le_rfl (target 0) hp
  have hL : MemLp (target 0) 2 seededLaw :=
    memLp_of_bounded (target_support 0) (target_measurable 0).aestronglyMeasurable 2
  have he := independent_prediction_square seededLaw (target 0) (target 0) hL hL hi
  have hc : (∫ ω, (target 0 ω - ∫ ω, target 0 ω ∂seededLaw)^2 ∂seededLaw) = 1 / 4 :=
    (variance_eq_integral (μ := seededLaw) (target_measurable 0).aemeasurable).symm.trans (target_variance 0)
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero, hc, target_variance] at he
  norm_num at he

end Tests.OnlineGuessingRandomizedIID
