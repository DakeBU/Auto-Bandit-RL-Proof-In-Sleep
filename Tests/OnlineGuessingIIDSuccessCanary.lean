import BanditRLProof.OnlineGuessingIIDSuccess
import Tests.OnlineGuessingRandomizedIIDCanary

noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics BanditRL.OnlineLearning
open Tests.OnlineGuessingIIDBenchmark Tests.OnlineGuessingRandomizedIID

namespace Tests.OnlineGuessingIIDSuccess

theorem actual_meanPredict_success :
    Tendsto (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T /
      (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T) =o[atTop]
      (fun T : ℕ => (T : ℝ)) := by
  simpa only [observation] using meanPredict_iid_success iidLaw observation
    observation_measurable observation_sameLaw observation_support observation_independent

theorem actual_meanPredict_upper (T : ℕ) (hT : 0 < T) :
    expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T ≤
      4 + 4 * Real.log T := by
  simpa only [observation] using meanPredict_expectedFixed_upper iidLaw observation
    observation_measurable observation_sameLaw observation_support T hT

theorem actual_meanPredict_two_round_positive :
    expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = 1 / 4 :=
  meanPredict_two_round_excess

theorem actual_positive_variance : variance (observation 0) iidLaw = 1 / 4 :=
  observation_variance 0

def persistentPolicy (t : ℕ) (q : ℝ × ((↑(Finset.range t) : Type) → ℝ)) : ℝ :=
  seedBit q.1

theorem persistentPolicy_measurable (t : ℕ) : Measurable (persistentPolicy t) :=
  seedBit_measurable.comp measurable_fst

theorem persistentPolicy_legal (t : ℕ) (s : ℝ) (z : (↑(Finset.range t) : Type) → ℝ)
    (_ : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) : persistentPolicy t (s, z) ∈ Set.Icc (0 : ℝ) 1 :=
  seedBit_feasible s

def persistentPrediction (t : ℕ) (ω : ℝ × (ℕ → ℝ)) : ℝ :=
  persistentPolicy t (seed ω, fun i => target i ω)

theorem persistent_excess (T : ℕ) :
    expectedFixedRegret seededLaw target persistentPrediction T = (T : ℝ) / 4 := by
  have he := (randomized_history_policy_expectedFixed_excess seededLaw target target_measurable
    target_sameLaw target_support target_independent seed seed_measurable
    seed_independent_whole_process persistentPolicy persistentPolicy_measurable persistentPolicy_legal T).1
  have hpoint (s : ℝ) : (seedBit s - (1 : ℝ) / 2)^2 = 1 / 4 := by
    unfold seedBit
    split_ifs <;> norm_num
  change expectedFixedRegret seededLaw target persistentPrediction T = _ at he
  rw [he]
  simp_rw [target_mean, persistentPolicy, hpoint]
  simp
  ring

theorem persistent_normalized_limit :
    Tendsto (fun T => expectedFixedRegret seededLaw target persistentPrediction T / (T : ℝ))
      atTop (nhds ((1 : ℝ) / 4)) := by
  have he : (fun T => expectedFixedRegret seededLaw target persistentPrediction T / (T : ℝ))
      =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ) / 4) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    rw [persistent_excess]
    have hne : (T : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hT)
    field_simp
  exact tendsto_const_nhds.congr' he.symm

theorem persistent_not_sublinear :
    ¬ (fun T => expectedFixedRegret seededLaw target persistentPrediction T) =o[atTop]
      (fun T : ℕ => (T : ℝ)) := by
  intro h
  have he := tendsto_nhds_unique h.tendsto_div_nhds_zero persistent_normalized_limit
  norm_num at he

theorem persistent_policy_not_successful :
    ¬ Tendsto (fun T => (∫ ω, ∑ t ∈ Finset.range T,
      (persistentPrediction t ω - target t ω)^2 ∂seededLaw) / (T : ℝ) -
        variance (target 0) seededLaw) atTop (nhds (0 : ℝ)) := by
  intro h
  have hi := (randomized_history_policy_success_iff seededLaw target target_measurable
    target_sameLaw target_support target_independent seed seed_measurable
    seed_independent_whole_process persistentPolicy persistentPolicy_measurable persistentPolicy_legal).2.1.mpr h
  exact persistent_not_sublinear hi

theorem zero_horizon_difference :
    ((∫ ω, ∑ t ∈ Finset.range 0, (meanPredict ω t - observation t ω)^2 ∂iidLaw) /
      (0 : ℝ) - variance (observation 0) iidLaw) = -1 / 4 ∧
    expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 0 / (0 : ℝ) = 0 := by
  simp [observation_variance]
  norm_num

theorem nonzero_initial_total_sublinear :
    (fun T : ℕ => (5 + 3 * (T : ℝ)) - (T : ℝ) * 3) =o[atTop]
      (fun T : ℕ => (T : ℝ)) := by
  apply (centered_total_sublinear_iff_average (fun T => 5 + 3 * (T : ℝ)) 3).mpr
  have he : (fun T : ℕ => (5 + 3 * (T : ℝ)) / (T : ℝ) - 3) =ᶠ[atTop]
      (fun T : ℕ => 5 / (T : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    have hne : (T : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hT)
    field_simp
    ring
  exact (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).congr' he.symm

theorem correlated_meanPredict_upper (T : ℕ) (hT : 0 < T) :
    expectedFixedRegret iidLaw (fun _ => observation 0)
      (fun t ω => meanPredict (fun _ => observation 0 ω) t) T ≤ 4 + 4 * Real.log T :=
  meanPredict_expectedFixed_upper iidLaw (fun _ => observation 0)
    (fun _ => observation_measurable 0)
    (fun _ => IdentDistrib.refl (observation_measurable 0).aemeasurable)
    (fun _ => observation_support 0) T hT

theorem correlated_meanPredict_negative_two :
    expectedFixedRegret iidLaw (fun _ => observation 0)
      (fun t ω => meanPredict (fun _ => observation 0 ω) t) 2 = -1 / 4 := by
  unfold expectedFixedRegret
  rw [repeated_target_fixed_minimum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [meanPredict, empiricalMean, observation]
  norm_num
  have hv := variance_eq_integral (μ := iidLaw) (observation_measurable 0).aemeasurable
  rw [observation_mean] at hv
  have he : (∫ ω, ((1 : ℝ) / 2 - observation 0 ω)^2 ∂iidLaw) = 1 / 4 := by
    have heq (ω : ℕ → ℝ) : (1 / 2 - observation 0 ω)^2 = (observation 0 ω - 1 / 2)^2 := by ring
    simp_rw [heq]
    exact hv.symm.trans (observation_variance 0)
  simp only [observation] at he
  linarith

end Tests.OnlineGuessingIIDSuccess
