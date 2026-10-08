import Tests.OnlineLearningFoundationsCanary
import Tests.OnlineGuessingIIDBenchmarkCanary
import BanditRLProof.OnlineLearningHistory

noncomputable section
open MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
namespace Tests.OnlineLearningCoreAudit
open Tests.OnlineGuessingIIDBenchmark

/-- Test-only modification off the null support, needed by the legacy pointwise APIs. -/
def clip (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clip_measurable : Measurable clip := by
  exact measurable_const.max (measurable_const.min measurable_id)

theorem clip_unit (x : ℝ) : clip x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_fixed {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clip x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

def boundedObservation (t : ℕ) (ω : ℕ → ℝ) : ℝ := clip (observation t ω)

theorem bounded_measurable (t : ℕ) : Measurable (boundedObservation t) :=
  clip_measurable.comp (observation_measurable t)

theorem bounded_support (t : ℕ) (ω : ℕ → ℝ) :
    boundedObservation t ω ∈ Set.Icc (0 : ℝ) 1 := clip_unit _

theorem bounded_eq_original_ae (t : ℕ) :
    boundedObservation t =ᶠ[ae iidLaw] observation t := by
  filter_upwards [observation_support t] with ω hω
  exact clip_fixed hω

theorem clipping_is_not_pointwise_identity :
    boundedObservation 0 (fun _ => 2) = 1 ∧ observation 0 (fun _ => 2) = 2 := by
  norm_num [boundedObservation, clip, observation]

theorem bounded_independent : iIndepFun boundedObservation iidLaw :=
  observation_independent.comp (fun _ => clip) (fun _ => clip_measurable)

theorem bounded_sameLaw (t : ℕ) :
    IdentDistrib (boundedObservation t) (boundedObservation 0) iidLaw iidLaw :=
  (observation_sameLaw t).comp clip_measurable

theorem bounded_mean (t : ℕ) : (∫ ω, boundedObservation t ω ∂iidLaw) = 1 / 2 := by
  rw [integral_congr_ae (bounded_eq_original_ae t), observation_mean]

theorem bounded_variance (t : ℕ) : variance (boundedObservation t) iidLaw = 1 / 4 := by
  rw [variance_congr (bounded_eq_original_ae t), observation_variance]

theorem bounded_memLp (t : ℕ) : MemLp (boundedObservation t) 2 iidLaw :=
  memLp_of_bounded (Filter.Eventually.of_forall (bounded_support t))
    (bounded_measurable t).aestronglyMeasurable 2

/-- The generic fixed-comparator identity permits u outside the legal game interval. -/
theorem outside_comparator_loss :
    (∫ ω, ((2 : ℝ) - boundedObservation 0 ω)^2 ∂iidLaw) = 5 / 2 := by
  rw [expected_square_decomposition iidLaw (boundedObservation 0) (bounded_memLp 0) 2,
    bounded_variance, bounded_mean]
  norm_num

/-- The supplied-independence consumer is instantiated with a genuinely random P and Y. -/
theorem independent_coordinate_loss :
    (∫ ω, (boundedObservation 0 ω - boundedObservation 1 ω)^2 ∂iidLaw) = 1 / 2 := by
  have he := independent_prediction_square iidLaw (boundedObservation 0) (boundedObservation 1)
    (bounded_memLp 0) (bounded_memLp 1)
    (bounded_independent.indepFun (by norm_num : (0 : ℕ) ≠ 1))
  have hc := variance_eq_integral (μ := iidLaw) (bounded_measurable 0).aemeasurable
  rw [bounded_mean] at hc
  simp_rw [bounded_mean, bounded_variance] at he
  rw [← hc, bounded_variance] at he
  norm_num at he
  exact he

theorem actual_mean_independent (t : ℕ) :
    IndepFun (fun ω => meanPredict (fun i => boundedObservation i ω) t)
      (boundedObservation t) iidLaw :=
  meanPredict_independent iidLaw boundedObservation bounded_measurable bounded_independent t

theorem actual_mean_measurable (t : ℕ) :
    Measurable (fun ω => meanPredict (fun i => boundedObservation i ω) t) :=
  meanPredict_measurable boundedObservation bounded_measurable t

theorem actual_mean_memLp (t : ℕ) :
    MemLp (fun ω => meanPredict (fun i => boundedObservation i ω) t) 2 iidLaw :=
  meanPredict_memLp iidLaw boundedObservation bounded_measurable bounded_support t

theorem actual_mean_excess_identity (T : ℕ) :
    (∫ ω, ∑ t ∈ Finset.range T,
      (meanPredict (fun i => boundedObservation i ω) t - boundedObservation t ω)^2 ∂iidLaw) -
      T * variance (boundedObservation 0) iidLaw =
        ∑ t ∈ Finset.range T,
          ∫ ω, (meanPredict (fun i => boundedObservation i ω) t -
            ∫ ω, boundedObservation 0 ω ∂iidLaw)^2 ∂iidLaw :=
  iid_meanPredict_excess iidLaw boundedObservation bounded_measurable bounded_independent
    bounded_sameLaw bounded_support T

theorem actual_mean_excess_nonnegative (T : ℕ) :
    0 ≤ (∫ ω, ∑ t ∈ Finset.range T,
      (meanPredict (fun i => boundedObservation i ω) t - boundedObservation t ω)^2 ∂iidLaw) -
      T * variance (boundedObservation 0) iidLaw :=
  iid_meanPredict_excess_nonneg iidLaw boundedObservation bounded_measurable bounded_independent
    bounded_sameLaw bounded_support T

/-- Finite positive excess for the same source learner; no limit is asserted by this audit. -/
theorem actual_mean_two_round_excess :
    (∫ ω, ∑ t ∈ Finset.range 2,
      (meanPredict (fun i => boundedObservation i ω) t - boundedObservation t ω)^2 ∂iidLaw) -
      2 * variance (boundedObservation 0) iidLaw = 1 / 4 := by
  have he := actual_mean_excess_identity 2
  have hc := variance_eq_integral (μ := iidLaw) (bounded_measurable 0).aemeasurable
  rw [bounded_mean] at hc
  have hcenter : (∫ ω, (boundedObservation 0 ω - 1 / 2)^2 ∂iidLaw) = 1 / 4 :=
    hc.symm.trans (bounded_variance 0)
  simp_rw [bounded_mean] at he
  simp [Finset.sum_range_succ, meanPredict, empiricalMean] at he
  exact he.trans (by simpa only [one_div] using hcenter)

theorem actual_mean_optimal :
    (∫ ω, boundedObservation 0 ω ∂iidLaw) ∈ Set.Icc (0 : ℝ) 1 ∧
    (∫ ω, ((∫ ω, boundedObservation 0 ω ∂iidLaw) - boundedObservation 0 ω)^2 ∂iidLaw) =
      variance (boundedObservation 0) iidLaw ∧
    ∀ u : ℝ, variance (boundedObservation 0) iidLaw ≤
      ∫ ω, (u - boundedObservation 0 ω)^2 ∂iidLaw :=
  source_mean_optimal iidLaw (boundedObservation 0) (bounded_measurable 0) (bounded_support 0)

/-- Clip the off-cube last-policy outputs to satisfy every-tuple boundedness exactly. -/
def boundedLast (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ) : ℝ := clip (lastPolicy t z)

theorem boundedLast_measurable (t : ℕ) : Measurable (boundedLast t) :=
  clip_measurable.comp (lastPolicy_measurable t)

theorem boundedLast_unit (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ) :
    boundedLast t z ∈ Set.Icc (0 : ℝ) 1 := clip_unit _

theorem boundedLast_legal_identity (t : ℕ) (z : (↑(Finset.range t) : Type) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) : boundedLast t z = lastPolicy t z :=
  clip_fixed (lastPolicy_legal t z hz)

theorem actual_history_independent (t : ℕ) :
    IndepFun (fun ω => boundedLast t (fun i => boundedObservation i ω))
      (boundedObservation t) iidLaw :=
  history_policy_independent iidLaw boundedObservation bounded_measurable bounded_independent
    t (boundedLast t) (boundedLast_measurable t)

theorem actual_history_lower (t : ℕ) :
    (1 : ℝ) / 4 ≤ ∫ ω,
      (boundedLast t (fun i => boundedObservation i ω) - boundedObservation t ω)^2 ∂iidLaw := by
  simpa [bounded_variance] using history_policy_loss_ge_variance iidLaw boundedObservation
    bounded_measurable bounded_independent bounded_support t (boundedLast t)
    (boundedLast_measurable t) (boundedLast_unit t)

theorem actual_history_one_loss :
    (∫ ω, (boundedLast 1 (fun i => boundedObservation i ω) - boundedObservation 1 ω)^2 ∂iidLaw) =
      1 / 2 := by
  have hp : ∀ ω, boundedLast 1 (fun i => boundedObservation i ω) = boundedObservation 0 ω := by
    intro ω
    rw [boundedLast_legal_identity 1 _ (fun i => bounded_support i ω)]
    norm_num [lastPolicy]
  simp_rw [hp]
  exact independent_coordinate_loss

/-- Independent but non-identically distributed: the first target is deterministic zero. -/
def heterogeneous (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  if t = 0 then 0 else boundedObservation t ω

theorem heterogeneous_measurable (t : ℕ) : Measurable (heterogeneous t) := by
  unfold heterogeneous
  split_ifs
  · exact measurable_const
  · exact bounded_measurable t

theorem heterogeneous_unit (t : ℕ) (ω : ℕ → ℝ) :
    heterogeneous t ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold heterogeneous
  split_ifs
  · norm_num
  · exact bounded_support t ω

theorem heterogeneous_independent : iIndepFun heterogeneous iidLaw := by
  have h := bounded_independent.comp
    (fun t => fun x : ℝ => if t = 0 then 0 else x)
    (by intro t; dsimp only; split_ifs <;> fun_prop)
  simpa [Function.comp_def, heterogeneous] using h

theorem heterogeneous_not_sameLaw :
    ¬ IdentDistrib (heterogeneous 1) (heterogeneous 0) iidLaw iidLaw := by
  intro h
  have hv := h.variance_eq
  have h1 : heterogeneous 1 = boundedObservation 1 := by ext ω; simp [heterogeneous]
  have h0 : heterogeneous 0 = 0 := by ext ω; simp [heterogeneous]
  rw [h1, h0, bounded_variance, variance_zero] at hv
  norm_num at hv

theorem nonidentical_current_variance_lower :
    (1 : ℝ) / 4 ≤ ∫ ω,
      (boundedLast 1 (fun i => heterogeneous i ω) - heterogeneous 1 ω)^2 ∂iidLaw := by
  have h := history_policy_loss_ge_variance iidLaw heterogeneous heterogeneous_measurable
    heterogeneous_independent heterogeneous_unit 1 (boundedLast 1)
    (boundedLast_measurable 1) (boundedLast_unit 1)
  have h1 : heterogeneous 1 = boundedObservation 1 := by ext ω; simp [heterogeneous]
  rw [h1, bounded_variance] at h
  exact h

theorem positive_scalar_normalization :
    (2 : ℝ) / (2 : ℕ) - 1 / 4 = (2 - (2 : ℕ) * (1 / 4 : ℝ)) / (2 : ℕ) :=
  normalized_excess 2 (1 / 4) 2 (by norm_num)

theorem zero_horizon_discrepancy :
    (0 : ℝ) / (0 : ℕ) - 1 / 4 = -(1 / 4) ∧
    ((0 : ℝ) - (0 : ℕ) * (1 / 4)) / (0 : ℕ) = 0 ∧
    (0 : ℝ) / (0 : ℕ) - 1 / 4 ≠ ((0 : ℝ) - (0 : ℕ) * (1 / 4)) / (0 : ℕ) := by
  norm_num

end Tests.OnlineLearningCoreAudit
