from common_v1 import *
headers=load(CONTRACT/'planned-public-headers-v1.json')
addition='''
theorem pathWeight_pos (h : List Bool) : 0 < pathWeight h := by
  induction h with
  | nil => norm_num [pathWeight]
  | cons b h ih =>
    cases b
    · exact mul_pos ih (sub_pos.mpr (probability_mem h).2)
    · exact mul_pos ih (probability_mem h).1

theorem square_loss_mem (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    (x - y)^2 ∈ Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have hleft : 0 ≤ 1 - (x - y) := by linarith [hx.1,hx.2,hy.1,hy.2]
  have hright : 0 ≤ 1 + (x - y) := by linarith [hx.1,hx.2,hy.1,hy.2]
  nlinarith [mul_nonneg hleft hright]

theorem square_loss_sum_mem (T : ℕ) (p y : ℕ → ℝ)
    (hp : ∀ t < T, p t ∈ Icc (0 : ℝ) 1) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1) :
    (∑ t ∈ range T, (p t - y t)^2) ∈ Icc (0 : ℝ) T := by
  constructor
  · exact Finset.sum_nonneg (fun t _ => sq_nonneg _)
  · calc
      _ ≤ ∑ _t ∈ range T, (1 : ℝ) := Finset.sum_le_sum
        (fun t ht => (square_loss_mem _ _ (hp t (Finset.mem_range.mp ht))
          (hy t (Finset.mem_range.mp ht))).2)
      _ = _ := by simp

theorem pathRegret_abs_le (A : List Bool → ℝ) (h : List Bool)
    (hbound : ∀ k, A k ∈ Icc (0 : ℝ) 1) : |pathRegret A h| ≤ (h.length : ℝ) := by
  by_cases he : h.length = 0
  · have hn : h = [] := List.length_eq_zero_iff.mp he
    subst h
    simp [pathRegret, comparatorRegret]
  have hpos : 0 < h.length := Nat.pos_of_ne_zero he
  have hy : ∀ t < h.length, binaryValues h t ∈ Icc (0 : ℝ) 1 := by
    intro t _
    unfold binaryValues
    split_ifs <;> norm_num
  have hp : ∀ t < h.length, causalPredict A (binaryStream h) t ∈ Icc (0 : ℝ) 1 :=
    fun _ _ => hbound _
  have hm := (binary_mean_minimizer h hpos).1
  have hl := square_loss_sum_mem h.length (causalPredict A (binaryStream h)) (binaryValues h) hp hy
  have hb := square_loss_sum_mem h.length (fun _ => empiricalMean (binaryValues h) h.length)
    (binaryValues h) (fun _ _ => hm) hy
  rw [pathRegret_eq_losses, abs_le]
  change -(h.length : ℝ) ≤ _ ∧ _ ≤ (h.length : ℝ)
  constructor <;> dsimp [pathLearnerLoss,pathBestLoss] <;> linarith [hl.1,hl.2,hb.1,hb.2]

theorem pathRegret_measurable {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (h : List Bool) :
    Measurable (fun ω => pathRegret (A ω) h) := by
  unfold pathRegret comparatorRegret
  refine Measurable.sub ?_ measurable_const
  refine Finset.measurable_fun_sum _ (fun t _ => ?_)
  have hx : Measurable (fun ω => causalPredict (A ω) (binaryStream h) t - binaryValues h t) :=
    (hA _).sub measurable_const
  simpa only [pow_two] using hx.mul hx

theorem pathRegret_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ)
    (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1)
    (h : List Bool) : Integrable (fun ω => pathRegret (A ω) h) μ := by
  apply Integrable.of_bound (pathRegret_measurable A hA h).aestronglyMeasurable (h.length : ℝ)
  exact ae_of_all μ (fun ω => by
    simpa only [Real.norm_eq_abs] using pathRegret_abs_le (A ω) h (hbound ω))

'''+headers['randomized_harmonic_lower']+''' := by
  classical
  let C : ℝ := (harmonic (T + 1) : ℝ) / 6
  let B : List.Vector Bool T → ℝ := fun v => ∫ ω, pathRegret (A ω) v.toList ∂μ
  have hi (v : List.Vector Bool T) : Integrable
      (fun ω => pathWeight v.toList * pathRegret (A ω) v.toList) μ :=
    (pathRegret_integrable μ A hA hbound v.toList).const_mul _
  have he : Integrable (fun ω => pathExpectation T (pathRegret (A ω))) μ :=
    integrable_finset_sum univ (fun v _ => hi v)
  have hmean : C ≤ ∑ v : List.Vector Bool T, pathWeight v.toList * B v := by
    have hb := integral_mono (integrable_const C) he
      (fun ω => expected_pathRegret_lower (A ω) T hT)
    rw [integral_const] at hb
    simp only [measure_univ, ENNReal.toReal_one, one_smul] at hb
    rw [show (∫ ω, pathExpectation T (pathRegret (A ω)) ∂μ) =
      ∑ v : List.Vector Bool T, pathWeight v.toList * B v from by
        unfold pathExpectation
        rw [integral_finset_sum univ (fun v _ => hi v)]
        simp only [integral_const_mul]
        rfl] at hb
    exact hb
  by_contra hnone
  have hlt : ∀ v : List.Vector Bool T, B v < C := by
    intro v
    exact lt_of_not_ge (fun hv => hnone ⟨v,hv⟩)
  have hsum : (∑ v : List.Vector Bool T, pathWeight v.toList * B v) < C := by
    calc
      _ < ∑ v : List.Vector Bool T, pathWeight v.toList * C :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun v _ => mul_lt_mul_of_pos_left (hlt v) (pathWeight_pos v.toList))
      _ = C := by rw [← Finset.sum_mul, prefix_mass_one, one_mul]
  exact (not_lt_of_ge hmean) hsum

'''+headers['randomized_log_lower']+''' := by
  obtain ⟨v,hv⟩ := randomized_harmonic_lower μ A hA hbound T hT
  refine ⟨v,le_trans ?_ hv⟩
  have hl := log_add_one_le_harmonic (T + 1)
  have he : Real.log ((T : ℝ) + 2) ≤ (harmonic (T + 1) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hl
  exact div_le_div_of_nonneg_right he (by norm_num)

'''
ending='end BanditRL.OnlineLearning.GuessingLower';source=PUBLIC.read_text(encoding='utf-8')
write(RUN/'seeded-addition-v1.lean.txt',addition)
write(RUN/'leaves/seeded-v1.lean',source[:source.rindex(ending)]+addition+'\n'+ending+'\n')
gate('seeded-attempt-v1','lake','env','lean',RUN/'leaves/seeded-v1.lean')
