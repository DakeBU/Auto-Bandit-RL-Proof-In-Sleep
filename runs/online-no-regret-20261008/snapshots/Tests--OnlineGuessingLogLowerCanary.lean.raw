import BanditRLProof.OnlineGuessingLogLower

noncomputable section
open MeasureTheory Finset Set BanditRL.OnlineLearning.GuessingLower
namespace GuessingLogLowerProbe

theorem unbalanced_probability : polyaNext [true,true,true] = (4 : ℝ)/5 ∧
    polyaNext [true,true,true] ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨by norm_num [polyaNext], probability_mem _⟩

theorem correlated_two_step_masses :
    pathWeight [true,true] = (1 : ℝ)/3 ∧ pathWeight [false,false] = (1 : ℝ)/3 ∧
    pathWeight [true,false] = (1 : ℝ)/6 ∧ pathWeight [false,true] = (1 : ℝ)/6 := by
  norm_num [pathWeight,polyaNext]

theorem zero_and_two_normalization :
    (∑ v : List.Vector Bool 0, pathWeight v.toList) = 1 ∧
    (∑ v : List.Vector Bool 2, pathWeight v.toList) = 1 :=
  ⟨prefix_mass_one 0,prefix_mass_one 2⟩

theorem correlated_moments :
    pathExpectation 2 (fun h => (h.count true : ℝ)) = 1 ∧
    pathExpectation 2 (fun h => (h.count true : ℝ)^2) = (5 : ℝ)/3 := by
  constructor
  · norm_num [expected_heads]
  · norm_num [expected_heads_sq]

theorem averaged_variance :
    pathExpectation 2 (fun h => polyaNext h * (1-polyaNext h)) = (5 : ℝ)/24 := by
  norm_num [expected_next_variance]

theorem same_past_different_current :
    causalPredict polyaNext (binaryStream [true,false]) 1 =
      causalPredict polyaNext (binaryStream [false,false]) 1 := by
  apply causalPredict_prefix
  intro i hi
  have he : i = 0 := by omega
  subst i
  norm_num [binaryStream]

theorem actual_last_prediction :
    causalPredict polyaNext (binaryStream [true,true,false]) 2 = (1 : ℝ)/2 := by
  rw [show (2 : ℕ) = [true,false].length from rfl, causalPredict_cons_last polyaNext true [true,false]]
  norm_num [polyaNext]

theorem nondegenerate_actual_regret : pathRegret polyaNext [true,true] = (13 : ℝ)/36 := by
  rw [pathRegret_eq_losses]
  rw [pathLearnerLoss_cons, pathLearnerLoss_cons]
  rw [pathBestLoss_count _ (by norm_num)]
  norm_num [pathLearnerLoss,polyaNext]

theorem actual_optimal_loss : pathBestLoss [true,false] = (1 : ℝ)/2 := by
  rw [pathBestLoss_count _ (by norm_num)]
  norm_num

theorem one_step_harmonic_endpoint :
    (1 : ℝ)/4 ≤ pathExpectation 1 (pathRegret polyaNext) := by
  have h := expected_pathRegret_lower polyaNext 1 (by norm_num)
  norm_num [harmonic] at h
  exact h

noncomputable def coinMeasure : Measure Bool :=
  BanditRLProof.Exp3.finiteActionMeasure univ (fun _ => (1 : ℝ)/2)

theorem coin_distribution : BanditRLProof.Exp3.FiniteActionDistribution
    (univ : Finset Bool) (fun _ => (1 : ℝ)/2) := by
  constructor
  · intro b _
    norm_num
  · norm_num

instance : IsProbabilityMeasure coinMeasure :=
  BanditRLProof.Exp3.finiteActionMeasure_isProbabilityMeasure univ
    (fun _ : Bool => (1 : ℝ)/2) coin_distribution

def seededPolicy (b : Bool) (_h : List Bool) : ℝ := if b then 1 else 0

theorem seeded_policy_bounds : ∀ b h, seededPolicy b h ∈ Icc (0 : ℝ) 1 := by
  intro b h
  cases b <;> norm_num [seededPolicy]

theorem genuine_coin_policy :
    seededPolicy true [] = 1 ∧ seededPolicy false [] = 0 ∧
    coinMeasure {true} = (1 : ENNReal)/2 ∧ coinMeasure {false} = (1 : ENNReal)/2 := by
  norm_num [seededPolicy,coinMeasure,BanditRLProof.Exp3.finiteActionMeasure]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem seeded_fixed_sequence_endpoint :
    ∃ v : List.Vector Bool 2, (11 : ℝ)/36 ≤ ∫ b, pathRegret (seededPolicy b) v.toList ∂coinMeasure := by
  have he := randomized_harmonic_lower coinMeasure seededPolicy
    (fun h => measurable_of_countable _) seeded_policy_bounds 2 (by norm_num)
  norm_num [harmonic] at he
  exact he

theorem seeded_log_endpoint :
    ∃ v : List.Vector Bool 2, Real.log 4 / 6 ≤ ∫ b, pathRegret (seededPolicy b) v.toList ∂coinMeasure := by
  have he := randomized_log_lower coinMeasure seededPolicy
    (fun h => measurable_of_countable _) seeded_policy_bounds 2 (by norm_num)
  norm_num at he
  exact he

theorem deterministic_fixed_sequence_endpoint (T : ℕ) (hT : 0 < T) :
    ∃ v : List.Vector Bool T, Real.log ((T : ℝ)+2)/6 ≤ pathRegret polyaNext v.toList := by
  have hb (h : List Bool) : polyaNext h ∈ Icc (0 : ℝ) 1 :=
    ⟨(probability_mem h).1.le,(probability_mem h).2.le⟩
  have he := randomized_log_lower (Measure.dirac ()) (fun _ : Unit => polyaNext)
    (fun _ => measurable_const) (fun _ h => hb h) T hT
  simpa using he

end GuessingLogLowerProbe
