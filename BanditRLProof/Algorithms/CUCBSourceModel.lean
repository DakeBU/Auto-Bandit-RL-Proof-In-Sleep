import BanditRLProof.Algorithms.CUCBFeedbackModel

/-! The frozen full triggered-CUCB source model: arbitrary finite feasible
superarms, nonlinear smooth reward scores and randomized approximation oracle.
No confidence, counting or regret premise is part of this structure. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] {m : ℕ}

noncomputable def scoreOptimum (score : Input m → A → ℝ) (v : Input m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (score v)

theorem score_le_optimum (score : Input m → A → ℝ) (v : Input m) (a : A) :
    score v a≤scoreOptimum score v := Finset.le_sup' _ (Finset.mem_univ a)

noncomputable def sourceGap (score : Input m → A → ℝ) (v : Input m) (α : ℝ) (a : A) : ℝ :=
  α*scoreOptimum score v-score v a

noncomputable def maxPositiveGap (score : Input m → A → ℝ) (v : Input m) (α : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => max 0 (sourceGap score v α a))

theorem gap_le_maxPositiveGap (score : Input m → A → ℝ) (v : Input m) (α : ℝ) (a : A) :
    sourceGap score v α a≤maxPositiveGap score v α :=
  (le_max_right (0:ℝ) (sourceGap score v α a)).trans
    (Finset.le_sup' (fun b => max 0 (sourceGap score v α b)) (Finset.mem_univ a))

variable [MeasurableSpace A]

structure SourceModel (M : FeedbackModel A m) where
  score : Input m → A → ℝ
  score_nonneg : ∀v a, 0≤score v a
  score_true : ∀a, score M.trueInput a=M.expectedReward a
  modulus : ℝ → ℝ
  modulus_zero : modulus 0=0
  modulus_continuous : ContinuousOn modulus (Set.Ici 0)
  modulus_strictMono : StrictMonoOn modulus (Set.Ici 0)
  score_monotone : ∀v w, (∀i, (v i:ℝ)≤(w i:ℝ)) → ∀a, score v a≤score w a
  score_smooth : ∀v w a L, 0≤L → (∀i∈M.possible a, |(v i:ℝ)-(w i:ℝ)|≤L) →
    |score v a-score w a|≤modulus L
  alpha : ℝ
  beta : ℝ
  alpha_mem : alpha ∈ Set.Ioc (0:ℝ) 1
  beta_mem : beta ∈ Set.Ioc (0:ℝ) 1
  oracle : Kernel (Input m) A
  oracle_markov : IsMarkovKernel oracle
  oracle_success : ∀v, ENNReal.ofReal beta ≤ oracle v {a | alpha*scoreOptimum score v≤score v a}
  inverse_range : ∀d, 0<d → d≤maxPositiveGap score M.trueInput alpha →
    ∃u, 0≤u ∧ modulus u=d

namespace SourceModel
variable {M : FeedbackModel A m} (S : SourceModel M)
instance oracle_isMarkov : IsMarkovKernel S.oracle := S.oracle_markov

noncomputable def gap (a : A) : ℝ := sourceGap S.score M.trueInput S.alpha a
noncomputable def bad (a : A) : Bool := decide (0<S.gap a)

noncomputable def inverseGap (a : A) : ℝ :=
  if h : 0<S.gap a then Classical.choose (S.inverse_range (S.gap a) h
    (gap_le_maxPositiveGap S.score M.trueInput S.alpha a)) else 0

theorem inverseGap_spec (a : A) (ha : 0<S.gap a) :
    0<S.inverseGap a ∧ S.modulus (S.inverseGap a)=S.gap a := by
  have h := Classical.choose_spec (S.inverse_range (S.gap a) ha
    (gap_le_maxPositiveGap S.score M.trueInput S.alpha a))
  rw [inverseGap, dif_pos ha]
  refine ⟨lt_of_le_of_ne h.1 ?_, h.2⟩
  intro hz
  rw [← hz, S.modulus_zero] at h
  linarith [h.2]

noncomputable def chargeData : ChargeData A m := M.chargeData S.bad S.inverseGap

theorem chargeData_sufficient (N : Fin m → ℕ) (a : A) (i : Fin m)
    (h : S.chargeData.choose N a=some i) (n : ℕ)
    (hi : samplingThreshold n (S.inverseGap a) (M.minTrigger i)<N i) :
    ∀j∈M.possible a, samplingThreshold n (S.inverseGap a) (M.minTrigger j)<N j := by
  have hb := (S.chargeData.choose_mem N a i h).1
  have hgap : 0<S.gap a := by simpa [chargeData, FeedbackModel.chargeData, bad] using hb
  exact S.chargeData.choose_sufficient N a i h (S.inverseGap_spec a hgap).1
    (fun j _ => M.minTrigger_pos j) n hi

theorem optimum_monotone (v w : Input m) (h : ∀i, (v i:ℝ)≤(w i:ℝ)) :
    scoreOptimum S.score v≤scoreOptimum S.score w := by
  apply Finset.sup'_le
  intro a ha
  exact (S.score_monotone v w h a).trans (score_le_optimum S.score w a)

theorem maxPositiveGap_eq_zero_of_no_bad (h : ∀a, S.gap a≤0) :
    maxPositiveGap S.score M.trueInput S.alpha=0 := by
  have he (a : A) : max 0 (sourceGap S.score M.trueInput S.alpha a)=0 :=
    max_eq_left (h a)
  simp [maxPositiveGap, he]

theorem counters_zero_of_no_bad (h : ∀a, S.gap a≤0) (actions : ℕ → A) (n : ℕ) (i : Fin m) :
    S.chargeData.counters actions n i=0 := by
  rw [ChargeData.counters_eq_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hb : S.bad (actions t)=false := by simp [bad, not_lt.mpr (h (actions t))]
  simp [ChargeData.choose, chargeData, FeedbackModel.chargeData, hb]

end SourceModel
end BanditRLProof.CUCB
