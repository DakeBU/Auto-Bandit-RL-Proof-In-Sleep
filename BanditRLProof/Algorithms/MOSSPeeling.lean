import BanditRLProof.Algorithms.MOSS
import BanditRLProof.ConcentrationMartingaleMaximal
import BanditRLProof.ConcentrationDyadicExponential
import Mathlib.Data.Nat.Log

/-! # MOSS dyadic peeling

The source barrier and explicit dyadic maximum-event bridge for Lemma 9.3.
-/

namespace BanditRLProof.MOSS

open Real Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem logPlus_mono {x y : ℝ} (hxy : x ≤ y) : logPlus x ≤ logPlus y :=
  log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 x)) (max_le_max le_rfl hxy)

theorem exp_neg_logPlus_inv_le (x : ℝ) (hx : 0 < x) :
    exp (-logPlus (1 / x)) ≤ x := by
  have h := log_le_log (show 0 < 1 / x by positivity) (le_max_right 1 (1 / x))
  have he : -logPlus (1 / x) ≤ log x := by
    simpa [logPlus, log_div] using neg_le_neg h
  exact (exp_le_exp.mpr he).trans_eq (exp_log hx)

/-- Scaled source confidence barrier, avoiding division by the sample count. -/
noncomputable def peelingBarrier (δ gap s : ℝ) : ℝ :=
  sqrt (4 * s * logPlus (1 / (s * δ))) + s * gap

/-- Lower barrier common to one dyadic block m<=s<=2m. -/
noncomputable def blockBarrier (δ gap m : ℝ) : ℝ :=
  sqrt (4 * m * logPlus (1 / (2 * m * δ))) + m * gap

theorem blockBarrier_pos (δ gap m : ℝ) (hm : 0 < m) (hg : 0 < gap) :
    0 < blockBarrier δ gap m := by
  unfold blockBarrier
  exact add_pos_of_nonneg_of_pos (sqrt_nonneg _) (mul_pos hm hg)

theorem blockBarrier_le_peelingBarrier (δ gap m s : ℝ)
    (hδ : 0 < δ) (hg : 0 ≤ gap) (hm : 0 < m) (hms : m ≤ s) (hsm : s ≤ 2*m) :
    blockBarrier δ gap m ≤ peelingBarrier δ gap s := by
  have hs : 0 < s := hm.trans_le hms
  have hlog : logPlus (1 / (2*m*δ)) ≤ logPlus (1 / (s*δ)) := by
    apply logPlus_mono
    exact one_div_le_one_div_of_le (mul_pos hs hδ) (mul_le_mul_of_nonneg_right hsm hδ.le)
  apply add_le_add
  · apply sqrt_le_sqrt
    exact mul_le_mul (by linarith : 4*m ≤ 4*s) hlog
      (logPlus_nonneg _) (by positivity)
  · exact mul_le_mul_of_nonneg_right hms hg

/-- Scalar exponential bound used after Doob on one dyadic block. -/
theorem exp_neg_blockBarrier_sq_le (δ gap m : ℝ)
    (hδ : 0 < δ) (hg : 0 ≤ gap) (hm : 0 < m) :
    exp (-(blockBarrier δ gap m)^2 / (4*m)) ≤
      (2*m*δ) * exp (-(m*gap^2/4)) := by
  have hl := logPlus_nonneg (1 / (2*m*δ))
  have hs := sq_sqrt (show 0 ≤ 4*m*logPlus (1/(2*m*δ)) by positivity)
  have hcross : 0 ≤ sqrt (4*m*logPlus (1/(2*m*δ))) * (m*gap) := by positivity
  have hsq : 4*m*logPlus (1/(2*m*δ)) + m^2*gap^2 ≤
      (blockBarrier δ gap m)^2 := by
    unfold blockBarrier
    nlinarith
  have hexponent : -(blockBarrier δ gap m)^2 / (4*m) ≤
      -logPlus (1/(2*m*δ)) - m*gap^2/4 := by
    apply (div_le_iff₀ (show 0 < 4*m by positivity)).2
    nlinarith
  calc
    exp (-(blockBarrier δ gap m)^2 / (4*m)) ≤
        exp (-logPlus (1/(2*m*δ)) - m*gap^2/4) := exp_le_exp.mpr hexponent
    _ = exp (-logPlus (1/(2*m*δ))) * exp (-(m*gap^2/4)) := by
      rw [sub_eq_add_neg, exp_add]
    _ ≤ (2*m*δ) * exp (-(m*gap^2/4)) :=
      mul_le_mul_of_nonneg_right (exp_neg_logPlus_inv_le _ (by positivity)) (exp_pos _).le

/-- Centered partial sum in the source's one-based sample convention. -/
noncomputable def peelingSum {Ω : Type*} (X : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ range s, X (j+1) ω

/-- Maximal partial-sum event dominating one dyadic block. -/
def blockBadEvent {Ω : Type*} (X : ℕ → Ω → ℝ) (δ gap : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∃ s, s ≤ 2*m ∧ peelingSum X s ω + blockBarrier δ gap (m : ℝ) ≤ 0}

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measure_blockBadEvent_le (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (m : ℕ) (hm : 0 < m) :
    μ (blockBadEvent X δ gap m) ≤
      ENNReal.ofReal ((2*(m : ℝ)*δ) * exp (-((m : ℝ)*gap^2/4))) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hneg : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun (_ : ℕ) (x : ℝ) => -x) (fun _ => measurable_neg)
  have h := Concentration.measure_exists_le_independent_partialSum_ge_le_subgaussian
    (fun i ω => -X i ω) (fun i => (hXm i).neg) hneg
    (fun i => by simp only [integral_neg, hmean, neg_zero])
    1 (by norm_num) (fun i => (hsubG i).neg) (2*m) (by omega)
    (blockBarrier δ gap (m : ℝ)) (blockBarrier_pos δ gap _ hmR hg)
  simp only [NNReal.coe_one, mul_one, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [show (2 : ℝ)*(2*(m : ℝ)) = 4*(m : ℝ) by ring] at h
  refine (measure_mono ?_).trans (h.trans (ENNReal.ofReal_le_ofReal
    (exp_neg_blockBarrier_sq_le δ gap _ hδ hg.le hmR)))
  rintro ω ⟨s, hs, hb⟩
  refine ⟨s, hs, ?_⟩
  simp only [sum_neg_distrib]
  change peelingSum X s ω + blockBarrier δ gap (m : ℝ) ≤ 0 at hb
  unfold peelingSum at hb
  linarith

/-- All positive-sample source bad events, in scaled partial-sum form. -/
def scaledBadEvent (X : ℕ → Ω → ℝ) (δ gap : ℝ) : Set Ω :=
  {ω | ∃ s, 0 < s ∧ peelingSum X s ω + peelingBarrier δ gap (s : ℝ) ≤ 0}

/-- Countable dyadic peeling with the printed constant 15. -/
theorem measure_scaledBadEvent_le_fifteen (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) :
    μ (scaledBadEvent X δ gap) ≤ ENNReal.ofReal (15*δ/gap^2) := by
  have hcover : scaledBadEvent X δ gap ⊆ ⋃ j : ℕ, blockBadEvent X δ gap (2^j) := by
    rintro ω ⟨s, hs, hb⟩
    let j := Nat.log 2 s
    have hlow : 2^j ≤ s := Nat.pow_log_le_self 2 (Nat.ne_of_gt hs)
    have hupp : s ≤ 2*(2^j) := by
      have h := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) s).le
      simpa [j, pow_succ, Nat.mul_comm] using h
    apply Set.mem_iUnion.mpr
    refine ⟨j, s, hupp, ?_⟩
    have hbar := blockBarrier_le_peelingBarrier δ gap ((2^j : ℕ) : ℝ) (s : ℝ)
      hδ hg.le (by positivity) (by exact_mod_cast hlow) (by exact_mod_cast hupp)
    linarith
  refine (measure_mono hcover).trans ((measure_iUnion_le _).trans ?_)
  refine (ENNReal.tsum_le_tsum (fun j => ?_)).trans
    (Concentration.tsum_moss_peeling_exponential_le_fifteen δ gap hδ.le hg)
  have h := measure_blockBadEvent_le X hXm hind hmean hsubG δ gap hδ hg (2^j) (by positivity)
  convert h using 1 <;> push_cast <;> congr 1 <;> rw [pow_succ] <;> ring

/-- The actual empirical-mean bad event appearing in source Lemma 9.3. -/
def meanBadEvent (X : ℕ → Ω → ℝ) (δ gap : ℝ) : Set Ω :=
  {ω | ∃ s : ℕ, 0 < s ∧ peelingSum X s ω / (s : ℝ) +
    sqrt (4 / (s : ℝ) * logPlus (1 / ((s : ℝ)*δ))) + gap ≤ 0}

theorem meanBadEvent_subset_scaledBadEvent (X : ℕ → Ω → ℝ) (δ gap : ℝ) :
    meanBadEvent X δ gap ⊆ scaledBadEvent X δ gap := by
  rintro ω ⟨s, hs, hb⟩
  have hsR : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
  have hscale : (s : ℝ) * sqrt (4 / (s : ℝ) * logPlus (1 / ((s : ℝ)*δ))) =
      sqrt (4 * (s : ℝ) * logPlus (1 / ((s : ℝ)*δ))) := by
    calc
      _ = sqrt ((s : ℝ)^2) * sqrt (4 / (s : ℝ) * logPlus (1 / ((s : ℝ)*δ))) := by
        rw [sqrt_sq hsR.le]
      _ = sqrt ((s : ℝ)^2 * (4 / (s : ℝ) * logPlus (1 / ((s : ℝ)*δ)))) :=
        (sqrt_mul (sq_nonneg (s : ℝ)) _).symm
      _ = _ := by congr 1; field_simp
  refine ⟨s, hs, ?_⟩
  have h := mul_le_mul_of_nonneg_left hb hsR.le
  unfold peelingBarrier
  rw [mul_add, mul_add, mul_div_cancel₀ _ (ne_of_gt hsR), hscale, mul_zero] at h
  simpa only [add_assoc] using h

/-- Source Lemma 9.3, with the printed constant and actual mean/radius event.
The proof works for every positive delta, hence in particular delta in (0,1).
The explicit centered-coordinate contracts are later instantiated by MOSS. -/
theorem measure_meanBadEvent_le_fifteen (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) 1 μ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) :
    μ (meanBadEvent X δ gap) ≤ ENNReal.ofReal (15*δ/gap^2) :=
  (measure_mono (meanBadEvent_subset_scaledBadEvent X δ gap)).trans
    (measure_scaledBadEvent_le_fifteen X hXm hind hmean hsubG δ gap hδ hg)

end BanditRLProof.MOSS
