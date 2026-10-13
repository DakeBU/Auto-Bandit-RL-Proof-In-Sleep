/-
Derived support for Orabona v10 Example 2.14 (printed p15/PDF27), using the
actual Chapter 1 strict-prefix mean predictor (printed p4/PDF16).
On the same all-zero real labels, the mean predictor starts at 1/2 and has
cumulative square loss 1/4. The actual horizon-tuned projected OGD starts at 1
and has loss at least n/4 at T=(2*n)^2, so their gap is at least n/4-1/4 and
exceeds every real threshold at some n above every natural cutoff.
These are derived comparison refinements, not numerical results printed in the
book, an equal-initialization comparison, an every-stream/every-initialization
claim, or a minimax/Chapter 4 theorem. The horizon is known for each separate
tuned run; this is not a single horizon-independent algorithm or future-label
optimization. Zero comparator loss is optimal on this fixed stream. At n=1 the
displayed lower gap is zero. Existing source contracts and library are reused;
this module alone does not accept Chapter 1, Chapter 2 or the whole book.
-/

import BanditRLProof.OnlineGuessingLower
import BanditRLProof.OnlineLearningFTL

open Set Finset
namespace BanditRL.OnlineGradientDescent

theorem meanPredict_zero_cumulativeLoss (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T,
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = 1/4 := by
  have hp (t : ℕ) :
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2 =
        if t = 0 then (1/4 : ℝ) else 0 := by
    by_cases ht : t = 0
    · simp [BanditRL.OnlineLearning.meanPredict, ht]
      norm_num
    · simp [BanditRL.OnlineLearning.meanPredict,
        BanditRL.OnlineLearning.empiricalMean, ht]
  simp_rw [hp]
  simpa [hT] using (Finset.sum_ite_eq' (range T) 0 (fun _ => (1/4 : ℝ)))

theorem guessing_vs_mean_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ)/4 - 1/4 ≤
      regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by
  rw [meanPredict_zero_cumulativeLoss ((2*n)^2) (by positivity)]
  exact sub_le_sub_right (guessing_squared_horizon_lower n hn) (1/4)

theorem guessing_vs_mean_unbounded (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      C < regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (4*C+1) (N : ℝ))
  have hNC : (N : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hN : N < n := by exact_mod_cast hNC
  have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le N) hN
  refine ⟨n, hN, lt_of_lt_of_le ?_ (guessing_vs_mean_lower n hnpos)⟩
  have hC : 4*C+1 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  linarith

end BanditRL.OnlineGradientDescent
