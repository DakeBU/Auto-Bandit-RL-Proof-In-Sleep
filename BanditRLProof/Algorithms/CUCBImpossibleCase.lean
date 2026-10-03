import BanditRLProof.Algorithms.CUCBSourceModel

/-! The source impossible-case argument with actual CUCB indices, true score
gaps, finite possible-trigger sets and the source sampling constant six. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem confidenceRadius_lt_half {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m)
    (u : ℝ) (hu : 0<u)
    (hc : 6*Real.log ((n:ℝ)+1)/u^2 < (observationCount Y n i : ℝ)) :
    confidenceRadius Y n i (3*Real.log ((n:ℝ)+1)) < u/2 := by
  have hl : 0≤Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have ht : (0:ℝ)<observationCount Y n i := lt_of_le_of_lt (by positivity) hc
  have hn : observationCount Y n i≠0 := by exact_mod_cast ne_of_gt ht
  rw [confidenceRadius, if_neg hn]
  apply lt_of_le_of_lt (min_le_left _ _)
  have hs := Real.sq_sqrt (show 0≤3*Real.log ((n:ℝ)+1)/(2*observationCount Y n i) by positivity)
  have hx := (div_lt_iff₀ (sq_pos_of_pos hu)).1 hc
  have hd : 3*Real.log ((n:ℝ)+1)/(2*observationCount Y n i)<(u/2)^2 := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*observationCount Y n i)).2
    nlinarith
  nlinarith [Real.sqrt_nonneg (3*Real.log ((n:ℝ)+1)/(2*observationCount Y n i))]

namespace SourceModel
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

theorem not_bad_of_nice_and_sufficient_observations (Y : ℕ → Feedback m) (n : ℕ) (a : A)
    (hnice : ∀i, |empiricalMean Y n i-(M.trueInput i:ℝ)|≤
      confidenceRadius Y n i (3*Real.log ((n:ℝ)+1)))
    (horacle : S.alpha*scoreOptimum S.score (oracleInput Y n)≤S.score (oracleInput Y n) a)
    (hcount : ∀i∈M.possible a,
      6*Real.log ((n:ℝ)+1)/(S.inverseGap a)^2 < (observationCount Y n i : ℝ)) :
    ¬0<S.gap a := by
  intro hbad
  have hu := S.inverseGap_spec a hbad
  let v := oracleInput Y n
  have hindex (i : Fin m) := upperIndex_of_confidence Y n i (M.trueInput i:ℝ)
    (M.trueInput i).property (hnice i)
  have hopt : scoreOptimum S.score M.trueInput≤scoreOptimum S.score v :=
    S.optimum_monotone M.trueInput v (fun i => (hindex i).1)
  let L : ℝ := (M.possible a).sup' (M.possible_nonempty a)
    (fun i => |(v i:ℝ)-(M.trueInput i:ℝ)|)
  have hL0 : 0≤L := by
    obtain ⟨i, hi⟩ := M.possible_nonempty a
    exact (abs_nonneg ((v i:ℝ)-(M.trueInput i:ℝ))).trans
      (Finset.le_sup' (fun j => |(v j:ℝ)-(M.trueInput j:ℝ)|) hi)
  have hLi (i : Fin m) (hi : i∈M.possible a) : |(v i:ℝ)-(M.trueInput i:ℝ)|≤L :=
    Finset.le_sup' (fun j => |(v j:ℝ)-(M.trueInput j:ℝ)|) hi
  have hLu : L<S.inverseGap a := by
    apply (Finset.sup'_lt_iff (M.possible_nonempty a)).2
    intro i hi
    have hr := confidenceRadius_lt_half Y n i (S.inverseGap a) hu.1 (hcount i hi)
    have h0 : 0≤(v i:ℝ)-(M.trueInput i:ℝ) := sub_nonneg.mpr (hindex i).1
    rw [abs_of_nonneg h0]
    have h1 := (hindex i).2
    change upperIndex Y n i-(M.trueInput i:ℝ)<S.inverseGap a
    linarith
  have hs := S.score_smooth v M.trueInput a L hL0 hLi
  have hf : S.modulus L<S.gap a := by
    rw [← hu.2]
    exact S.modulus_strictMono hL0 hu.1.le hLu
  have hscore : S.score v a<S.score M.trueInput a+S.gap a := by
    have hh := le_abs_self (S.score v a-S.score M.trueInput a)
    linarith
  have ha := mul_le_mul_of_nonneg_left hopt S.alpha_mem.1.le
  change S.alpha*scoreOptimum S.score v≤S.score v a at horacle
  unfold gap sourceGap at hscore
  linarith

end SourceModel
end BanditRLProof.CUCB
