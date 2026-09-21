import BanditRLProof.HeavyTailSourceGap

/-! Strict good-event index comparison and actual selected-large-count events. -/
namespace BanditRLProof.HeavyTail.SourcePolicy
open MeasureTheory ProbabilityTheory
variable {K : ℕ}

theorem selected_gap_lt (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (mean : Fin K → ℝ) (best : Fin K)
    (n : ℕ) (hn : K ≤ n+1)
    (hbest : mean best - robustMean hK ε u stream best (n+1) <
      sourceConfidenceRadius ε u (n+1) (pullCount (robustAction hK ε u stream) best (n+1)))
    (hchosen : robustMean hK ε u stream (robustAction hK ε u stream (n+1)) (n+1) -
      mean (robustAction hK ε u stream (n+1)) < sourceConfidenceRadius ε u (n+1)
        (pullCount (robustAction hK ε u stream) (robustAction hK ε u stream (n+1)) (n+1))) :
    mean best - mean (robustAction hK ε u stream (n+1)) <
      2*sourceConfidenceRadius ε u (n+1)
        (pullCount (robustAction hK ε u stream) (robustAction hK ε u stream (n+1)) (n+1)) := by
  have hs := robustAction_maximizes hK ε u stream n hn best
  dsimp only at hs
  simp_rw [robustIndex_history] at hs
  linarith

theorem robust_selected_small_radius_tail (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (t : ℕ) (ht : K ≤ t)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | robustAction hK ε u stream t = arm ∧
      2*sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        (∫ x, x ∂ν best) - ∫ x, x ∂ν arm} ≤
      2*t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  let badBest := {stream | sourceConfidenceRadius ε u t
    (pullCount (robustAction hK ε u stream) best t) ≤
      (∫ x, x ∂ν best) - robustMean hK ε u stream best t}
  let badArm := {stream | sourceConfidenceRadius ε u t
    (pullCount (robustAction hK ε u stream) arm t) ≤
      robustMean hK ε u stream arm t - ∫ x, x ∂ν arm}
  have hs : {stream | robustAction hK ε u stream t = arm ∧
      2*sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        (∫ x, x ∂ν best) - ∫ x, x ∂ν arm} ⊆ badBest ∪ badArm := by
    intro stream hstream
    rcases hstream with ⟨hselected, hgap⟩
    by_contra hbad
    have hgood := not_or.mp hbad
    simp only [badBest, badArm, Set.mem_setOf_eq] at hgood
    have hb := lt_of_not_ge hgood.1
    have ha := lt_of_not_ge hgood.2
    cases t with
    | zero => omega
    | succ n =>
      have hc := selected_gap_lt hK ε u stream (fun a => ∫ x, x ∂ν a) best n ht hb
        (by simpa only [hselected] using ha)
      rw [hselected] at hc
      exact (not_lt_of_ge hgap) hc
  have hb := robustMean_lower_tail hK ν best ε u t ht hε0 hε hu0 (hX best) (hm best) (hu best)
  have ha := robustMean_upper_tail hK ν arm ε u t ht hε0 hε hu0 (hX arm) (hm arm) (hu arm)
  calc
    _ ≤ (UCB.armStreamMeasure ν).real (badBest ∪ badArm) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ (UCB.armStreamMeasure ν).real badBest + (UCB.armStreamMeasure ν).real badArm :=
      measureReal_union_le _ _
    _ ≤ 2*t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
      dsimp [badBest, badArm]
      linarith

theorem robust_initial_count_zero (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (t : ℕ) (ht : t < K) :
    pullCount (robustAction hK ε u stream) (robustAction hK ε u stream t) t = 0 := by
  apply pullCount_eq_zero_of_forall_ne
  intro s hs heq
  rw [robustAction_initialization hK ε u stream s (hs.trans ht),
    robustAction_initialization hK ε u stream t ht] at heq
  have hv := congrArg Fin.val heq
  simp only [UCB.initializationArm, Nat.mod_eq_of_lt (hs.trans ht), Nat.mod_eq_of_lt ht] at hv
  omega

theorem robust_large_count_tail (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (T t : ℕ) (hT : 2 ≤ T) (ht : t < T)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | robustAction hK ε u stream t = arm ∧
      gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T ≤
        pullCount (robustAction hK ε u stream) arm t} ≤ 2*t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  by_cases hinit : t < K
  · have he : {stream | robustAction hK ε u stream t = arm ∧
        gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T ≤
          pullCount (robustAction hK ε u stream) arm t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro stream hs
      rcases hs with ⟨hsel, hcount⟩
      have hz := robust_initial_count_zero hK ε u stream t hinit
      rw [hsel] at hz
      have hp := gapThreshold_pos ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T hT hu0 hgap
      omega
    rw [he, measureReal_empty]
    positivity
  · refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
      (robust_selected_small_radius_tail hK ν best arm ε u t (Nat.le_of_not_gt hinit)
        hε0.le hε hu0 hX hm hu)
    intro stream hs
    exact ⟨hs.1, twice_radius_le_gap ε u _ hε0 hu0 hgap t T _ hT ht hs.2⟩

end BanditRLProof.HeavyTail.SourcePolicy
