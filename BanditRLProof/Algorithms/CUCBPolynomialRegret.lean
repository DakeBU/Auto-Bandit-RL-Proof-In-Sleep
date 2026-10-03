import BanditRLProof.Algorithms.CUCBPolynomialIntegral
import BanditRLProof.PowerCutoffNormalization

/-! Exact source polynomial-smoothness endpoints, including small horizons. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

include M in
omit [Fintype A] [MeasurableSingletonClass A] [StandardBorelSpace A] in
theorem base_arm_count_pos : 0<m := by
  obtain ⟨i,_⟩ := M.arms_nonempty
  have h := i.isLt
  omega

omit [StandardBorelSpace A] in
theorem approximationRegret_le_linear_gap (H : ℕ) :
    S.approximationRegret H≤(H:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hg : ∀Y : ℕ → Round A m, (∑n∈Finset.range H, S.gap (Y n).1)≤
      (H:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
    intro Y
    have h := Finset.sum_le_sum (s:=Finset.range H) (fun n _ =>
      gap_le_maxPositiveGap S.score M.trueInput S.alpha (Y n).1)
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h
  have hi := integral_mono (integrable_finset_sum _ (fun n _ => S.integrable_actual_gap n))
    (integrable_const _) hg
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  obtain ⟨a⟩ := ‹Nonempty A›
  have ho : 0≤scoreOptimum S.score M.trueInput := (S.score_nonneg _ a).trans (score_le_optimum _ _ a)
  have hc : 0≤(H:ℝ)*S.alpha*(1-S.beta)*scoreOptimum S.score M.trueInput :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg H) S.alpha_mem.1.le)
      (sub_nonneg.mpr S.beta_mem.2)) ho
  rw [S.approximationRegret_eq_gap_sum]
  linarith

omit [StandardBorelSpace A] in
theorem approximationRegret_one_le (c : ℝ) (hc : 1≤c) :
    S.approximationRegret 1≤c*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have h := S.approximationRegret_le_linear_gap 1
  simp only [Nat.cast_one,one_mul] at h
  have hm : (1:ℝ)≤m := by exact_mod_cast (Nat.succ_le_of_lt (base_arm_count_pos (M:=M)))
  have hcm : (1:ℝ)≤c*(m:ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hm)]
  exact h.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hcm) S.maxPositiveGap_nonneg])

theorem theorem_two_deterministic (H : ℕ) (hH : 1≤H) (hp : M.globalMinTrigger=1)
    (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) :
    S.approximationRegret H≤(2*γ/(2-ω))*(6*(m:ℝ)*Real.log (H:ℝ))^(ω/2)*(H:ℝ)^(1-ω/2)+
      (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  by_cases hone : H=1
  · subst H
    simpa [Real.zero_rpow (show ω/2≠0 by positivity)] using
      S.approximationRegret_one_le (1+Real.pi^2/3) (by nlinarith [sq_nonneg Real.pi])
  have hHgt : 1<H := by omega
  have hN : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have hm : 0<(m:ℝ) := by exact_mod_cast (base_arm_count_pos (M:=M))
  have hlog : 0<Real.log (H:ℝ) := Real.log_pos (by exact_mod_cast hHgt)
  let q := 2/ω
  let C := 6*(m:ℝ)*Real.log (H:ℝ)
  let K := C*γ^q
  let a := (K/(H:ℝ))^(1/q)
  have hq : 1<q := (lt_div_iff₀ hω).mpr (by linarith)
  have hC : 0<C := by dsimp [C]; positivity
  have hK : 0<K := mul_pos hC (Real.rpow_pos_of_pos hγ _)
  have ha : 0<a := Real.rpow_pos_of_pos (div_pos hK hN) _
  have hopt : S.approximationRegret H≤q/(q-1)*((H:ℝ)*a)+
      (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
    by_cases hlarge : maxPositiveGap S.score M.trueInput S.alpha≤a
    · have hr := S.approximationRegret_le_large_cutoff H a hlarge
      simp only [hp,lt_self_iff_false,ite_false,add_zero] at hr
      have hc : 1≤q/(q-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
      have hh := mul_le_mul_of_nonneg_right hc (mul_pos hN ha).le
      have hd := mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) S.maxPositiveGap_nonneg
      nlinarith
    · have hr := S.polynomial_cutoff_regret_deterministic H hH hp γ ω hγ hω hω1 hf a
        ⟨ha,le_of_not_ge hlarge⟩
      have hr' : S.approximationRegret H≤(H:ℝ)*a+K*a^(1-q)/(q-1)+
          (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
        dsimp [K,C,q]
        convert hr using 1
        ring
      rw [show (H:ℝ)*a+K*a^(1-q)/(q-1)=q/(q-1)*((H:ℝ)*a) from
        PowerTailIntegral.cutoff_objective K (H:ℝ) q hK hN hq] at hr'
      exact hr'
  have he := PowerTailIntegral.source_cutoff_normalization C (H:ℝ) γ ω hC hN hγ hω hω1
  change q/(q-1)*((H:ℝ)*a)=_ at he
  rw [he] at hopt
  exact hopt





theorem theorem_two_probabilistic (H : ℕ) (hH : 1≤H) (hp : M.globalMinTrigger<1)
    (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) :
    S.approximationRegret H≤(2*γ/(2-ω))*(12*(m:ℝ)*Real.log (H:ℝ)/M.globalMinTrigger)^(ω/2)*
      (H:ℝ)^(1-ω/2)+(1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
      ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
  by_cases hone : H=1
  · subst H
    simpa [Real.zero_rpow (show ω/2≠0 by positivity)] using
      S.approximationRegret_one_le (1+Real.pi^2/2) (by nlinarith [sq_nonneg Real.pi])
  have hHgt : 1<H := by omega
  have hN : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have hm : 0<(m:ℝ) := by exact_mod_cast (base_arm_count_pos (M:=M))
  have hlog : 0<Real.log (H:ℝ) := Real.log_pos (by exact_mod_cast hHgt)
  have hpstar := M.globalMinTrigger_pos
  let q := 2/ω
  let C := 12*(m:ℝ)*Real.log (H:ℝ)/M.globalMinTrigger
  let K := C*γ^q
  let a := (K/(H:ℝ))^(1/q)
  have hq : 1<q := (lt_div_iff₀ hω).mpr (by linarith)
  have hC : 0<C := by dsimp [C]; positivity
  have hK : 0<K := mul_pos hC (Real.rpow_pos_of_pos hγ _)
  have ha : 0<a := Real.rpow_pos_of_pos (div_pos hK hN) _
  have hE : 0≤∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*
      maxPositiveGap S.score M.trueInput S.alpha := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (div_nonneg (by positivity) (M.minTrigger_pos i).le) S.maxPositiveGap_nonneg
  have hopt : S.approximationRegret H≤q/(q-1)*((H:ℝ)*a)+
      (1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
      ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
    by_cases hlarge : maxPositiveGap S.score M.trueInput S.alpha≤a
    · have hr := S.approximationRegret_le_large_cutoff H a hlarge
      simp only [hp,ite_true] at hr
      have hc : 1≤q/(q-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
      have hh := mul_le_mul_of_nonneg_right hc (mul_pos hN ha).le
      have hd := mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) S.maxPositiveGap_nonneg
      nlinarith
    · have hr := S.polynomial_cutoff_regret_probabilistic H hH hp γ ω hγ hω hω1 hf a
        ⟨ha,le_of_not_ge hlarge⟩
      have hr' : S.approximationRegret H≤(H:ℝ)*a+K*a^(1-q)/(q-1)+
          (1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
          ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
        dsimp [K,C,q]
        convert hr using 1
        ring
      rw [show (H:ℝ)*a+K*a^(1-q)/(q-1)=q/(q-1)*((H:ℝ)*a) from
        PowerTailIntegral.cutoff_objective K (H:ℝ) q hK hN hq] at hr'
      exact hr'
  have he := PowerTailIntegral.source_cutoff_normalization C (H:ℝ) γ ω hC hN hγ hω hω1
  change q/(q-1)*((H:ℝ)*a)=_ at he
  rw [he] at hopt
  exact hopt

end BanditRLProof.CUCB.SourceModel
