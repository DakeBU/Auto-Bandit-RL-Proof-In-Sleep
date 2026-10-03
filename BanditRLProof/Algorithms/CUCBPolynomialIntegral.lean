import BanditRLProof.Algorithms.CUCBPolynomialThreshold
import BanditRLProof.PowerTailIntegral

/-! Integration of the actual source thresholds under a polynomial modulus. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

theorem threshold_integral_le_power (H : ℕ) (hH : 1≤H) (i : Fin m)
    (a : ℝ) (ha : a∈S.gapDomain) (q B c : ℝ) (hq : 1<q) (hB : 0≤B) (hc : 0≤c)
    (he : ∀x∈Set.Icc a (maxPositiveGap S.score M.trueInput S.alpha),
      S.gapThreshold H (M.minTrigger i) x≤B*x^(-q)+c) :
    (∫x in a..maxPositiveGap S.score M.trueInput S.alpha, S.gapThreshold H (M.minTrigger i) x)≤
      B*a^(1-q)/(q-1)+c*maxPositiveGap S.score M.trueInput S.alpha := by
  let D := maxPositiveGap S.score M.trueInput S.alpha
  have hD : D∈S.gapDomain := ⟨ha.1.trans_le ha.2,le_rfl⟩
  have hz : (0:ℝ)∉Set.uIcc a D := by
    rw [Set.uIcc_of_le ha.2]
    intro h
    linarith [h.1,ha.1]
  have hp : IntervalIntegrable (fun x : ℝ => x^(-q)) volume a D := intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hcI : IntervalIntegrable (fun _ : ℝ => c) volume a D := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on ha.2
    (S.gapThreshold_intervalIntegrable H hH _ (M.minTrigger_pos i) ha hD)
    ((hp.const_mul B).add hcI) he
  rw [intervalIntegral.integral_add (hp.const_mul B) hcI,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  have ht := mul_le_mul_of_nonneg_left (PowerTailIntegral.integral_power_tail_le a D q ha.1 ha.2 hq) hB
  rw [← mul_div_assoc] at ht
  have hc' := mul_nonneg hc ha.1.le
  change _≤B*a^(1-q)/(q-1)+c*D
  nlinarith [h.trans (add_le_add ht le_rfl)]

theorem polynomial_threshold_integral_deterministic (H : ℕ) (hH : 1≤H) (i : Fin m)
    (hp : M.minTrigger i=1) (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) (a : ℝ) (ha : a∈S.gapDomain) :
    (∫x in a..maxPositiveGap S.score M.trueInput S.alpha, S.gapThreshold H (M.minTrigger i) x)≤
      (6*Real.log (H:ℝ)*γ^(2/ω))*a^(1-2/ω)/(2/ω-1) := by
  have hq : 1<2/ω := (lt_div_iff₀ hω).mpr (by linarith)
  have hlog : 0≤Real.log (H:ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have h := S.threshold_integral_le_power H hH i a ha (2/ω)
    (6*Real.log (H:ℝ)*γ^(2/ω)) 0 hq (by positivity) le_rfl (fun x hx => by
      rw [hp,S.gapThreshold_polynomial_deterministic H γ ω hγ hω hf
        ⟨ha.1.trans_le hx.1,hx.2⟩,add_zero])
  simpa using h

theorem polynomial_threshold_integral_probabilistic (H : ℕ) (hH : 1≤H) (i : Fin m)
    (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) (a : ℝ) (ha : a∈S.gapDomain) :
    (∫x in a..maxPositiveGap S.score M.trueInput S.alpha, S.gapThreshold H (M.minTrigger i) x)≤
      (12*Real.log (H:ℝ)/M.globalMinTrigger*γ^(2/ω))*a^(1-2/ω)/(2/ω-1)+
      (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hq : 1<2/ω := (lt_div_iff₀ hω).mpr (by linarith)
  have hlog : 0≤Real.log (H:ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hp := M.minTrigger_pos i
  have hpstar := M.globalMinTrigger_pos
  exact S.threshold_integral_le_power H hH i a ha (2/ω)
    (12*Real.log (H:ℝ)/M.globalMinTrigger*γ^(2/ω)) (24*Real.log (H:ℝ)/M.minTrigger i)
    hq (by positivity) (by positivity) (fun x hx =>
      S.gapThreshold_polynomial_upper H hH i γ ω hγ hω hf ⟨ha.1.trans_le hx.1,hx.2⟩)




variable [MeasurableSingletonClass A] [StandardBorelSpace A]

theorem polynomial_cutoff_regret_deterministic (H : ℕ) (hH : 1≤H)
    (hp : M.globalMinTrigger=1) (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) (a : ℝ) (ha : a∈S.gapDomain) :
    S.approximationRegret H≤(H:ℝ)*a+
      ((m:ℝ)*(6*Real.log (H:ℝ)*γ^(2/ω)))*a^(1-2/ω)/(2/ω-1)+
      (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hi := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    S.polynomial_threshold_integral_deterministic H hH i
      (M.globalMinTrigger_eq_one_iff.mp hp i) γ ω hγ hω hω1 hf a ha)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  have h := (S.approximationRegret_le_gap_cutoff H hH a ha).trans
    (add_le_add (add_le_add le_rfl hi) le_rfl)
  simp only [hp,lt_self_iff_false,ite_false,add_zero] at h
  convert h using 1
  ring

theorem polynomial_cutoff_regret_probabilistic (H : ℕ) (hH : 1≤H)
    (hp : M.globalMinTrigger<1) (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) (a : ℝ) (ha : a∈S.gapDomain) :
    S.approximationRegret H≤(H:ℝ)*a+
      ((m:ℝ)*(12*Real.log (H:ℝ)/M.globalMinTrigger*γ^(2/ω)))*a^(1-2/ω)/(2/ω-1)+
      (1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
      ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hi := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    S.polynomial_threshold_integral_probabilistic H hH i γ ω hγ hω hω1 hf a ha)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  have h := (S.approximationRegret_le_gap_cutoff H hH a ha).trans
    (add_le_add (add_le_add le_rfl hi) le_rfl)
  simp only [hp,ite_true] at h
  convert h using 1
  ring

end BanditRLProof.CUCB.SourceModel
