import BanditRLProof.Algorithms.HOODepthOptimization

/-! Repaired source Theorem 6: actual HOO expected pseudo-regret at all
positive horizons, with a horizon-independent constant. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-- Every real exponent strictly above the actual near-optimality dimension
admits the source rate for the constructed causal HOO process. The logarithm
repair is log(max(N,2)); the confidence and algorithm use the same repair. -/
theorem RegularCovering.expected_pseudoRegret_rate {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀x, (∫ y, y ∂law x)=f x)
    (hf : ∀x, f x≤best) (hfrange : ∀x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
      (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
        ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      γ*(N:ℝ)^((d+1)/(d+2))*(Real.log (max (N:ℝ) 2))^(1/(d+2)) := by
  have hdpos : 0<d := EReal.coe_lt_coe_iff.mp
    ((C.nearOptimalityDimension_nonneg f best (4*C.nu1/C.nu2)).trans_lt hd)
  obtain ⟨K, hK, hsums⟩ := C.expected_regret_dimension_sums law f best d hmean hf hfrange
    hbest hw hbound hd
  let q := C.rho^(-(1+d))
  let B := regretSumConstant C.nu1 C.nu2 C.rho d K/(q-1)
  have hq : 1<q := Real.one_lt_rpow_of_pos_of_lt_one_of_neg C.rho_pos C.rho_lt_one (by linarith)
  have hB : 0<B := div_pos (regretSumConstant_pos C.nu1_pos C.nu2_pos C.rho_pos hK) (by linarith)
  have hA : 0<4*C.nu1 := mul_pos (by norm_num) C.nu1_pos
  refine ⟨4*C.nu1+B*q, by positivity, fun N hN => ?_⟩
  obtain ⟨hLpos, hLN⟩ := log_horizon_pos_le N hN
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  obtain ⟨H, _, hopt⟩ := exists_regret_depth C.rho_pos C.rho_lt_one hdpos
    hA.le hB.le hn hLpos hLN
  have hlog : Real.log 2 ≤ Real.log (max (N:ℝ) 2) :=
    Real.log_le_log (by norm_num) (le_max_right _ _)
  have hred := regret_sums_le C.nu1_pos C.nu2_pos C.rho_pos C.rho_lt_one hdpos hK hlog H
  have hh := hsums H N
  have hcombined :
      (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
        ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      (4*C.nu1)*(N:ℝ)*C.rho^H+B*Real.log (max (N:ℝ) 2)*(C.rho^H)^(-(1+d)) := by
    dsimp only [B, q]
    linarith
  exact hcombined.trans hopt

end BanditRLProof.HOO
