import BanditRLProof.Algorithms.HOOActualRegret

/-! Arbitrary reward-family interface for the source-repaired HOO rate.
Only the countable representative-node law must be measurable. The internal
discrete-domain transport preserves the actual action and trajectory. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def Covering.familyNodeLaw {X : Type*} (C : Covering X)
    (law : X → Measure ℝ) : Kernel Node ℝ where
  toFun v := law (C.representative v)
  measurable' := measurable_of_countable _

instance Covering.familyNodeLaw_markov {X : Type*} (C : Covering X)
    (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)] :
    IsMarkovKernel (C.familyNodeLaw law) where
  isProbabilityMeasure v := inferInstanceAs (IsProbabilityMeasure (law (C.representative v)))

theorem Covering.familyNodeLaw_apply {X : Type*} (C : Covering X)
    (law : X → Measure ℝ) (v : Node) :
    C.familyNodeLaw law v = law (C.representative v) := rfl

theorem Covering.familyNodeLaw_eq_nodeLaw {X : Type*} [MeasurableSpace X]
    (C : Covering X) (law : Kernel X ℝ) :
    C.familyNodeLaw (fun x => law x) = C.nodeLaw law := rfl

noncomputable def RegularCovering.discrete {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) : @RegularCovering X ⊤ :=
  @RegularCovering.mk X ⊤ C.toCovering (fun _ => trivial)
    C.ell C.ell_nonneg C.ell_self C.nu1 C.nu2 C.rho C.nu1_pos C.nu2_pos
    C.rho_pos C.rho_lt_one C.diameter_bound C.center C.center_mem
    C.ball_subset C.balls_disjoint

noncomputable def familyDiscreteKernel {X : Type*} (law : X → Measure ℝ) :
    @Kernel X ℝ ⊤ (inferInstance : MeasurableSpace ℝ) := by
  letI : MeasurableSpace X := ⊤
  exact { toFun := law, measurable' := measurable_from_top }

instance familyDiscreteKernel_markov {X : Type*} (law : X → Measure ℝ)
    [∀ x, IsProbabilityMeasure (law x)] : IsMarkovKernel (familyDiscreteKernel law) where
  isProbabilityMeasure x := inferInstanceAs (IsProbabilityMeasure (law x))

theorem RegularCovering.expected_pseudoRegret_rate_family {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hf : ∀ x, f x≤best) (hfrange : ∀ x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
      (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
        ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) ≤
      γ*(N:ℝ)^((d+1)/(d+2))*(Real.log (max (N:ℝ) 2))^(1/(d+2)) := by
  exact @RegularCovering.expected_pseudoRegret_rate X ⊤ C.discrete (familyDiscreteKernel law) inferInstance f best d
    hmean hf hfrange hbest hw hbound hd

theorem RegularCovering.expected_actual_eq_pseudoRegret_family {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hfrange : ∀ x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    (∫ Y, (∑ n ∈ Finset.range N, (best-Y n))
      ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) =
    (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
      ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) := by
  exact @RegularCovering.expected_actual_eq_pseudoRegret X ⊤ C.discrete (familyDiscreteKernel law) inferInstance f best
    hmean hfrange hbound N

theorem RegularCovering.expected_actualRegret_rate_family {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hf : ∀ x, f x≤best) (hfrange : ∀ x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
      (∫ Y, (∑ n ∈ Finset.range N, (best-Y n))
        ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) ≤
      γ*(N:ℝ)^((d+1)/(d+2))*(Real.log (max (N:ℝ) 2))^(1/(d+2)) := by
  exact @RegularCovering.expected_actualRegret_rate X ⊤ C.discrete (familyDiscreteKernel law) inferInstance f best d
    hmean hf hfrange hbest hw hbound hd

end BanditRLProof.HOO
