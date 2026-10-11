import BanditRLProof.OnlineSubgradientMax
import BanditRLProof.OnlineNormalCone

namespace MaximumProbe
open BanditRL.OnlineConvex Set
noncomputable def family (i : Bool) (y : ℝ) : EReal := if i then (y : EReal) else ((-y : ℝ) : EReal)

theorem family_proper (i : Bool) : SourceProper (family i) := by
  constructor
  · intro y
    cases i <;> simp [family]
  · exact ⟨0, 0, by cases i <;> simp [family]⟩

theorem family_domain (i : Bool) (x : ℝ) : x ∈ effectiveDomain (family i) := by
  cases i
  · change ((-x : ℝ) : EReal) < ⊤
    exact EReal.coe_lt_top (-x)
  · change (x : EReal) < ⊤
    exact EReal.coe_lt_top x

theorem family_convex (i : Bool) : IsConvexExtended (family i) := by
  rw [convexExtended_iff_toReal (family i) (family_proper i).1]
  have hd : effectiveDomain (family i) = univ := eq_univ_of_forall (family_domain i)
  rw [hd]
  cases i
  · change ConvexOn ℝ univ (fun y : ℝ => (((-y : ℝ) : EReal)).toReal)
    simpa only [EReal.toReal_coe, Pi.neg_apply, id_eq] using
      (concaveOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))).neg
  · change ConvexOn ℝ univ (fun y : ℝ => (y : EReal).toReal)
    simpa only [EReal.toReal_coe, id_eq] using
      (convexOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ)))

theorem family_continuous (i : Bool) (x : ℝ) : ContinuousAt (family i) x := by
  cases i
  · change ContinuousAt (fun y : ℝ => ((-y : ℝ) : EReal)) x
    exact (continuous_coe_real_ereal.comp continuous_neg).continuousAt
  · change ContinuousAt ((↑) : ℝ → EReal) x
    exact continuous_coe_real_ereal.continuousAt

theorem affine_support (a x : ℝ) :
    SourceSubdifferential (fun y : ℝ => ((a * y : ℝ) : EReal)) x = {a} := by
  ext g
  change (∀ y, ((a * x : ℝ) : EReal) + (inner ℝ g (y - x) : EReal) ≤ ((a * y : ℝ) : EReal)) ↔ g = a
  constructor
  · intro hg
    have h1 := hg (x + 1)
    have h2 := hg (x - 1)
    rw [← EReal.coe_add] at h1 h2
    have h1r := EReal.coe_le_coe_iff.mp h1
    have h2r := EReal.coe_le_coe_iff.mp h2
    change a*x + (x+1-x)*g ≤ a*(x+1) at h1r
    change a*x + (x-1-x)*g ≤ a*(x-1) at h2r
    nlinarith
  · intro hg
    subst g
    intro y
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    change a*x + (y-x)*a ≤ a*y
    nlinarith

theorem maximum_zero : SourceFiniteMax family 0 = 0 := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun i => family i 0)).mpr
    intro i _
    cases i <;> simp [family]
  · have h := Finset.le_sup' (fun i => family i 0) (Finset.mem_univ true)
    change family true 0 ≤ SourceFiniteMax family 0 at h
    simpa only [family, if_true] using h

theorem tie_active_union : SourceActiveSubgradientUnion family 0 = {(-1 : ℝ), 1} := by
  have hs (i : Bool) : SourceSubdifferential (family i) 0 = {if i then (1 : ℝ) else -1} := by
    cases i
    · simpa [family] using affine_support (-1) 0
    · simpa [family] using affine_support 1 0
  ext g
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq, maximum_zero]
  constructor
  · rintro ⟨i, hi, hg⟩
    cases i <;> simp_all [hs, family]
  · intro hg
    rcases hg with h | h
    · exact ⟨false, by simp [family], by simpa [hs] using h⟩
    · exact ⟨true, by simp [family], by simpa [hs] using h⟩

theorem full_tie_hull_canary :
    SourceSubdifferential (SourceFiniteMax family) 0 = convexHull ℝ {(-1 : ℝ), 1} := by
  simpa only [tie_active_union] using theorem_2_26 family family_proper family_convex 0
    (fun i => family_domain i 0) (fun i => family_continuous i 0)



theorem full_tie_interval_canary :
    SourceSubdifferential (SourceFiniteMax family) 0 = Icc (-1 : ℝ) 1 := by
  rw [full_tie_hull_canary, convexHull_pair, segment_eq_Icc (by norm_num)]

theorem mixture_and_rejection_canary :
    (1 / 2 : ℝ) ∈ SourceSubdifferential (SourceFiniteMax family) 0 ∧
    (1 / 2 : ℝ) ∉ SourceActiveSubgradientUnion family 0 ∧
    (2 : ℝ) ∉ SourceSubdifferential (SourceFiniteMax family) 0 := by
  norm_num [full_tie_interval_canary, tie_active_union]

theorem maximum_two : SourceFiniteMax family 2 = ((2 : ℝ) : EReal) := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun i => family i 2)).mpr
    intro i _
    cases i
    · change ((-2 : ℝ) : EReal) ≤ ((2 : ℝ) : EReal)
      exact EReal.coe_le_coe_iff.mpr (by norm_num)
    · exact le_rfl
  · have h := Finset.le_sup' (fun i => family i 2) (Finset.mem_univ true)
    change family true 2 ≤ SourceFiniteMax family 2 at h
    simpa only [family, if_true] using h

theorem inactive_union_canary : SourceActiveSubgradientUnion family 2 = {(1 : ℝ)} := by
  have hs (i : Bool) : SourceSubdifferential (family i) 2 = {if i then (1 : ℝ) else -1} := by
    cases i
    · simpa [family] using affine_support (-1) 2
    · simpa [family] using affine_support 1 2
  ext g
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hg⟩
    cases i
    · change ((-2 : ℝ) : EReal) = SourceFiniteMax family 2 at hi
      rw [maximum_two] at hi
      have hr := EReal.coe_injective hi
      norm_num at hr
    · simpa only [hs, if_true] using hg
  · intro hg
    refine ⟨true, ?_, ?_⟩
    · change ((2 : ℝ) : EReal) = SourceFiniteMax family 2
      exact maximum_two.symm
    · simpa only [hs, if_true] using hg

theorem strict_active_canary :
    SourceSubdifferential (SourceFiniteMax family) 2 = {(1 : ℝ)} ∧
    (-1 : ℝ) ∉ SourceSubdifferential (SourceFiniteMax family) 2 := by
  have he := theorem_2_26 family family_proper family_convex 2
    (fun i => family_domain i 2) (fun i => family_continuous i 2)
  rw [inactive_union_canary, convexHull_singleton] at he
  exact ⟨he, by rw [he]; norm_num⟩

#print axioms full_tie_hull_canary
#print axioms full_tie_interval_canary
#print axioms mixture_and_rejection_canary
#print axioms strict_active_canary
end MaximumProbe

namespace MaximumExtendedProbe
open BanditRL.OnlineConvex Set Filter Topology
noncomputable def constrained (_ : Unit) : ℝ → EReal := extendedIndicator (Icc (-1 : ℝ) 1)

theorem constrained_proper (i : Unit) : SourceProper (constrained i) :=
  sourceProper_indicator_iff _ |>.mpr ⟨0, by norm_num⟩

theorem constrained_convex (i : Unit) : IsConvexExtended (constrained i) :=
  convex_indicator_iff _ |>.mpr (convex_Icc (-1 : ℝ) 1)

theorem constrained_domain (i : Unit) : (0 : ℝ) ∈ effectiveDomain (constrained i) := by
  rw [constrained, effectiveDomain_indicator]
  norm_num

theorem constrained_continuous (i : Unit) : ContinuousAt (constrained i) (0 : ℝ) := by
  have he : constrained i =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : EReal)) := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with y hy
    simp only [constrained, extendedIndicator, if_pos (show y ∈ Icc (-1 : ℝ) 1 from ⟨hy.1.le, hy.2.le⟩)]
  exact continuousAt_const.congr_of_eventuallyEq he

theorem singleton_max (y : ℝ) : SourceFiniteMax constrained y = constrained () y := by
  obtain ⟨i, hi⟩ := finiteMax_attained constrained y
  cases i
  exact hi

theorem singleton_extended_domain_canary :
    SourceSubdifferential (SourceFiniteMax constrained) 0 = {(0 : ℝ)} ∧
    SourceFiniteMax constrained 2 = ⊤ := by
  have hs : SourceSubdifferential (constrained ()) 0 = {(0 : ℝ)} := by
    have hi : (0 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) := by
      rw [interior_Icc]
      norm_num
    rw [constrained, indicator_subdifferential_eq_normalCone _ ⟨0, by norm_num⟩ (convex_Icc _ _),
      normalCone_interior_eq_zero _ ⟨0, by norm_num⟩ (convex_Icc _ _) 0 hi]
  have hU : SourceActiveSubgradientUnion constrained 0 = {(0 : ℝ)} := by
    ext g
    simp only [SourceActiveSubgradientUnion, mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hg⟩
      cases i
      simpa only [hs] using hg
    · intro hg
      exact ⟨(), (singleton_max 0).symm, by simpa only [hs] using hg⟩
  have he := theorem_2_26 constrained constrained_proper constrained_convex 0
    constrained_domain constrained_continuous
  rw [hU, convexHull_singleton] at he
  refine ⟨he, ?_⟩
  rw [singleton_max]
  norm_num [constrained, extendedIndicator]

#print axioms singleton_extended_domain_canary
end MaximumExtendedProbe
