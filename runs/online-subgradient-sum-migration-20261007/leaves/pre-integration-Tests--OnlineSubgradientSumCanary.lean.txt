import BanditRLProof.OnlineSubgradientSum
import Tests.OnlineSubgradientBasicCanary
import Tests.OnlineSubgradientDifferentiabilityCanary

noncomputable section

namespace SumEqualityProbe
open BanditRL.OnlineConvex Set

def square (y : ℝ) : EReal := ((y^2 : ℝ) : EReal)
def interval : ℝ → EReal := extendedIndicator (Icc (0 : ℝ) 2)
def family : Fin 3 → ℝ → EReal := ![square, square, interval]

theorem square_proper : SourceProper square :=
  ⟨fun y => EReal.coe_ne_bot _, 0, 0, by norm_num [square]⟩
theorem square_domain : effectiveDomain square = univ := by
  ext y
  simp only [effectiveDomain, mem_setOf_eq, mem_univ, iff_true]
  exact EReal.coe_lt_top _
theorem square_convex : IsConvexExtended square := by
  apply (convexExtended_iff_toReal square square_proper.1).mpr
  rw [square_domain]
  simpa only [square, EReal.toReal_coe] using SubgradientProbe.square_convex
theorem square_closed : SourceClosed square := by
  intro r
  have he : {y : ℝ | square y ≤ (r : EReal)} = {y : ℝ | y^2 ≤ r} := by
    ext y
    exact EReal.coe_le_coe_iff
  rw [he]
  exact isClosed_le (continuous_id.pow 2) continuous_const
theorem interval_proper : SourceProper interval :=
  (sourceProper_indicator_iff _).mpr ⟨0, by norm_num⟩
theorem interval_convex : IsConvexExtended interval :=
  (convex_indicator_iff _).mpr (convex_Icc 0 2)
theorem interval_closed : SourceClosed interval :=
  (sourceClosed_indicator_iff _).mpr isClosed_Icc

theorem family_proper : ∀ i, SourceProper (family i) := by
  intro i
  fin_cases i
  · exact square_proper
  · exact square_proper
  · exact interval_proper
theorem family_convex : ∀ i, IsConvexExtended (family i) := by
  intro i
  fin_cases i
  · exact square_convex
  · exact square_convex
  · exact interval_convex
theorem family_closed : ∀ i, SourceClosed (family i) := by
  intro i
  fin_cases i
  · exact square_closed
  · exact square_closed
  · exact interval_closed
theorem family_mixed_qualification :
    ∃ z : ℝ, z ∈ effectiveDomain (family (Fin.last 2)) ∧
      ∀ i : Fin 3, i ≠ Fin.last 2 → z ∈ interior (effectiveDomain (family i)) := by
  refine ⟨0, ?_, ?_⟩
  · change (0 : ℝ) ∈ effectiveDomain interval
    rw [interval, effectiveDomain_indicator]
    norm_num
  · intro i hi
    fin_cases i
    · change (0 : ℝ) ∈ interior (effectiveDomain square)
      rw [square_domain, interior_univ]
      exact mem_univ _
    · change (0 : ℝ) ∈ interior (effectiveDomain square)
      rw [square_domain, interior_univ]
      exact mem_univ _
    · exact (hi rfl).elim

theorem nonzero_aggregate_support :
    (-1 : ℝ) ∈ SourceSubdifferential (fun y => ∑ i, family i y) 0 := by
  intro y
  simp only [Fin.sum_univ_three]
  change square 0 + square 0 + interval 0 + (inner ℝ (-1 : ℝ) (y - 0) : EReal) ≤
    square y + square y + interval y
  have hz : interval 0 = 0 := by norm_num [interval, extendedIndicator]
  have hs : square 0 = 0 := by norm_num [square]
  rw [hs, hz]
  by_cases hy : y ∈ Icc (0 : ℝ) 2
  · have hhy : interval y = 0 := by simp only [interval, extendedIndicator, if_pos hy]
    rw [hhy]
    simp only [zero_add, add_zero, ← EReal.coe_add]
    apply EReal.coe_le_coe
    change (y - 0) * (-1) ≤ y^2 + y^2
    nlinarith [hy.1, sq_nonneg y]
  · have hhy : interval y = ⊤ := by simp only [interval, extendedIndicator, if_neg hy]
    rw [hhy, EReal.add_top_of_ne_bot (EReal.add_ne_bot_iff.mpr ⟨square_proper.1 y, square_proper.1 y⟩)]
    exact le_top

theorem actual_three_component_decomposition :
    ∃ G : Fin 3 → ℝ, (∀ i, G i ∈ SourceSubdifferential (family i) 0) ∧
      ∑ i, G i = (-1 : ℝ) := by
  have he := theorem_2_23_equality 2 family family_proper family_convex family_closed
    family_mixed_qualification 0
  have hg := nonzero_aggregate_support
  rw [he] at hg
  exact hg

theorem last_domain_boundary :
    (0 : ℝ) ∉ interior (effectiveDomain (family (Fin.last 2))) := by
  change (0 : ℝ) ∉ interior (effectiveDomain interval)
  rw [interval, effectiveDomain_indicator, interior_Icc]
  norm_num

theorem outside_domain_both_empty :
    SourceSubdifferential (fun y => ∑ i, family i y) 3 = ∅ ∧
      SourceSubgradientSum family 3 = ∅ := by
  have he := theorem_2_23_equality 2 family family_proper family_convex family_closed
    family_mixed_qualification 3
  have hempty : SourceSubgradientSum family 3 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro g ⟨G, hG, hs⟩
    have hi := subgradient_point_finite interval interval_proper 3 (G (Fin.last 2)) (hG (Fin.last 2))
    rw [interval, effectiveDomain_indicator] at hi
    norm_num at hi
  exact ⟨he.trans hempty, hempty⟩

theorem singleton_family_empty_interior :
    interior (effectiveDomain (extendedIndicator ({0} : Set ℝ))) = ∅ ∧
      (7 : ℝ) ∈ SourceSubgradientSum (fun _ : Fin 1 => extendedIndicator ({0} : Set ℝ)) 0 := by
  have hproper : SourceProper (extendedIndicator ({0} : Set ℝ)) :=
    (sourceProper_indicator_iff _).mpr ⟨0, mem_singleton 0⟩
  have hconvex : IsConvexExtended (extendedIndicator ({0} : Set ℝ)) :=
    (convex_indicator_iff _).mpr (convex_singleton 0)
  have hclosed : SourceClosed (extendedIndicator ({0} : Set ℝ)) :=
    (sourceClosed_indicator_iff _).mpr isClosed_singleton
  have hqual : ∃ z : ℝ, z ∈ effectiveDomain (extendedIndicator ({0} : Set ℝ)) ∧
      ∀ i : Fin 1, i ≠ Fin.last 0 → z ∈ interior (effectiveDomain (extendedIndicator ({0} : Set ℝ))) := by
    refine ⟨0, ?_, ?_⟩
    · rw [effectiveDomain_indicator]
      exact mem_singleton 0
    · intro i hi
      exact (hi (Subsingleton.elim _ _)).elim
  have he := theorem_2_23_equality 0 (fun _ : Fin 1 => extendedIndicator ({0} : Set ℝ))
    (fun _ => hproper) (fun _ => hconvex) (fun _ => hclosed) hqual 0
  constructor
  · rw [effectiveDomain_indicator]
    exact interior_singleton (0 : ℝ)
  · rw [← he]
    intro y
    simp only [Fin.sum_univ_one]
    by_cases hy : y = 0
    · subst y
      norm_num [extendedIndicator]
    · rw [show extendedIndicator ({0} : Set ℝ) y = ⊤ from by simp [extendedIndicator, hy]]
      exact le_top

#print axioms actual_three_component_decomposition
#print axioms nonzero_aggregate_support
#print axioms last_domain_boundary
#print axioms outside_domain_both_empty
#print axioms singleton_family_empty_interior
end SumEqualityProbe

namespace SumRuleProbe
open BanditRL.OnlineConvex Set
open scoped BigOperators

theorem quadratic_plus_constraint_support :
    (2 : ℝ) ∈ SourceSubdifferential
      (fun y : ℝ => ((y^2 : ℝ) : EReal) + extendedIndicator (Icc (0 : ℝ) 2) y) 1 := by
  let f : Fin 2 → ℝ → EReal := fun i => if i = 0 then
    (fun y => ((y^2 : ℝ) : EReal)) else extendedIndicator (Icc (0 : ℝ) 2)
  have hp : ∀ i, SourceProper (f i) := by
    intro i
    fin_cases i
    · change SourceProper (fun y : ℝ => ((y^2 : ℝ) : EReal))
      exact ⟨(fun y => EReal.coe_ne_bot _), 0, 0, by norm_num⟩
    · change SourceProper (extendedIndicator (Icc (0 : ℝ) 2))
      exact (sourceProper_indicator_iff _).mpr ⟨0, by norm_num⟩
  let G : Fin 2 → ℝ := fun i => if i = 0 then 2 else 0
  have hG : ∀ i, G i ∈ SourceSubdifferential (f i) 1 := by
    intro i
    fin_cases i
    · simpa only [f, G, if_pos rfl, mul_one] using SubgradientProbe.square_support 1
    · change (0 : ℝ) ∈ SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 2)) 1
      rw [ForwardSubgradientProbe.constrained_interval_singleton]
      exact mem_singleton 0
  have hm : (2 : ℝ) ∈ SourceSubgradientSum f 1 := by
    refine ⟨G, hG, ?_⟩
    norm_num [G, Fin.sum_univ_two]
  have hs := theorem_2_23_inclusion f hp 1 hm
  simpa only [f, Fin.sum_univ_two, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hs

theorem concave_quadratic_no_support (g : ℝ) :
    g ∉ SourceSubdifferential (fun y : ℝ => ((-y^2 : ℝ) : EReal)) 0 := by
  intro hg
  have h1 := hg 1
  have hm := hg (-1)
  rw [← EReal.coe_add] at h1 hm
  change (((-(0 : ℝ)^2 + (1 - 0) * g : ℝ) : EReal)) ≤ ((-(1 : ℝ)^2 : ℝ) : EReal) at h1
  change (((-(0 : ℝ)^2 + (-1 - 0) * g : ℝ) : EReal)) ≤ ((-(-1 : ℝ)^2 : ℝ) : EReal) at hm
  have h1r : -(0 : ℝ)^2 + (1 - 0) * g ≤ -(1 : ℝ)^2 := by exact_mod_cast h1
  have hmr : -(0 : ℝ)^2 + (-1 - 0) * g ≤ -(-1 : ℝ)^2 := by exact_mod_cast hm
  nlinarith

theorem nonconvex_vacuous_inclusion (g : ℝ) :
    g ∉ SourceSubgradientSum
      (fun _ : Fin 1 => fun y : ℝ => ((-y^2 : ℝ) : EReal)) 0 := by
  rintro ⟨G, hG, hsum⟩
  exact concave_quadratic_no_support (G 0) (hG 0)

theorem empty_family_zero_support :
    (0 : ℝ) ∈ SourceSubdifferential
      (fun y : ℝ => ∑ i : Fin 0, ((y^2 : ℝ) : EReal)) 1 := by
  let f : Fin 0 → ℝ → EReal := fun _ y => ((y^2 : ℝ) : EReal)
  have hp : ∀ i, SourceProper (f i) := fun i => Fin.elim0 i
  have hm : (0 : ℝ) ∈ SourceSubgradientSum f 1 := by
    refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
    simp
  exact theorem_2_23_inclusion f hp 1 hm

#print axioms quadratic_plus_constraint_support
#print axioms concave_quadratic_no_support
#print axioms nonconvex_vacuous_inclusion
#print axioms empty_family_zero_support
end SumRuleProbe
