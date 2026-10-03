import BanditRLProof.OnlineSubgradientMax
noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def sourceHinge (z x : E) : EReal := ((max (1 - inner ℝ z x) 0 : ℝ) : EReal)

theorem affine_subdifferential (a : E) (b : ℝ) (x : E) :
    SourceSubdifferential (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x = {a} := by
  ext g
  change (∀ y, ((inner ℝ a x + b : ℝ) : EReal) +
    (inner ℝ g (y - x) : EReal) ≤ ((inner ℝ a y + b : ℝ) : EReal)) ↔ g = a
  constructor
  · intro hg
    have h := hg (x + (g - a))
    rw [← EReal.coe_add] at h
    have hr := EReal.coe_le_coe_iff.mp h
    simp only [add_sub_cancel_left, inner_add_right] at hr
    have hd : inner ℝ (g - a) (g - a) ≤ 0 := by
      rw [inner_sub_left]
      linarith
    have hz : g - a = 0 := inner_self_eq_zero.mp
      (le_antisymm hd real_inner_self_nonneg)
    exact sub_eq_zero.mp hz
  · intro hg
    subst g
    intro y
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    rw [inner_sub_right]
    linarith



def hingeFamily (z : E) (i : Bool) (y : E) : EReal :=
  ((inner ℝ (if i then -z else 0) y + (if i then 1 else 0) : ℝ) : EReal)

theorem affine_proper (a : E) (b : ℝ) :
    SourceProper (fun y => ((inner ℝ a y + b : ℝ) : EReal)) := by
  exact ⟨fun y => EReal.coe_ne_bot _, 0, b, by simp⟩

theorem affine_convex (a : E) (b : ℝ) :
    IsConvexExtended (fun y => ((inner ℝ a y + b : ℝ) : EReal)) := by
  rw [convexExtended_iff_toReal _ (affine_proper a b).1]
  have hd : effectiveDomain (fun y => ((inner ℝ a y + b : ℝ) : EReal)) = univ := by
    ext y
    simp only [effectiveDomain, mem_setOf_eq, mem_univ, iff_true]
    exact EReal.coe_lt_top _
  rw [hd]
  simp only [EReal.toReal_coe]
  refine ⟨convex_univ, ?_⟩
  intro u hu v hv p q hp hq hpq
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  have hb := congrArg (fun t : ℝ => t * b) hpq
  nlinarith

theorem affine_continuous (a : E) (b : ℝ) (x : E) :
    ContinuousAt (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x := by
  exact (continuous_coe_real_ereal.comp
    ((continuous_const.inner continuous_id).add continuous_const)).continuousAt

theorem hinge_max_identity (z : E) : SourceFiniteMax (hingeFamily z) = sourceHinge z := by
  funext x
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun i => hingeFamily z i x)).mpr
    intro i hi
    cases i
    · change ((inner ℝ (0 : E) x + 0 : ℝ) : EReal) ≤ (max (1 - inner ℝ z x) 0 : EReal)
      apply EReal.coe_le_coe_iff.mpr
      simpa using le_max_right (1 - inner ℝ z x) 0
    · change ((inner ℝ (-z) x + 1 : ℝ) : EReal) ≤ (max (1 - inner ℝ z x) 0 : EReal)
      apply EReal.coe_le_coe_iff.mpr
      simpa only [inner_neg_left, neg_add_eq_sub] using le_max_left (1 - inner ℝ z x) 0
  · by_cases h : 0 ≤ 1 - inner ℝ z x
    · have hi := Finset.le_sup' (fun i => hingeFamily z i x) (Finset.mem_univ true)
      change hingeFamily z true x ≤ SourceFiniteMax (hingeFamily z) x at hi
      calc
        sourceHinge z x = hingeFamily z true x := by
          change ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) =
            ((inner ℝ (-z) x + 1 : ℝ) : EReal)
          apply congrArg (fun t : ℝ => (t : EReal))
          rw [max_eq_left h, inner_neg_left]
          ring
        _ ≤ _ := hi
    · have hi := Finset.le_sup' (fun i => hingeFamily z i x) (Finset.mem_univ false)
      change hingeFamily z false x ≤ SourceFiniteMax (hingeFamily z) x at hi
      calc
        sourceHinge z x = hingeFamily z false x := by
          change ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) =
            ((inner ℝ (0 : E) x + 0 : ℝ) : EReal)
          rw [max_eq_right (le_of_not_ge h), inner_zero_left, zero_add]
        _ ≤ _ := hi

theorem hinge_subdifferential_hull [FiniteDimensional ℝ E] (z x : E) :
    SourceSubdifferential (sourceHinge z) x =
      convexHull ℝ (SourceActiveSubgradientUnion (hingeFamily z) x) := by
  rw [← hinge_max_identity z]
  apply theorem_2_26
  · intro i
    exact affine_proper _ _
  · intro i
    exact affine_convex _ _
  · intro i
    exact EReal.coe_lt_top _
  · intro i
    exact affine_continuous _ _ _

theorem hinge_family_support (z : E) (i : Bool) (x : E) :
    SourceSubdifferential (hingeFamily z i) x = {if i then -z else 0} :=
  affine_subdifferential _ _ _

theorem hinge_family_false (z x : E) : hingeFamily z false x = ((0 : ℝ) : EReal) := by
  simp only [hingeFamily, Bool.false_eq_true, if_false, inner_zero_left, zero_add]

theorem hinge_family_true (z x : E) :
    hingeFamily z true x = ((1 - inner ℝ z x : ℝ) : EReal) := by
  change ((inner ℝ (-z) x + 1 : ℝ) : EReal) = ((1 - inner ℝ z x : ℝ) : EReal)
  apply congrArg (fun t : ℝ => (t : EReal))
  rw [inner_neg_left]
  ring

theorem hinge_active_negative (z x : E) (h : 1 - inner ℝ z x < 0) :
    SourceActiveSubgradientUnion (hingeFamily z) x = {(0 : E)} := by
  ext g
  have hn : ((1 - inner ℝ z x : ℝ) : EReal) ≠ ((0 : ℝ) : EReal) :=
    ne_of_lt (EReal.coe_lt_coe_iff.mpr h)
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq, Bool.exists_bool,
    hinge_max_identity, hinge_family_support, hinge_family_false, hinge_family_true,
    Bool.false_eq_true, if_false, if_true, mem_singleton_iff]
  change (((0 : ℝ) : EReal) = ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) ∧ g = 0) ∨
    (((1 - inner ℝ z x : ℝ) : EReal) = ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) ∧ g = -z) ↔ g = 0
  rw [max_eq_right h.le]
  simp only [hn, false_and, or_false, true_and]

theorem hinge_active_positive (z x : E) (h : 0 < 1 - inner ℝ z x) :
    SourceActiveSubgradientUnion (hingeFamily z) x = {-z} := by
  ext g
  have hn : ((0 : ℝ) : EReal) ≠ ((1 - inner ℝ z x : ℝ) : EReal) :=
    ne_of_lt (EReal.coe_lt_coe_iff.mpr h)
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq, Bool.exists_bool,
    hinge_max_identity, hinge_family_support, hinge_family_false, hinge_family_true,
    Bool.false_eq_true, if_false, if_true, mem_singleton_iff]
  change (((0 : ℝ) : EReal) = ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) ∧ g = 0) ∨
    (((1 - inner ℝ z x : ℝ) : EReal) = ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) ∧ g = -z) ↔ g = -z
  rw [max_eq_left h.le]
  simp only [hn, false_and, false_or, true_and]

theorem hinge_active_zero (z x : E) (h : 1 - inner ℝ z x = 0) :
    SourceActiveSubgradientUnion (hingeFamily z) x = {(0 : E), -z} := by
  ext g
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq, Bool.exists_bool,
    hinge_max_identity, hinge_family_support, hinge_family_false, hinge_family_true,
    Bool.false_eq_true, if_false, if_true, mem_singleton_iff, mem_insert_iff]
  change (((0 : ℝ) : EReal) = ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) ∧ g = 0) ∨
    (((1 - inner ℝ z x : ℝ) : EReal) = ((max (1 - inner ℝ z x) 0 : ℝ) : EReal) ∧ g = -z) ↔ g = 0 ∨ g = -z
  rw [h, max_self]
  simp only [true_and]

theorem example_2_27 [FiniteDimensional ℝ E] (z x : E) :
    SourceSubdifferential (sourceHinge z) x =
      if 1 - inner ℝ z x < 0 then {0}
      else if 1 - inner ℝ z x = 0 then
        {g | ∃ α ∈ Icc (0 : ℝ) 1, g = -(α • z)}
      else {-z} := by
  rw [hinge_subdifferential_hull]
  split_ifs with hn hz
  · rw [hinge_active_negative z x hn, convexHull_singleton]
  · rw [hinge_active_zero z x hz, convexHull_pair, segment_eq_image]
    ext g
    simp only [mem_image, mem_Icc, mem_setOf_eq, smul_zero, zero_add, smul_neg]
    constructor
    · rintro ⟨α, hα, he⟩
      exact ⟨α, hα, he.symm⟩
    · rintro ⟨α, hα, he⟩
      exact ⟨α, hα, he.symm⟩
  · rw [hinge_active_positive z x (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)),
      convexHull_singleton]

#print axioms BanditRL.OnlineConvex.example_2_27
end BanditRL.OnlineConvex
