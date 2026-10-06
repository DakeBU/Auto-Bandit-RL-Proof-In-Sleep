/-
Orabona v10 Example2.27 printed18/PDF30.
ONE main-text Example2.27, THREE branches of ONE full set equality, with twelve supporting library proofs and two complete retained definitions. THIRTEEN retained proofs, FIVE old canary proofs, zero new mathematical/TEST/registry nodes.
Both owned definitions and every public helper retain intrinsic NormedAddCommGroup E and InnerProductSpace real E. Only hinge_subdifferential_hull and example_2_27 explicitly add finite dimension. Borrowed properness/domain/real epigraph definitions have arbitrary ambient E, epigraph convexity uses AddCommGroup/Module real, and the actual finite maximum needs only an arbitrary E and finite nonempty index. Borrowed S/U use intrinsic real inner-product structure; U additionally has finite nonempty indexing, with no FD or function regularity premise.
Finite-dimensional real inner-product spaces include the source Euclidean instances; no separately certified coordinate-isometry or setting functor. Finite-dimensional completeness is derived where the upstream maximum rule needs it; no extra CompleteSpace or positive-dimension premise.
The shared global support predicate accepts arbitrary EReal functions, including improper ones, beyond the printed proper-function convention. Here the actual hinge and both real affine components are finite everywhere, proper, convex and ambient-continuous, so this source instance has no excluded domain query. These component facts are constructed rather than supplied.
Every z,x and every candidate support g; every ambient support-test y. No nonzero z, norm or domain bound, label/data constraint, supplied support formula, differentiability oracle or selected-support assumption.
A vector g supporting inner(a,y)+b is tested at y=x+(g-a). The actual supporting inequality forces inner(g-a,g-a)<=0, hence g=a. Conversely, the affine identity gives support at EVERY ambient y. This proves the full affine singleton without finite dimension.
The complete retained hingeFamily definition maps Bool false to the affine slope0/offset0 and Bool true to slope-z/offset1. Its two concrete components are f0(y)=0 and f1(y)=inner(-z,y)+1; the definition itself has no finite-dimension or function-regularity premise. Properness, convex epigraphs, finite query values and ambient continuity are proved from real affine algebra. Actual finite-maximum bounds identify their maximum with the hinge, then the full Theorem2.26 yields the ordinary hull of ALL active component supports.
For m(x)=1-inner(z,x), negative margin activates only f0 and gives{0}; positive margin only f1 and gives{-z}; zero margin activates both and gives the active union{0,-z}. Strict signs exclude the inactive component. The active union itself omits genuine boundary mixtures.
The ordinary convex hull of{0,-z} is the entire segment{-alpha z:alpha in[0,1]}, including both endpoints and every intermediate mixture; singleton hulls remain singletons. Both inclusions of the three-branch equality follow, without a hull closure or membership-only replacement.
All FIVE unchanged scalar canaries: z1,x2 full{0}; z1,x0 full{-1}; z1,x1 fullinterval[-1,0]; actual -1/2 belongs to the full support but not the active union and +1 is rejected; z0 gives{0} at EVERY scalar x. For z0 the margin is1 and the loss is constant1, so this is the positive-margin branch, not a boundary test. No new or actual2D hinge canary is claimed.
Only Example2.27 and its necessary retained foundations. Next Theorem2.28 affine transport and all remaining Chapter1/2 maintext and necessary appendix obligations REQUIRED, including nine OTHER Chapter1 main-relative contributor-contract gaps. Chapter2 mandatory total null/incomplete; Chapters3-16 unenumerated; whole Goal ACTIVE. No algorithm/regret/probability/feedback/computable or measurable selection guarantee, merge/deploy/main/live update or worktree retirement.
-/
import BanditRLProof.OnlineSubgradientMax

/-!
# Full hinge-loss subdifferential
Orabona arXiv:1912.13213v10, Example2.27 printed18 / PDF30.
The actual loss max(1-inner(z,x),0) has the full three-branch global
subdifferential, including the entire closed segment at equality and z=0.
Affine supports are constructed, and the full finite-maximum rule is actually
instantiated. This package is not Chapter2 or whole-book completion.
-/
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

end BanditRL.OnlineConvex
