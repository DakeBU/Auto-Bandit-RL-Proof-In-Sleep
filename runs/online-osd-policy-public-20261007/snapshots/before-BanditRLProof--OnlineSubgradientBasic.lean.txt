/-
Orabona v10 printed16-17/PDF28-29: Definition2.20, the required adjacent
outside-domain/dom-subdifferential inclusion observation, and Theorem2.21.
Two retained proofs, one complete definition; zero new math code/nodes.
The printed definition explicitly restricts to proper functions. The generic
SourceSubdifferential predicate accepts all EReal functions, a wider library
scope faithful on proper functions. At bottom points and for identically top
functions every vector supports; outside-domain emptiness needs properness.
EffectiveDomain excludes top but includes bottom generically; SourceProper
excludes bottom and supplies a genuine finite global witness. The point-domain
proof uses that witness/support, drops source convexity (stronger theorem),
and exactly gives dom subdifferential inclusion and outside emptiness via
witness unpacking. No converse or support-existence producer is claimed.
Theorem2.21 uses globally real f, Convex V, and existing GLOBAL supports at
EVERY point of V, tested at ALL ambient y. This is the printed hypothesis;
ConvexOn is produced by nonnegative weighted supports and inner cancellation,
including weights0/1. No merely finite-on-V extended-real extension is claimed.
Actual arbitrary real inner-product scope generalizes finite Euclidean source;
no CompleteSpace/FiniteDimensional premises. Ambient E has zero/nonempty;
V may be empty/full/unbounded. Two independent leaves share the definition,
not a mutual theorem dependency chain. Three scoped nodes/320 direct references
are not full/canary graph export. Whole3canaries/6named kernel dependency
checks/2nativeguards are distinct from combined acceptance gates.
Initial context source-properness prose was corrected before stabilization;
original draft history remains preserved. Interior existence and the stronger
relative-interior footnote, Theorems2.22/2.23, Chapter2 and the persistent
Chapters1-16 Goal remain mandatory/incomplete.
-/
import BanditRLProof.OnlineClosedProper
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SourceSubdifferential (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}

theorem subgradient_point_finite (f : E → EReal) (hf : SourceProper f)
    (x g : E) (hg : g ∈ SourceSubdifferential f x) :
    x ∈ effectiveDomain f := by
  obtain ⟨y, r, hr⟩ := hf.2
  change f x < ⊤
  by_contra h
  have hx : f x = ⊤ := eq_top_iff.mpr (not_lt.mp h)
  have hi := hg y
  simp [hx, hr] at hi

theorem theorem_2_21 (f : E → ℝ) (V : Set E) (hV : Convex ℝ V)
    (hsub : ∀ x ∈ V, (SourceSubdifferential (fun y => (f y : EReal)) x).Nonempty) :
    ConvexOn ℝ V f := by
  refine ⟨hV, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨g, hg⟩ := hsub (a • x + b • y) (hV hx hy ha hb hab)
  have h1 := hg x
  have h2 := hg y
  simp only [← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
  have hz : a * inner ℝ g (x - (a • x + b • y)) +
      b * inner ℝ g (y - (a • x + b • y)) = 0 := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    have he : b = 1 - a := by linarith
    rw [he]
    ring
  have h1' := mul_le_mul_of_nonneg_left h1 ha
  have h2' := mul_le_mul_of_nonneg_left h2 hb
  have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  nlinarith
end BanditRL.OnlineConvex
