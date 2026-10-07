/-
Orabona v10 Definition2.29/Theorem2.30 printed19/PDF31.
ONE printed Definition2.29 and ONE Theorem2.30: ONE retained owned definition and ONE retained proof, ZERO new mathematical, TEST or registry nodes. Whole18oldcanaryproofs/sixTESTdefinitions/twoabbreviations unchanged.
SourceLipschitzOn needs only NormedAddCommGroup, with no real Module, inner product or finite dimension. The theorem adds real InnerProductSpace and FiniteDimensional; coordinate-free Euclidean L2 extension, no separate coordinate adapter. FIVE shared borrowed contexts: SourceProper/effectiveDomain/realEpigraph arbitrary carrier; SourceSubdifferential intrinsic norm/inner; IsConvexExtended AddCommGroup and real Module. None of the five is owned or newly defined. Actual compiled prints supersede the historical preparation pending-type flag evidentially.
Definition2.29 is represented by genuine finite real-value witnesses at EVERY x in arbitrary V together with the actual all-pairs absolute difference bound for the chosen norm. Generic EReal input may have bottom or top outside V; no standalone global properness/convexity assertion. Under the source globally no-bottom codomain, V subsetdom guarantees exactly these finite values. Empty V is vacuous; a toReal-only bound at infinity is insufficient. This definition has no theorem proof or support-production conclusion.
L:NNReal includes zero and makes the conventional nonnegative Lipschitz constant explicit; printed Definition2.29/Theorem2.30 do not explicitly write L>=0. Their zero-support proof case uses this convention. The actual proper convex constant0 on Euclidean Fin0 obeys every pair inequality at realL=-1 since distances0, but genuine support0 violates norm0<=-1. This refutes unrestricted realL for the admitted zero-dimensional extension, not a separately positive-dimensional source formulation. Zero dimension, zero L and empty interior remain allowed. Separate current source convention review accepted-with-explicit-delta.
The full iff uses proper convex f and U=AMBIENT interior effectiveDomain. Properness excludes bottom globally, interior domain excludes top before real conversion. EVERY support g at EVERY interior x tests EVERY ambient y. No selected-gradient-only conclusion, relative-interior/whole-domain/boundary extension, closedness, differentiability, boundedness, positive L/dimension, nonempty interior or supplied support-existence premise.
Forward obtain an actual positive-radius ball in U and restrict genuine finite values/all-pairs bounds; shared norm-ball proof perturbs along the normalized given support. Reverse construct actual global supports at BOTH x and y from proper convexity and interior membership, certify finite EReal conversion, apply both global support inequalities and Cauchy-Schwarz/two signs to obtain the same-L absolute bound. No assumed norm conclusion or support-existence oracle.
Exactly18unchanged canary proofs/sixTESTdefinitions/twoabbreviations: actual |.| proper/domain/convex/L1 yields ALLsupport bound and nonzero supports+1 at2 and -1 at-2; actual affine slope3 reverse; constant0/L0 and exactsupport0; singleton indicator empty interior but boundarysupport3; halfline indicator interiorbound0 versus boundary-2 and all-toReal0 trap that fails actual finite witnesses on univ; constant9 on EuclideanFin0/L0; separate properconvex constant0 realL=-1 obstruction. Six scenario groups are not six total proofs. No new/2D/matrix-coordinate test claimed.
Only bounded Definition2.29/Theorem2.30 source refinement. Legacy queue0 is NOT Chapter2 mandatory total or completion. Adjacent 2D |x1| nondifferentiability, Lemma2.31/OSD/linearization/Example2.32/unitanalysis and all other Chapter1/2 maintext, nine OTHER Chapter1 main-relative contract gaps and necessary appendices remain REQUIRED. Chapter2totalnull/incomplete,3-16unenumerated,totalGoalACTIVE. No algorithm/regret/probability/feedback/computable/measurable selection, merge/deploy/mainlive/worktree retirement.
-/
import BanditRLProof.OnlineSubgradientDifferentiability
/-!
# Interior Lipschitz and subgradient bounds
Orabona arXiv:1912.13213v10, Definition 2.29 / Theorem 2.30, printed 19 / PDF 31.
The full equivalence on the ambient interior of the effective domain uses
actual finite values and every global support. Proper convexity constructs
both supports needed for the reverse implication. The Lipschitz constant is
explicitly nonnegative (NNReal, including zero), matching the source proof's
convention. This is not unrestricted real-L equivalence: the source-audit
fixture proves a negative-L counterexample in dimension zero.
Zero dimension, zero constant and empty interior are retained; boundary
supports and infinity-toReal projections are not covered by a fake bound.
This package is not Chapter 2 or whole-book completion.
-/
noncomputable section
open Set
open scoped Topology NNReal
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite values on V and the actual all-pairs Lipschitz inequality.
The constant is explicitly nonnegative, including zero. -/
def SourceLipschitzOn (f : E → EReal) (V : Set E) (L : ℝ≥0) : Prop :=
  (∀ x ∈ V, ∃ a : ℝ, f x = (a : EReal)) ∧
    ∀ x ∈ V, ∀ y ∈ V, |(f x).toReal - (f y).toReal| ≤ (L : ℝ) * ‖x - y‖

theorem theorem_2_30 [FiniteDimensional ℝ E]
    (f : E → EReal) (hp : SourceProper f) (hc : IsConvexExtended f) (L : ℝ≥0) :
    SourceLipschitzOn f (interior (effectiveDomain f)) L ↔
      ∀ x ∈ interior (effectiveDomain f), ∀ g ∈ SourceSubdifferential f x,
        ‖g‖ ≤ (L : ℝ) := by
  constructor
  · intro hl x hx g hg
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
    apply subgradient_norm_le_lipschitz_ball f x r hr L ?_ ?_ g hg
    · intro y hy
      exact hl.1 y (hball hy)
    · apply LipschitzOnWith.of_dist_le_mul
      intro y hy z hz
      simpa only [Real.dist_eq, dist_eq_norm] using hl.2 y (hball hy) z (hball hz)
  · intro hb
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxdom : x ∈ effectiveDomain f := interior_subset hx
      exact ⟨(f x).toReal,
        (EReal.coe_toReal (ne_of_lt hxdom) (hp.1 x)).symm⟩
    · intro x hx y hy
      obtain ⟨gx, hgx⟩ := subgradient_exists_of_domain_interior f hp hc x hx
      obtain ⟨gy, hgy⟩ := subgradient_exists_of_domain_interior f hp hc y hy
      have hxdom : x ∈ effectiveDomain f := interior_subset hx
      have hydom : y ∈ effectiveDomain f := interior_subset hy
      have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hp.1 x)
      have hyv := EReal.coe_toReal (ne_of_lt hydom) (hp.1 y)
      have hxy := hgx y
      have hyx := hgy x
      rw [← hxv, ← hyv, ← EReal.coe_add] at hxy
      rw [← hyv, ← hxv, ← EReal.coe_add] at hyx
      have hxyR := EReal.coe_le_coe_iff.mp hxy
      have hyxR := EReal.coe_le_coe_iff.mp hyx
      have hxg : -(inner ℝ gx (y - x)) ≤ (L : ℝ) * ‖x - y‖ := calc
        -(inner ℝ gx (y - x)) ≤ |inner ℝ gx (y - x)| := neg_le_abs _
        _ ≤ ‖gx‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
        _ ≤ (L : ℝ) * ‖y - x‖ := mul_le_mul_of_nonneg_right (hb x hx gx hgx) (norm_nonneg _)
        _ = (L : ℝ) * ‖x - y‖ := by rw [norm_sub_rev]
      have hyg : -(inner ℝ gy (x - y)) ≤ (L : ℝ) * ‖x - y‖ := calc
        -(inner ℝ gy (x - y)) ≤ |inner ℝ gy (x - y)| := neg_le_abs _
        _ ≤ ‖gy‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
        _ ≤ (L : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right (hb y hy gy hgy) (norm_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith

end BanditRL.OnlineConvex
