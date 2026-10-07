/-
Orabona v10, printed16/PDF28: Definitions2.16/2.18, Examples2.17/2.19,
and the required unnumbered closedness/lower-semicontinuity equivalence.
Three retained proofs and two complete definitions; zero new math code/nodes.
The source gives Euclidean and more generally Hausdorff sufficient scope;
actual arbitrary topological scope is a stronger generalization, no T2 premise.
SourceClosed uses REAL cuts; the proof derives bottom strict superlevels by
the union of real cuts, handles top by empty, and admits both infinite values.
No convexity/properness/no-bottom or closed-epigraph replacement is assumed.
SourceProper itself has no topology binder; the ACTUAL proper-indicator iff
still retains TopologicalSpace E. No Nonempty E or closed/convex V premise.
The SAME canonical zero-on-V/top-outside extendedIndicator is reused.
Direct indicator cuts and genuine finite witnesses prove the two indicator
equivalences independently; reading order is not a theorem dependency chain.
Empty ambient: closedness vacuous, properness false. Full indicator properness
is exactly ambient nonemptiness. Bottom-improper examples use the real line.
Whole six canary proofs and all eleven named kernel dependency checks include bottom_closed.
All original headers/proof/definition bytes and whole canary remain fixed.
Chapter2 and the persistent Chapters1-16 Goal remain incomplete.
-/
import BanditRLProof.OnlineConvexExtended
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [TopologicalSpace E]

def SourceClosed (f : E → EReal) : Prop :=
  ∀ r : ℝ, IsClosed {x | f x ≤ (r : EReal)}

def SourceProper (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)

theorem sourceClosed_iff_lowerSemicontinuous (f : E → EReal) :
    SourceClosed f ↔ LowerSemicontinuous f := by
  constructor
  · intro hc
    have ho (r : ℝ) : IsOpen {x | (r : EReal) < f x} := by
      simpa only [compl_setOf, not_le] using (hc r).isOpen_compl
    apply lowerSemicontinuous_iff_isOpen_preimage.mpr
    intro a
    induction a with
    | bot =>
      have he : f ⁻¹' Ioi (⊥ : EReal) = ⋃ r : ℝ, {x | (r : EReal) < f x} := by
        ext x
        simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_setOf_eq]
        constructor
        · intro hx
          obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
          exact ⟨r, hrx⟩
        · rintro ⟨r, hr⟩
          exact (EReal.bot_lt_coe r).trans hr
      rw [he]
      exact isOpen_iUnion ho
    | coe r => exact ho r
    | top => simp
  · intro hf r
    exact hf.isClosed_preimage (r : EReal)

theorem sourceClosed_indicator_iff (V : Set E) :
    SourceClosed (extendedIndicator V) ↔ IsClosed V := by
  classical
  have hcut (r : ℝ) : {x | extendedIndicator V x ≤ (r : EReal)} =
      if 0 ≤ r then V else ∅ := by
    ext x
    by_cases hx : x ∈ V <;> by_cases hr : 0 ≤ r <;>
      simp [extendedIndicator, hx, hr]
  constructor
  · intro h
    have h0 := h 0
    simpa only [hcut, if_pos le_rfl] using h0
  · intro h r
    rw [hcut]
    split_ifs
    · exact h
    · exact isClosed_empty

theorem sourceProper_indicator_iff (V : Set E) :
    SourceProper (extendedIndicator V) ↔ V.Nonempty := by
  classical
  constructor
  · rintro ⟨hbot, x, r, hr⟩
    refine ⟨x, ?_⟩
    by_contra hx
    simp [extendedIndicator, hx] at hr
  · rintro ⟨x, hx⟩
    constructor
    · intro y
      by_cases hy : y ∈ V <;> simp [extendedIndicator, hy]
    · exact ⟨x, 0, by simp [extendedIndicator, hx]⟩
end BanditRL.OnlineConvex
