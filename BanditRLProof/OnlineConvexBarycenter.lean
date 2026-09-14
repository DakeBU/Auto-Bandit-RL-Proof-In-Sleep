import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open Set Filter MeasureTheory
universe u v
namespace BanditRL.OnlineConvex

section SupportEquality
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem supporting_functional_ae_eq_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Integrable X μ) (a : E →L[ℝ] ℝ)
    (hle : ∀ᵐ ω ∂μ, a (X ω) ≤ a (∫ ω, X ω ∂μ)) :
    ∀ᵐ ω ∂μ, a (X ω) = a (∫ ω, X ω ∂μ) := by
  apply (integral_eq_iff_of_ae_le (a.integrable_comp hX) (integrable_const _) hle).mp
  rw [a.integral_comp_comm hX]
  simp

end SupportEquality

section FiniteSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem supporting_functional_at_closure (s : Set E) (hs : Convex ℝ s)
    (x : E) (hx : x ∈ closure s) (hxi : x ∉ interior s) :
    ∃ a : E →L[ℝ] ℝ, a ≠ 0 ∧ ∀ y ∈ s, a y ≤ a x := by
  by_cases hint : (interior s).Nonempty
  · exact geometric_hahn_banach_of_nonempty_interior_point hs hxi hint
  · let A := affineSpan ℝ s
    have hA : A ≠ ⊤ := fun h => hint (hs.interior_nonempty_iff_affineSpan_eq_top.mpr h)
    have hxA : x ∈ A := closure_minimal (subset_affineSpan ℝ s) A.closed_of_finiteDimensional hx
    have hdir : A.direction < ⊤ := lt_top_iff_ne_top.mpr fun h =>
      hA ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxA⟩).mp h)
    obtain ⟨a, hane, ha⟩ := A.direction.exists_le_ker_of_lt_top hdir
    refine ⟨a.toContinuousLinearMap, ?_, ?_⟩
    · intro hz
      exact hane (congrArg ContinuousLinearMap.toLinearMap hz)
    · intro y hy
      have hxy : y - x ∈ A.direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ s hy) hxA
      have hz : a (y - x) = 0 := ha hxy
      rw [map_sub] at hz
      change a y ≤ a x
      exact (sub_eq_zero.mp hz).le

end FiniteSupport

section Barycenter
variable {Ω : Type v} [MeasurableSpace Ω]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem integral_mem_convex_finiteDimensional (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Set E) (hs : Convex ℝ s) (X : Ω → E) (hX : Integrable X μ)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ s) :
    (∫ ω, X ω ∂μ) ∈ s := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    have H : ∀ n : ℕ, ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F], Module.finrank ℝ F = n →
        ∀ (t : Set F), Convex ℝ t → ∀ (Z : Ω → F), Integrable Z μ →
        (∀ᵐ ω ∂μ, Z ω ∈ t) → (∫ ω, Z ω ∂μ) ∈ t := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro F instN instS instF hdim t ht Z hZ hmemZ
        let m : F := ∫ ω, Z ω ∂μ
        by_contra hnot
        have hcl : m ∈ closure t := ht.closure.integral_mem isClosed_closure
          (hmemZ.mono fun ω hω => subset_closure hω) hZ
        have hni : m ∉ interior t := fun hm => hnot (interior_subset hm)
        obtain ⟨a, ha, has⟩ := supporting_functional_at_closure t ht m hcl hni
        have heq : ∀ᵐ ω ∂μ, a (Z ω) = a m :=
          supporting_functional_ae_eq_mean μ Z hZ a (hmemZ.mono fun ω hω => has (Z ω) hω)
        let K : Submodule ℝ F := a.toLinearMap.ker
        have hK : K ≠ ⊤ := by
          intro hk
          apply ha
          ext z
          have hz := LinearMap.congr_fun (LinearMap.ker_eq_top.mp hk) z
          exact hz
        have hless : Module.finrank ℝ K < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hK
        let Y : Ω → K := fun ω => if h : Z ω - m ∈ K then ⟨Z ω - m, h⟩ else 0
        have hYae : (fun ω => (Y ω : F)) =ᵐ[μ] fun ω => Z ω - m := by
          filter_upwards [heq] with ω hω
          have hk : Z ω - m ∈ K := by
            change a (Z ω - m) = 0
            rw [map_sub, hω, sub_self]
          simp [Y, hk]
        have hYcoe : Integrable (fun ω => (Y ω : F)) μ :=
          (hZ.sub (integrable_const m)).congr hYae.symm
        have hY : Integrable Y μ :=
          (K.subtypeₗᵢ.isometry.lipschitz.integrable_comp_iff_of_antilipschitz
            K.subtypeₗᵢ.isometry.antilipschitz rfl).mp hYcoe
        have hYzero : (∫ ω, Y ω ∂μ) = 0 := by
          apply Subtype.ext
          change ((∫ ω, Y ω ∂μ : K) : F) = 0
          calc
            _ = ∫ ω, (Y ω : F) ∂μ := (K.subtypeL.integral_comp_comm hY).symm
            _ = ∫ ω, Z ω - m ∂μ := integral_congr_ae hYae
            _ = 0 := by rw [integral_sub hZ (integrable_const m)]; simp [m]
        let A : K →ᵃ[ℝ] F := K.subtype.toAffineMap + AffineMap.const ℝ K m
        let tK : Set K := A ⁻¹' t
        have htK : Convex ℝ tK := ht.affine_preimage A
        have hmK : ∀ᵐ ω ∂μ, Y ω ∈ tK := by
          filter_upwards [hmemZ, hYae] with ω hω hYω
          change (Y ω : F) + m ∈ t
          rw [hYω, sub_add_cancel]
          exact hω
        have hm := ih (Module.finrank ℝ K) hless K rfl tK htK Y hY hmK
        rw [hYzero] at hm
        apply hnot
        simpa [tK, A] using hm
    exact H (Module.finrank ℝ E) E rfl s hs X hX hmem

end Barycenter
end BanditRL.OnlineConvex
