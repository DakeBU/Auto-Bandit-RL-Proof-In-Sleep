import BanditRLProof.LowerBounds.FinitePartitionKL
import BanditRLProof.LowerBounds.RelativeEntropyFiltration
import Mathlib.Data.Fintype.Pi

/-! The finite-discretisation definition of KL equals the RN definition. -/

namespace BanditRLProof.LowerBounds

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A measurable finite-range map admits a finite code and an exact decoder. -/
theorem exists_fin_encoding_of_finite_range
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (f : α → β) (hf : Measurable f)
    (hfin : (Set.range f).Finite) :
    ∃ (n : ℕ) (g : α → Fin n), Measurable g ∧
      ∃ d : Fin n → β, f = d ∘ g := by
  classical
  letI : Fintype (Set.range f) := hfin.fintype
  let e := Fintype.equivFin (Set.range f)
  let g : α → Fin (Fintype.card (Set.range f)) := fun x => e ⟨f x, ⟨x, rfl⟩⟩
  refine ⟨_, g, (measurable_of_countable e).comp hf.subtype_mk,
    (fun i => (e.symm i).val), ?_⟩
  funext x
  simp [g]

/-- Each density-approximation layer is contained in a finite observation sigma-algebra. -/
theorem exists_fin_observation_densityApproximation
    {α : Type*} [m : MeasurableSpace α] (r : α → ENNReal) (n : ℕ) :
    ∃ (k : ℕ) (g : α → Fin k) (_hg : Measurable g),
      densityApproximationFiltration r n ≤
        (inferInstance : MeasurableSpace (Fin k)).comap g := by
  classical
  let H : α → (Fin (n + 1) → ENNReal) := fun x i => SimpleFunc.eapprox r i.val x
  have hH : Measurable H := measurable_pi_lambda _ fun i => (SimpleFunc.eapprox r i.val).measurable
  have hfinite : (Set.range H).Finite := by
    apply (Set.Finite.pi' (fun i : Fin (n + 1) => (SimpleFunc.eapprox r i.val).finite_range)).subset
    rintro y ⟨x, rfl⟩ i
    exact ⟨x, rfl⟩
  obtain ⟨k, g, hg, d, hd⟩ := exists_fin_encoding_of_finite_range H hH hfinite
  refine ⟨k, g, hg, ?_⟩
  change (⨆ j ≤ n, MeasurableSpace.comap (SimpleFunc.eapprox r j) _) ≤ _
  refine iSup₂_le fun j hj => ?_
  apply measurable_iff_comap_le.1
  have hcoord : (SimpleFunc.eapprox r j : α → ENNReal) =
      (fun z => d z ⟨j, Nat.lt_succ_of_le hj⟩) ∘ g := by
    funext x
    exact congrFun (congrFun hd x) ⟨j, Nat.lt_succ_of_le hj⟩
  rw [hcoord]
  exact (measurable_of_countable _).comp (measurable_iff_comap_le.2 le_rfl)

/-- Refining a sub-sigma-algebra can only increase its retained KL. -/
theorem relativeEntropy_trim_mono
    {α : Type*} {m₁ m₂ m₀ : MeasurableSpace α} (P Q : @Measure α m₀)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₀) :
    @relativeEntropy α m₁ (P.trim (h₁₂.trans h₂)) (Q.trim (h₁₂.trans h₂)) ≤
      @relativeEntropy α m₂ (P.trim h₂) (Q.trim h₂) := by
  simpa only [trim_trim] using
    (relativeEntropy_trim_le (P := P.trim h₂) (Q := Q.trim h₂) h₁₂)

/-- Textbook Eq. (14.5) and Theorem 14.1: finite discretisations recover RN KL. -/
theorem finitePartitionRelativeEntropy_eq_relativeEntropy
    {α : Type*} [m : MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    finitePartitionRelativeEntropy P Q = relativeEntropy P Q := by
  by_cases h : P ≪ Q
  · apply le_antisymm (finitePartitionRelativeEntropy_le_relativeEntropy P Q)
    rw [relativeEntropy_eq_iSup_densityApproximation_trim P Q h]
    refine iSup_le fun n => ?_
    obtain ⟨k, g, hg, hle⟩ := exists_fin_observation_densityApproximation (P.rnDeriv Q) n
    calc
      _ ≤ @relativeEntropy α ((inferInstance : MeasurableSpace (Fin k)).comap g)
          (P.trim hg.comap_le) (Q.trim hg.comap_le) :=
        relativeEntropy_trim_mono P Q hle hg.comap_le
      _ = relativeEntropy (P.map g) (Q.map g) :=
        (relativeEntropy_map_eq_trim_of_absolutelyContinuous P Q h g hg).symm
      _ ≤ _ := relativeEntropy_map_le_finitePartitionRelativeEntropy P Q g hg
  · exact finitePartitionRelativeEntropy_eq_relativeEntropy_of_not_absolutelyContinuous P Q h

end
end BanditRLProof.LowerBounds
