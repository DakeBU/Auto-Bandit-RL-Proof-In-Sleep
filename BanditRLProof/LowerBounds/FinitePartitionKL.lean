import BanditRLProof.LowerBounds.FiniteDiscreteKL

/-!
# Finite measurable discretisations of relative entropy

The supremum in textbook Eq. (14.5) ranges over every finite measurable
partition, represented here by measurable maps to `Fin n`. Empty cells are
harmless. The singular branch below is only one part of the required
equivalence with the Radon--Nikodym definition.
-/

namespace BanditRLProof.LowerBounds

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Convexity bounds the divergence of total masses by finite-measure KL. -/
theorem totalMass_klFun_le_relativeEntropy
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ENNReal.ofReal (InformationTheory.klFun ((P univ / Q univ).toReal)) * Q univ ≤
      relativeEntropy P Q := by
  by_cases ht : relativeEntropy P Q = (⊤ : ENNReal)
  · simp [ht]
  have hreg := relativeEntropy_ne_top_iff.1 ht
  have hb := InformationTheory.mul_klFun_le_toReal_klDiv hreg.1 hreg.2
  calc
    _ = ENNReal.ofReal (Q.real univ *
        InformationTheory.klFun (P.real univ / Q.real univ)) := by
      rw [ENNReal.ofReal_mul (measureReal_nonneg)]
      simp [measureReal_def, ENNReal.toReal_div, mul_comm]
    _ ≤ ENNReal.ofReal (relativeEntropy P Q).toReal := ENNReal.ofReal_le_ofReal hb
    _ = _ := ENNReal.ofReal_toReal ht

/-- KL splits into the restrictions to all cells of a finite observation. -/
theorem sum_relativeEntropy_restrict_fibers
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q)
    {n : ℕ} (f : α → Fin n) (hf : Measurable f) :
    (∑ i, relativeEntropy (P.restrict (f ⁻¹' {i})) (Q.restrict (f ⁻¹' {i}))) =
      relativeEntropy P Q := by
  let g : α → ENNReal := fun x => ENNReal.ofReal
    (InformationTheory.klFun (P.rnDeriv Q x).toReal)
  have hcell (i : Fin n) : MeasurableSet (f ⁻¹' {i}) := hf (measurableSet_singleton i)
  have hall : (⋃ i, f ⁻¹' {i}) = univ := by
    ext x
    simp
  calc
    _ = ∑ i, ∫⁻ x in f ⁻¹' {i}, g x ∂Q := by
      apply Finset.sum_congr rfl
      intro i _
      rw [relativeEntropy, InformationTheory.klDiv_eq_lintegral_klFun_of_ac (h.restrict _)]
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_restrict_restrict h (hcell i)] with x hx
      simp [g, hx]
    _ = ∫⁻ x, g x ∂Q := by
      rw [← tsum_fintype (L := .unconditional _), ← lintegral_iUnion hcell
        (Set.pairwise_univ.1 (Set.pairwiseDisjoint_fiber f univ)), hall,
        Measure.restrict_univ]
    _ = _ := (InformationTheory.klDiv_eq_lintegral_klFun_of_ac h).symm

/-- Finite-valued measurable observations cannot increase KL. -/
theorem relativeEntropy_finite_map_le
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {n : ℕ} (f : α → Fin n) (hf : Measurable f) :
    relativeEntropy (P.map f) (Q.map f) ≤ relativeEntropy P Q := by
  by_cases ht : relativeEntropy P Q = (⊤ : ENNReal)
  · simp [ht]
  have h := (relativeEntropy_ne_top_iff.1 ht).1
  rw [relativeEntropy_finite_klFun _ _ (h.map hf)]
  calc
    _ ≤ ∑ i, relativeEntropy (P.restrict (f ⁻¹' {i})) (Q.restrict (f ⁻¹' {i})) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Measure.map_apply hf (measurableSet_singleton _),
        Measure.restrict_apply_univ] using
        totalMass_klFun_le_relativeEntropy (P.restrict (f ⁻¹' {i})) (Q.restrict (f ⁻¹' {i}))
    _ = _ := sum_relativeEntropy_restrict_fibers P Q h f hf

/-- Relative entropy defined by the supremum over finite measurable observations. -/
def finitePartitionRelativeEntropy {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) : ENNReal :=
  ⨆ (n : ℕ) (f : α → Fin n) (_ : Measurable f),
    relativeEntropy (P.map f) (Q.map f)

/-- The finite-discretisation supremum never exceeds RN relative entropy. -/
theorem finitePartitionRelativeEntropy_le_relativeEntropy
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    finitePartitionRelativeEntropy P Q ≤ relativeEntropy P Q := by
  refine iSup_le fun n => iSup_le fun f => iSup_le fun hf => ?_
  exact relativeEntropy_finite_map_le P Q f hf

/-- Every finite measurable observation is included in the defining supremum. -/
theorem relativeEntropy_map_le_finitePartitionRelativeEntropy
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    {n : ℕ} (f : α → Fin n) (hf : Measurable f) :
    relativeEntropy (P.map f) (Q.map f) ≤ finitePartitionRelativeEntropy P Q := by
  exact le_iSup_of_le n (le_iSup_of_le f (le_iSup_of_le hf le_rfl))

/-- On an already finite observation space, the identity partition loses nothing. -/
theorem finitePartitionRelativeEntropy_fin_eq {n : ℕ} (P Q : Measure (Fin n))
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    finitePartitionRelativeEntropy P Q = relativeEntropy P Q := by
  apply le_antisymm (finitePartitionRelativeEntropy_le_relativeEntropy P Q)
  simpa using relativeEntropy_map_le_finitePartitionRelativeEntropy P Q id measurable_id

/-- The discrete KL of an observation is the exact cell-mass formula. -/
theorem relativeEntropy_finite_map_eq_if
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {n : ℕ} (f : α → Fin n) (hf : Measurable f) :
    relativeEntropy (P.map f) (Q.map f) =
      if ∀ i, Q (f ⁻¹' {i}) = 0 → P (f ⁻¹' {i}) = 0 then
        ENNReal.ofReal (∑ i, (P (f ⁻¹' {i})).toReal *
          Real.log ((P (f ⁻¹' {i})).toReal / (Q (f ⁻¹' {i})).toReal))
      else (⊤ : ENNReal) := by
  classical
  letI : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (Q.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  simpa only [Measure.map_apply hf (measurableSet_singleton _)] using
    relativeEntropy_finite_eq_if (P.map f) (Q.map f)

/-- A measurable support mismatch is detected by a two-cell observation. -/
theorem exists_binary_map_relativeEntropy_eq_top_of_event
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    {A : Set α} (hA : MeasurableSet A) (hp : P A ≠ 0) (hq : Q A = 0) :
    ∃ f : α → Fin 2, Measurable f ∧
      relativeEntropy (P.map f) (Q.map f) = (⊤ : ENNReal) := by
  classical
  let f : α → Fin 2 := fun x => if x ∈ A then 0 else 1
  have hf : Measurable f := measurable_const.ite hA measurable_const
  have hcell : f ⁻¹' {(0 : Fin 2)} = A := by
    ext x
    simp [f]
  refine ⟨f, hf, relativeEntropy_eq_top_of_atom_support_mismatch _ _ 0 ?_ ?_⟩
  · simpa [Measure.map_apply hf (measurableSet_singleton _), hcell] using hp
  · simpa [Measure.map_apply hf (measurableSet_singleton _), hcell] using hq

/-- Non-absolute-continuity forces infinite finite-partition relative entropy. -/
theorem finitePartitionRelativeEntropy_eq_top_of_not_absolutelyContinuous
    {α : Type*} [MeasurableSpace α] (P Q : Measure α) (h : ¬ P ≪ Q) :
    finitePartitionRelativeEntropy P Q = (⊤ : ENNReal) := by
  classical
  have hex : ∃ A, MeasurableSet A ∧ Q A = 0 ∧ P A ≠ 0 := by
    by_contra hn
    apply h
    apply Measure.AbsolutelyContinuous.mk
    intro A hA hq
    by_contra hp
    exact hn ⟨A, hA, hq, hp⟩
  obtain ⟨A, hA, hq, hp⟩ := hex
  obtain ⟨f, hf, htop⟩ := exists_binary_map_relativeEntropy_eq_top_of_event P Q hA hp hq
  apply top_unique
  rw [← htop]
  exact relativeEntropy_map_le_finitePartitionRelativeEntropy P Q f hf

/-- The finite-partition and RN definitions agree in the singular branch. -/
theorem finitePartitionRelativeEntropy_eq_relativeEntropy_of_not_absolutelyContinuous
    {α : Type*} [MeasurableSpace α] (P Q : Measure α) (h : ¬ P ≪ Q) :
    finitePartitionRelativeEntropy P Q = relativeEntropy P Q := by
  rw [finitePartitionRelativeEntropy_eq_top_of_not_absolutelyContinuous P Q h,
    relativeEntropy_eq_top_of_not_absolutelyContinuous h]

end
end BanditRLProof.LowerBounds
