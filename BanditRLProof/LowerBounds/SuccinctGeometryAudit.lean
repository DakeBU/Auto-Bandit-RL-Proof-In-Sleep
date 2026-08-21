import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Succinct-support geometry audit

This module formalizes the first geometric layer of Zeng--Honorio (NeurIPS
2025), Definitions 3.1--3.2 and Lemmas 3.1--3.2.  It keeps the atom set
possibly infinite and makes every boundedness premise for real `sSup`
explicit.

The final diagnostic records a source boundary rather than a source theorem:
if the atoms do not span the ambient inner-product space, the candidate set
defining the paper's globally real-valued `R` can be unbounded.  Later source
lemmas therefore remain outside this module until a spanning, extended-real,
or span/quotient repair is chosen explicitly.
-/

namespace BanditRLProof
namespace LowerBounds
namespace Succinct

open scoped BigOperators InnerProductSpace

noncomputable section

/-- Source Axiom 3.1: a nonempty collection of unit atoms closed under
negation.  No spanning assumption is added. -/
structure SuccinctUnitSystem (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] where
  atoms : Set V
  atoms_nonempty : atoms.Nonempty
  norm_eq_one : ∀ e ∈ atoms, ‖e‖ = 1
  neg_mem : ∀ e ∈ atoms, -e ∈ atoms

namespace SuccinctUnitSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The source quantity `Q(X)=sup_{E in U} <X,E>`. -/
def sourceQ (system : SuccinctUnitSystem V) (x : V) : ℝ :=
  sSup ((fun e : V => ⟪x, e⟫_ℝ) '' system.atoms)

theorem sourceQSet_bddAbove (system : SuccinctUnitSystem V) (x : V) :
    BddAbove ((fun e : V => ⟪x, e⟫_ℝ) '' system.atoms) := by
  refine ⟨‖x‖, ?_⟩
  rintro value ⟨e, he, rfl⟩
  calc
    ⟪x, e⟫_ℝ ≤ |⟪x, e⟫_ℝ| := le_abs_self _
    _ ≤ ‖x‖ * ‖e‖ := abs_real_inner_le_norm x e
    _ = ‖x‖ := by rw [system.norm_eq_one e he, mul_one]

theorem le_sourceQ_of_mem (system : SuccinctUnitSystem V)
    {x e : V} (he : e ∈ system.atoms) :
    ⟪x, e⟫_ℝ ≤ system.sourceQ x := by
  exact le_csSup (system.sourceQSet_bddAbove x) ⟨e, he, rfl⟩

theorem sourceQ_le_norm (system : SuccinctUnitSystem V) (x : V) :
    system.sourceQ x ≤ ‖x‖ := by
  apply csSup_le
  · exact system.atoms_nonempty.image _
  · rintro value ⟨e, he, rfl⟩
    calc
      ⟪x, e⟫_ℝ ≤ |⟪x, e⟫_ℝ| := le_abs_self _
      _ ≤ ‖x‖ * ‖e‖ := abs_real_inner_le_norm x e
      _ = ‖x‖ := by rw [system.norm_eq_one e he, mul_one]

theorem sourceQ_nonneg (system : SuccinctUnitSystem V) (x : V) :
    0 ≤ system.sourceQ x := by
  rcases system.atoms_nonempty with ⟨e, he⟩
  by_cases hinner : 0 ≤ ⟪x, e⟫_ℝ
  · exact hinner.trans (system.le_sourceQ_of_mem he)
  · have hneg : 0 ≤ ⟪x, -e⟫_ℝ := by
      rw [inner_neg_right]
      exact neg_nonneg.mpr (le_of_not_ge hinner)
    exact hneg.trans (system.le_sourceQ_of_mem (system.neg_mem e he))

@[simp]
theorem sourceQ_zero (system : SuccinctUnitSystem V) : system.sourceQ 0 = 0 := by
  apply le_antisymm
  · simpa using system.sourceQ_le_norm 0
  · exact system.sourceQ_nonneg 0

theorem abs_inner_le_sourceQ_of_mem (system : SuccinctUnitSystem V)
    {x e : V} (he : e ∈ system.atoms) :
    |⟪x, e⟫_ℝ| ≤ system.sourceQ x := by
  apply abs_le.mpr
  constructor
  · have hneg : -⟪x, e⟫_ℝ ≤ system.sourceQ x := by
      simpa using system.le_sourceQ_of_mem (x := x) (system.neg_mem e he)
    linarith
  · exact system.le_sourceQ_of_mem he

theorem sourceQ_eq_zero_of_atom_orthogonal (system : SuccinctUnitSystem V)
    {x : V} (horthogonal : ∀ e ∈ system.atoms, ⟪x, e⟫_ℝ = 0) :
    system.sourceQ x = 0 := by
  apply le_antisymm
  · apply csSup_le
    · exact system.atoms_nonempty.image _
    · rintro value ⟨e, he, rfl⟩
      exact le_of_eq (horthogonal e he)
  · exact system.sourceQ_nonneg x

/-- The source quantity `R(X)=sup_{Q(Y)<=1} <X,Y>`, retained as a real-valued
`sSup`.  Consumers must separately prove the defining set is bounded. -/
def sourceR (system : SuccinctUnitSystem V) (x : V) : ℝ :=
  sSup ((fun y : V => ⟪x, y⟫_ℝ) '' {y | system.sourceQ y ≤ 1})

/-- If a nonzero ambient direction is orthogonal to every atom, the set used
to define its source `R` is unbounded.  This exposes the hidden global
regularity/codomain obligation in Definition 3.2. -/
theorem sourceRSet_not_bddAbove_of_nonzero_atom_orthogonal
    (system : SuccinctUnitSystem V) {x : V} (hx : x ≠ 0)
    (horthogonal : ∀ e ∈ system.atoms, ⟪x, e⟫_ℝ = 0) :
    ¬ BddAbove ((fun y : V => ⟪x, y⟫_ℝ) '' {y | system.sourceQ y ≤ 1}) := by
  intro hbounded
  rcases hbounded with ⟨bound, hbound⟩
  have hself : 0 < ⟪x, x⟫_ℝ := real_inner_self_pos.mpr hx
  let scale : ℝ := (bound + 1) / ⟪x, x⟫_ℝ
  let y : V := scale • x
  have hqy : system.sourceQ y = 0 := by
    apply system.sourceQ_eq_zero_of_atom_orthogonal
    intro e he
    simp [y, inner_smul_left, horthogonal e he]
  have hy : y ∈ {z | system.sourceQ z ≤ 1} := by
    simp [hqy]
  have hvalue : ⟪x, y⟫_ℝ ≤ bound := hbound ⟨y, hy, rfl⟩
  have hinner : ⟪x, y⟫_ℝ = bound + 1 := by
    change ⟪x, scale • x⟫_ℝ = bound + 1
    rw [inner_smul_right]
    dsimp [scale]
    field_simp
  linarith

/-- Source Definition 3.1.  The explicit boundedness field is the ordinary
mathematical meaning of the displayed finite real supremum, not a replacement
for the source equality. -/
structure IsSuccinctSupport (system : SuccinctUnitSystem V) {s : Nat}
    (basis : Fin s → V) : Prop where
  mem_atoms : ∀ i, basis i ∈ system.atoms
  correlation_bddAbove :
    BddAbove ((fun e : V => ∑ i, |⟪e, basis i⟫_ℝ|) '' system.atoms)
  correlation_sSup_eq_one :
    sSup ((fun e : V => ∑ i, |⟪e, basis i⟫_ℝ|) '' system.atoms) = 1

namespace IsSuccinctSupport

variable {system : SuccinctUnitSystem V} {s : Nat} {basis : Fin s → V}

theorem correlationSum_le_one (support : IsSuccinctSupport system basis)
    {e : V} (he : e ∈ system.atoms) :
    (∑ i, |⟪e, basis i⟫_ℝ|) ≤ 1 := by
  have hle :
      (∑ i, |⟪e, basis i⟫_ℝ|) ≤
        sSup ((fun z : V => ∑ i, |⟪z, basis i⟫_ℝ|) '' system.atoms) :=
    le_csSup support.correlation_bddAbove ⟨e, he, rfl⟩
  simpa [support.correlation_sSup_eq_one] using hle

/-- The mutual-orthogonality consequence stated after source Definition 3.1. -/
theorem inner_basis_basis (support : IsSuccinctSupport system basis)
    (i j : Fin s) :
    ⟪basis i, basis j⟫_ℝ = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, real_inner_self_eq_norm_sq,
      system.norm_eq_one (basis i) (support.mem_atoms i)]
    norm_num
  · rw [if_neg hij]
    have hsum := support.correlationSum_le_one (support.mem_atoms i)
    have hdiag : |⟪basis i, basis i⟫_ℝ| = 1 := by
      rw [real_inner_self_eq_norm_sq,
        system.norm_eq_one (basis i) (support.mem_atoms i)]
      norm_num
    have herase_nonneg :
        0 ≤ ∑ k ∈ (Finset.univ : Finset (Fin s)).erase i,
          |⟪basis i, basis k⟫_ℝ| := by positivity
    have herase_add := Finset.sum_erase_add (Finset.univ : Finset (Fin s))
      (fun k => |⟪basis i, basis k⟫_ℝ|) (Finset.mem_univ i)
    have herase_zero :
        (∑ k ∈ (Finset.univ : Finset (Fin s)).erase i,
          |⟪basis i, basis k⟫_ℝ|) = 0 := by
      change
        (∑ k ∈ (Finset.univ : Finset (Fin s)).erase i,
          |⟪basis i, basis k⟫_ℝ|) + |⟪basis i, basis i⟫_ℝ| =
            ∑ k, |⟪basis i, basis k⟫_ℝ| at herase_add
      rw [hdiag] at herase_add
      linarith
    have hjmem : j ∈ (Finset.univ : Finset (Fin s)).erase i := by
      simp [Ne.symm hij]
    have hjzero : |⟪basis i, basis j⟫_ℝ| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _hk => abs_nonneg ⟪basis i, basis k⟫_ℝ)).mp herase_zero j hjmem
    exact abs_eq_zero.mp hjzero

/-- The finite maximum appearing in source Lemma 3.1. -/
def maxAbsCoefficient [Nonempty (Fin s)] (a : Fin s → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin s)).sup' Finset.univ_nonempty (fun i => |a i|)

theorem abs_le_maxAbsCoefficient [Nonempty (Fin s)] (a : Fin s → ℝ) (i : Fin s) :
    |a i| ≤ maxAbsCoefficient a := by
  exact Finset.le_sup' (fun j => |a j|) (Finset.mem_univ i)

theorem maxAbsCoefficient_nonneg [Nonempty (Fin s)] (a : Fin s → ℝ) :
    0 ≤ maxAbsCoefficient a := by
  let i : Fin s := Classical.choice inferInstance
  exact (abs_nonneg (a i)).trans (abs_le_maxAbsCoefficient a i)

theorem exists_abs_eq_maxAbsCoefficient [Nonempty (Fin s)] (a : Fin s → ℝ) :
    ∃ i : Fin s, |a i| = maxAbsCoefficient a := by
  rcases Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin s)).Nonempty) (fun i => |a i|) with
    ⟨i, _hi, hmax⟩
  exact ⟨i, hmax.symm⟩

def supportCombination (basis : Fin s → V) (a : Fin s → ℝ) : V :=
  ∑ i, a i • basis i

def signedSupportAtom (coefficient : ℝ) (atom : V) : V :=
  if 0 ≤ coefficient then atom else -atom

theorem signedSupportAtom_mem (support : IsSuccinctSupport system basis)
    (a : Fin s → ℝ) (i : Fin s) :
    signedSupportAtom (a i) (basis i) ∈ system.atoms := by
  by_cases h : 0 ≤ a i
  · simpa [signedSupportAtom, h] using support.mem_atoms i
  · simpa [signedSupportAtom, h] using system.neg_mem (basis i) (support.mem_atoms i)

theorem sourceQ_supportCombination_le [Nonempty (Fin s)]
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) :
    system.sourceQ (supportCombination basis a) ≤ maxAbsCoefficient a := by
  apply csSup_le
  · exact system.atoms_nonempty.image _
  · rintro value ⟨e, he, rfl⟩
    calc
      ⟪supportCombination basis a, e⟫_ℝ ≤
          |⟪supportCombination basis a, e⟫_ℝ| := le_abs_self _
      _ = |∑ i, a i * ⟪basis i, e⟫_ℝ| := by
        simp [supportCombination, sum_inner, inner_smul_left]
      _ ≤ ∑ i, |a i * ⟪basis i, e⟫_ℝ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |a i| * |⟪e, basis i⟫_ℝ| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul, real_inner_comm]
      _ ≤ ∑ i, maxAbsCoefficient a * |⟪e, basis i⟫_ℝ| := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_right (abs_le_maxAbsCoefficient a i) (abs_nonneg _)
      _ = maxAbsCoefficient a * ∑ i, |⟪e, basis i⟫_ℝ| := by
        rw [Finset.mul_sum]
      _ ≤ maxAbsCoefficient a * 1 :=
        mul_le_mul_of_nonneg_left (support.correlationSum_le_one he)
          (maxAbsCoefficient_nonneg a)
      _ = maxAbsCoefficient a := mul_one _

theorem inner_supportCombination_basis
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) (m : Fin s) :
    ⟪supportCombination basis a, basis m⟫_ℝ = a m := by
  rw [supportCombination, sum_inner]
  calc
    (∑ i, ⟪a i • basis i, basis m⟫_ℝ) =
        ∑ i, a i * (if i = m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [inner_smul_left, support.inner_basis_basis]
      simp
    _ = a m := by simp

theorem inner_supportCombination_signedSupportAtom
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) (m : Fin s) :
    ⟪supportCombination basis a, signedSupportAtom (a m) (basis m)⟫_ℝ = |a m| := by
  by_cases h : 0 ≤ a m
  · rw [signedSupportAtom, if_pos h, support.inner_supportCombination_basis,
      abs_of_nonneg h]
  · have hneg : a m < 0 := lt_of_not_ge h
    rw [signedSupportAtom, if_neg h, inner_neg_right,
      support.inner_supportCombination_basis, abs_of_neg hneg]

/-- Source Lemma 3.1: `Q` is the coefficient maximum on a succinct support. -/
theorem sourceQ_supportCombination_eq [Nonempty (Fin s)]
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) :
    system.sourceQ (supportCombination basis a) = maxAbsCoefficient a := by
  apply le_antisymm (support.sourceQ_supportCombination_le a)
  rcases exists_abs_eq_maxAbsCoefficient a with ⟨m, hm⟩
  calc
    maxAbsCoefficient a = |a m| := hm.symm
    _ = ⟪supportCombination basis a,
        signedSupportAtom (a m) (basis m)⟫_ℝ :=
      (support.inner_supportCombination_signedSupportAtom a m).symm
    _ ≤ system.sourceQ (supportCombination basis a) :=
      system.le_sourceQ_of_mem (support.signedSupportAtom_mem a m)

def coefficientSign (coefficient : ℝ) : ℝ :=
  if 0 ≤ coefficient then 1 else -1

@[simp]
theorem abs_coefficientSign (coefficient : ℝ) : |coefficientSign coefficient| = 1 := by
  by_cases h : 0 ≤ coefficient <;> simp [coefficientSign, h]

theorem coefficientSign_mul (coefficient : ℝ) :
    coefficientSign coefficient * coefficient = |coefficient| := by
  by_cases h : 0 ≤ coefficient
  · simp [coefficientSign, h, abs_of_nonneg h]
  · have hneg : coefficient < 0 := lt_of_not_ge h
    simp [coefficientSign, h, abs_of_neg hneg]

def supportSignCombination (basis : Fin s → V) (a : Fin s → ℝ) : V :=
  supportCombination basis (fun i => coefficientSign (a i))

theorem maxAbsCoefficient_coefficientSign [Nonempty (Fin s)] (a : Fin s → ℝ) :
    maxAbsCoefficient (fun i => coefficientSign (a i)) = 1 := by
  simp [maxAbsCoefficient]

theorem sourceQ_supportSignCombination [Nonempty (Fin s)]
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) :
    system.sourceQ (supportSignCombination basis a) = 1 := by
  rw [supportSignCombination, support.sourceQ_supportCombination_eq,
    maxAbsCoefficient_coefficientSign]

theorem inner_supportCombination_supportSignCombination
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) :
    ⟪supportCombination basis a, supportSignCombination basis a⟫_ℝ =
      ∑ i, |a i| := by
  simp only [supportSignCombination, supportCombination]
  rw [inner_sum]
  calc
    (∑ i, ⟪∑ j, a j • basis j, coefficientSign (a i) • basis i⟫_ℝ) =
        ∑ i, coefficientSign (a i) * a i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [inner_smul_right]
      exact congrArg (fun value => coefficientSign (a i) * value)
        (support.inner_supportCombination_basis a i)
    _ = ∑ i, |a i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact coefficientSign_mul (a i)

theorem inner_supportCombination_le_sumAbs_mul_sourceQ
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) (y : V) :
    |⟪supportCombination basis a, y⟫_ℝ| ≤
      (∑ i, |a i|) * system.sourceQ y := by
  calc
    |⟪supportCombination basis a, y⟫_ℝ| =
        |∑ i, a i * ⟪basis i, y⟫_ℝ| := by
      simp [supportCombination, sum_inner, inner_smul_left]
    _ ≤ ∑ i, |a i * ⟪basis i, y⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |⟪y, basis i⟫_ℝ| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, real_inner_comm]
    _ ≤ ∑ i, |a i| * system.sourceQ y := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (system.abs_inner_le_sourceQ_of_mem (support.mem_atoms i)) (abs_nonneg _)
    _ = (∑ i, |a i|) * system.sourceQ y := by
      rw [Finset.sum_mul]

theorem inner_supportCombination_le_sumAbs_of_sourceQ_le_one
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) {y : V}
    (hy : system.sourceQ y ≤ 1) :
    ⟪supportCombination basis a, y⟫_ℝ ≤ ∑ i, |a i| := by
  calc
    ⟪supportCombination basis a, y⟫_ℝ ≤
        |⟪supportCombination basis a, y⟫_ℝ| := le_abs_self _
    _ ≤ (∑ i, |a i|) * system.sourceQ y :=
      support.inner_supportCombination_le_sumAbs_mul_sourceQ a y
    _ ≤ (∑ i, |a i|) * 1 :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = ∑ i, |a i| := mul_one _

theorem sourceRSet_bddAbove
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) :
    BddAbove ((fun y : V => ⟪supportCombination basis a, y⟫_ℝ) ''
      {y | system.sourceQ y ≤ 1}) := by
  refine ⟨∑ i, |a i|, ?_⟩
  rintro value ⟨y, hy, rfl⟩
  exact support.inner_supportCombination_le_sumAbs_of_sourceQ_le_one a hy

/-- Source Lemma 3.2 for a succinct vector.  The proof also supplies the
boundedness evidence missing from a bare use of real `sSup`. -/
theorem sourceR_supportCombination_eq [Nonempty (Fin s)]
    (support : IsSuccinctSupport system basis) (a : Fin s → ℝ) :
    system.sourceR (supportCombination basis a) = ∑ i, |a i| := by
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ?_⟩
      exact ⟨0, by simp, by simp⟩
    · rintro value ⟨y, hy, rfl⟩
      exact support.inner_supportCombination_le_sumAbs_of_sourceQ_le_one a hy
  · have hwitness : supportSignCombination basis a ∈
        {y | system.sourceQ y ≤ 1} := by
      simp [support.sourceQ_supportSignCombination a]
    calc
      (∑ i, |a i|) =
          ⟪supportCombination basis a, supportSignCombination basis a⟫_ℝ :=
        (support.inner_supportCombination_supportSignCombination a).symm
      _ ≤ system.sourceR (supportCombination basis a) :=
        le_csSup (support.sourceRSet_bddAbove a)
          ⟨supportSignCombination basis a, hwitness, rfl⟩

end IsSuccinctSupport
end SuccinctUnitSystem

end
end Succinct
end LowerBounds
end BanditRLProof
