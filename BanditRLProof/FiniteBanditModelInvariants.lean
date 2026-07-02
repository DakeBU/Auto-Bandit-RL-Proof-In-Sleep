import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import BanditRLProof.Core

/-!
# Finite-bandit model invariants

This module contains model-semantic facts about the local
`FiniteBanditModel.bestArm` selector.  It stays below regret, expectation,
filtrations, kernels, and concentration.
-/

namespace BanditRLProof

namespace FiniteBanditModel

private theorem mean_le_foldl_select
    {K : Nat} (mean : Fin K -> Rat) (init : Fin K) :
    forall l : List (Fin K),
      (forall a : Fin K, a ∈ l ->
        mean a <=
          mean
            (l.foldl
              (fun best arm : Fin K =>
                if mean best < mean arm then arm else best)
              init)) /\
      mean init <=
        mean
          (l.foldl
            (fun best arm : Fin K =>
              if mean best < mean arm then arm else best)
            init)
  | [] => by
      simp
  | arm :: rest => by
      let select :=
        fun best arm : Fin K =>
          if mean best < mean arm then arm else best
      let next := select init arm
      have ih := mean_le_foldl_select (mean := mean) next rest
      have harm_next : mean arm <= mean next := by
        by_cases hlt : mean init < mean arm
        · simp [next, select, hlt]
        · simp [next, select, hlt, le_of_not_gt hlt]
      constructor
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with ha | ha
        · subst ha
          exact le_trans harm_next ih.2
        · exact ih.1 a ha
      · have hinit_next : mean init <= mean next := by
          by_cases hlt : mean init < mean arm
          · simpa [next, select, hlt] using le_of_lt hlt
          · simp [next, select, hlt]
        exact le_trans hinit_next ih.2

/--
The mean of every arm is at most the mean of the model's selected best arm.

This is the `FINITE-BANDIT-BESTARM-DOMINATES` model-invariant leaf.  It is a
semantic fact about the local finite-arm selector only; it does not prove gap
nonnegativity or any expectation/concentration statement.
-/
theorem mean_le_bestArm_mean
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.mean model.bestArm := by
  unfold bestArm
  exact
    (mean_le_foldl_select
      (mean := model.mean)
      (init := ⟨0, model.hK⟩)
      (List.finRange K)).1 a (List.mem_finRange a)

/--
Every local model gap is nonnegative.

This is the `FINITE-BANDIT-GAP-NONNEG` model-invariant leaf.  It consumes only
`FiniteBanditModel.mean_le_bestArm_mean` and the local `gap` definition; it does
not prove or use any expectation, filtration, or concentration statement.
-/
theorem gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a := by
  by_cases h : a = model.bestArm
  · simp [gap, h]
  · simp [gap, h, bestMean,
      sub_nonneg.mpr (mean_le_bestArm_mean model a)]

/--
The maximum local arm gap over the finite arm set.

This is a deterministic finite-model constant only. It does not introduce
probability, expectation, concentration, or algorithmic behavior.
-/
noncomputable def maxGap
    {K : Nat}
    (model : FiniteBanditModel K) : Rat := by
  classical
  refine Finset.sup'
    (s := (Finset.univ : Finset (Fin K))) ?_
    (fun a : Fin K => model.gap a)
  use model.bestArm
  exact Finset.mem_univ model.bestArm

/--
Every local model gap is bounded by `FiniteBanditModel.maxGap`.

This is the finite max-gap adapter used by sharper ETC suffix bounds.
-/
theorem gap_le_maxGap
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.gap a <= model.maxGap := by
  unfold maxGap
  exact Finset.le_sup' (f := fun a : Fin K => model.gap a)
    (Finset.mem_univ a)

/-- The finite maximum gap is nonnegative. -/
theorem maxGap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) :
    (0 : Rat) <= model.maxGap := by
  simpa [FiniteBanditModel.gap_bestArm] using
    (FiniteBanditModel.gap_le_maxGap model model.bestArm)

end FiniteBanditModel

end BanditRLProof
