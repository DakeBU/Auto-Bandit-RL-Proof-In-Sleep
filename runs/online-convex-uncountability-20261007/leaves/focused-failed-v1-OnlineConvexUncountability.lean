/-
Orabona arXiv1912.13213v10, printed19/PDF31, the unnumbered paragraph
after Theorem2.30 at end2.2.1 immediately before2.2.2. The same real-plane
convex example |x1| has uncountably many AMBIENT nondifferentiability points.
The already proved closed-segment obstruction supplies actual nonsmoothness;
this module supplies the separately required cardinality consequence.
No exact continuum cardinality, measure-zero theorem, chapter completion,
different function or within-segment derivative is asserted here.
-/
import BanditRLProof.OnlineConvexNondifferentiability
import Mathlib.Analysis.Real.Cardinality

namespace BanditRL.OnlineConvex

theorem coordinate_segment_not_countable :
    ¬ (segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1)).Countable := by
  intro hc
  let v : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => PiLp.single 2 1 t
  have hinj : Function.Injective v := by
    intro s t h
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    simpa [v] using he
  have hpre := hc.preimage hinj
  have hsub : Set.Icc (0 : ℝ) 1 ⊆
      v ⁻¹' segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1) := by
    intro t ht
    change PiLp.single 2 1 t ∈
      segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1)
    refine ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, ?_⟩
    ext i
    fin_cases i <;> simp [PiLp.single_apply]
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable := Set.Countable.mono hsub hpre
  have hfalse : (1 : ℝ) ≤ 0 := Cardinal.Real.Icc_countable_iff.mp hIcc
  norm_num at hfalse

theorem convex_uncountable_nondifferentiability :
    ConvexOn ℝ Set.univ coordinateAbsolute ∧
    ¬ ({x : EuclideanSpace ℝ (Fin 2) | ¬ DifferentiableAt ℝ coordinateAbsolute x}).Countable := by
  refine ⟨coordinate_absolute_convex, ?_⟩
  intro hc
  apply coordinate_segment_not_countable
  exact Set.Countable.mono (fun x hx => convex_nondifferentiable_segment.2 x hx) hc

end BanditRL.OnlineConvex
