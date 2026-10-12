/-
Orabona arXiv1912.13213v10, unnumbered paragraph after Theorem 2.30,
printed 19 / PDF 31, immediately before Section 2.2.2.
The fixed function f(x)=|x₁| is real-valued on all of the real Euclidean plane. Lean uses EuclideanSpace ℝ (Fin 2), with source x₁ represented by index 0. DifferentiableAt means the ambient real Fréchet derivative. The segment joins (0,0) to (0,1) and includes both endpoints. Countable means at most countable. Convexity, derivative failure and uncountability are conclusions proved by the library, not supplied premises.
Orabona states the convex example and its failure of differentiability along the segment without a proof. The three missing derivations—convexity, ambient nondifferentiability and the uncountability bridge—are supplied here by the library, not attributed to a printed argument. The helper proving failure on the entire vertical axis is explicitly stronger than the stated segment example.
This bounded example does not complete Chapter 2 or the book. Exact nonsmooth-locus equality, exact continuum cardinality and a general almost-everywhere differentiability theorem are outside this package.
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
    fin_cases i <;> simp
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
