import BanditRLProof.OnlineConvexUncountability

open BanditRL.OnlineConvex
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

namespace ConvexUncountabilityProbe

theorem segment_nonsmooth_intersection_not_countable :
    ¬ (segment ℝ (0 : Plane) (PiLp.single 2 1 1) ∩
      {x : Plane | ¬ DifferentiableAt ℝ coordinateAbsolute x}).Countable := by
  intro hc
  apply coordinate_segment_not_countable
  have hsub : segment ℝ (0 : Plane) (PiLp.single 2 1 1) ⊆
      segment ℝ (0 : Plane) (PiLp.single 2 1 1) ∩
        {x : Plane | ¬ DifferentiableAt ℝ coordinateAbsolute x} := by
    intro x hx
    exact ⟨hx, convex_nondifferentiable_segment.2 x hx⟩
  exact Set.Countable.mono hsub hc

theorem endpoint_pair_countable_and_distinct :
    ({(0 : Plane), PiLp.single 2 1 1} : Set Plane).Countable ∧
      (0 : Plane) ≠ PiLp.single 2 1 1 := by
  refine ⟨by simp, ?_⟩
  intro h
  have hc := congrArg (fun x : Plane => x 1) h
  norm_num at hc

theorem scalar_absolute_nonsmooth_locus_countable :
    ({x : ℝ | ¬ DifferentiableAt ℝ (fun t : ℝ => |t|) x}).Countable := by
  apply Set.Countable.mono (s₂ := {(0 : ℝ)}) _ (Set.countable_singleton 0)
  intro x hx
  change x = 0
  by_contra h
  exact hx (differentiableAt_id.abs h)

theorem countable_exception_set_misses_nonsmooth_point (S : Set Plane) (hS : S.Countable) :
    ∃ x : Plane, x ∉ S ∧ ¬ DifferentiableAt ℝ coordinateAbsolute x := by
  by_contra h
  have hsub : {x : Plane | ¬ DifferentiableAt ℝ coordinateAbsolute x} ⊆ S := by
    intro x hx
    by_contra hxS
    exact h ⟨x, hxS, hx⟩
  exact convex_uncountable_nondifferentiability.2 (Set.Countable.mono hsub hS)

end ConvexUncountabilityProbe
