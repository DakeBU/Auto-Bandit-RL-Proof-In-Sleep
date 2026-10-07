import BanditRLProof.OnlineConvexNondifferentiability

open BanditRL.OnlineConvex
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

namespace ConvexNondiffProbe

theorem closed_endpoints :
    ¬ DifferentiableAt ℝ coordinateAbsolute (0 : Plane) ∧
    ¬ DifferentiableAt ℝ coordinateAbsolute (PiLp.single 2 1 1 : Plane) := by
  exact ⟨convex_nondifferentiable_segment.2 _ (left_mem_segment ℝ _ _),
    convex_nondifferentiable_segment.2 _ (right_mem_segment ℝ _ _)⟩

theorem nonzero_midpoint :
    let p : Plane := PiLp.single 2 1 (1 / 2 : ℝ)
    p ∈ segment ℝ (0 : Plane) (PiLp.single 2 1 1) ∧
      p ≠ 0 ∧ ¬ DifferentiableAt ℝ coordinateAbsolute p := by
  dsimp only
  have hm : (PiLp.single 2 1 (1 / 2 : ℝ) : Plane) ∈
      segment ℝ (0 : Plane) (PiLp.single 2 1 1) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    fin_cases i <;> simp [PiLp.single_apply]
  refine ⟨hm, ?_, convex_nondifferentiable_segment.2 _ hm⟩
  intro h
  have hc := congrArg (fun q : Plane => q 1) h
  norm_num at hc

theorem axis_outside_segment :
    let p : Plane := PiLp.single 2 1 (2 : ℝ)
    p ∉ segment ℝ (0 : Plane) (PiLp.single 2 1 1) ∧
      ¬ DifferentiableAt ℝ coordinateAbsolute p := by
  dsimp only
  refine ⟨?_, coordinate_absolute_not_differentiable _ (by simp)⟩
  intro h
  rcases h with ⟨a, b, ha, _, hab, heq⟩
  have hc := congrArg (fun q : Plane => q 1) heq
  simp at hc
  linarith

theorem offaxis_positive_and_negative :
    DifferentiableAt ℝ coordinateAbsolute
      ((PiLp.single 2 0 1 + PiLp.single 2 1 2) : Plane) ∧
    DifferentiableAt ℝ coordinateAbsolute
      ((PiLp.single 2 0 (-1) + PiLp.single 2 1 2) : Plane) := by
  let A : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  have h (x : Plane) (hx : x 0 ≠ 0) : DifferentiableAt ℝ coordinateAbsolute x :=
    A.differentiableAt.abs hx
  exact ⟨h _ (by simp), h _ (by simp)⟩

theorem constant_vertical_restriction :
    (∀ t : ℝ, coordinateAbsolute (PiLp.single 2 1 t : Plane) = 0) ∧
    Differentiable ℝ (fun t : ℝ => coordinateAbsolute (PiLp.single 2 1 t : Plane)) := by
  refine ⟨fun t => by simp [coordinateAbsolute], ?_⟩
  simpa [coordinateAbsolute] using (differentiable_const (0 : ℝ))

end ConvexNondiffProbe
