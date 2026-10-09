import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineNonsmoothExamplesCanary
open scoped InnerProductSpace
open Tests.OnlineGradientDescentSource

example :
    ConvexOn ℝ Set.univ (fun w : ℝ => |w - 10|) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 10 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 9 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 11 :=
  Tests.OnlineNonsmoothExamples.source_shift_ten

#check @Tests.OnlineNonsmoothExamples.source_shift_ten
#print axioms Tests.OnlineNonsmoothExamples.source_shift_ten

example :
    ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) (1 / 6) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) (-1 / 6) ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) 0 ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) 0 ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) :=
  Tests.OnlineNonsmoothExamples.positive_negative_labels

#check @Tests.OnlineNonsmoothExamples.positive_negative_labels
#print axioms Tests.OnlineNonsmoothExamples.positive_negative_labels

example (y z : ℝ) :
    Differentiable ℝ (fun w : ℝ => max (1 - 0 * inner ℝ z w) 0) ∧
      Differentiable ℝ (fun w : ℝ => max (1 - y * inner ℝ (0 : ℝ) w) 0) ∧
      ∀ w : ℝ, max (1 - 0 * inner ℝ z w) 0 = 1 ∧
        max (1 - y * inner ℝ (0 : ℝ) w) 0 = 1 :=
  Tests.OnlineNonsmoothExamples.zero_label_and_feature y z

#check @Tests.OnlineNonsmoothExamples.zero_label_and_feature
#print axioms Tests.OnlineNonsmoothExamples.zero_label_and_feature

example :
    ¬ DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0)
        (e0 + (3 : ℝ) • e1) ∧
      DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0) e1 ∧
      DifferentiableAt ℝ (fun t : ℝ => max (1 - inner ℝ e0 (e0 + (3 + t) • e1)) 0) 0 :=
  Tests.OnlineNonsmoothExamples.plane_ambient_and_tangential

#check @Tests.OnlineNonsmoothExamples.plane_ambient_and_tangential
#print axioms Tests.OnlineNonsmoothExamples.plane_ambient_and_tangential

example (y : ℝ) (z : EuclideanSpace ℝ (Fin 0)) :
    Differentiable ℝ
        (fun w : EuclideanSpace ℝ (Fin 0) => max (1 - y * inner ℝ z w) 0) ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), max (1 - y * inner ℝ z w) 0 = 1 :=
  Tests.OnlineNonsmoothExamples.dimension_zero y z

#check @Tests.OnlineNonsmoothExamples.dimension_zero
#print axioms Tests.OnlineNonsmoothExamples.dimension_zero
