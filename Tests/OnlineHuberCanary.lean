import BanditRLProof

namespace HuberSeamProbe
lemma upper_join : HasDerivAt (fun x : ℝ => if x ≤ 1 then x^2/2 else x-1/2) 1 1 := by
  apply BanditRL.OnlineHuber.hasDerivAt_ite_le
  · simpa using (((hasDerivAt_id (1:ℝ)).pow 2).div_const 2)
  · exact (hasDerivAt_id (1:ℝ)).sub_const (1/2)
  · norm_num
#print axioms upper_join
#print axioms BanditRL.OnlineHuber.hasDerivAt_ite_le
end HuberSeamProbe

namespace HuberDerivativeProbe
open BanditRL.OnlineHuber
theorem lower_seam : HasDerivAt (huber 2) (-2) (-2) := by
  convert huber_hasDerivAt 2 (-2) (by norm_num) using 1 <;> norm_num
theorem upper_seam : HasDerivAt (huber 2) 2 2 := by
  convert huber_hasDerivAt 2 2 (by norm_num) using 1 <;> norm_num
theorem zero_threshold : HasDerivAt (huber 0) 0 (-7) := by
  convert huber_hasDerivAt 0 (-7) (by norm_num) using 1 <;> norm_num
theorem quadratic_interior : HasDerivAt (huber 2) 1 1 := by
  convert huber_hasDerivAt 2 1 (by norm_num) using 1 <;> norm_num
theorem affine_exterior : HasDerivAt (huber 2) 2 3 := by
  convert huber_hasDerivAt 2 3 (by norm_num) using 1 <;> norm_num
#print axioms BanditRL.OnlineHuber.hasDerivAt_join
#print axioms BanditRL.OnlineHuber.huber_hasDerivAt
#print axioms lower_seam
#print axioms upper_seam
#print axioms zero_threshold
#print axioms quadratic_interior
#print axioms affine_exterior
end HuberDerivativeProbe

namespace HuberVectorProbe
open BanditRL.OnlineHuber
theorem nonzero_feature : gradient (fun w : ℝ => huber 2 (inner ℝ 3 w - 1)) 2 = 6 := by
  rw [(huber_linear_hasGradientAt 2 1 (by norm_num) (3 : ℝ) 2).gradient,
    huber_deriv_clamp 2 _ (by norm_num)]
  change max (-2 : ℝ) (min (2 * 3 - 1) 2) * 3 = 6
  norm_num
theorem zero_threshold : gradient (fun w : ℝ => huber 0 (inner ℝ 3 w - 1)) 2 = 0 := by
  rw [(huber_linear_hasGradientAt 0 1 (by norm_num) (3 : ℝ) 2).gradient,
    huber_deriv_clamp 0 _ (by norm_num)]
  norm_num [RCLike.inner_apply]
theorem feature_bound : ‖gradient (fun w : ℝ => huber 2 (inner ℝ 3 w - 1)) 2‖ ≤ 6 := by
  have h := huber_linear_gradient_bound 2 1 (by norm_num) (3 : ℝ) 2
  norm_num at h ⊢
  exact h
theorem global_convex : ConvexOn ℝ Set.univ (fun w : ℝ => huber 2 (inner ℝ 3 w - 1)) :=
  huber_linear_convex 2 1 (by norm_num) 3
#print axioms BanditRL.OnlineHuber.huber_deriv_clamp
#print axioms BanditRL.OnlineHuber.huber_convex
#print axioms BanditRL.OnlineHuber.huber_deriv_bound
#print axioms BanditRL.OnlineHuber.huber_deriv_source
#print axioms BanditRL.OnlineHuber.huber_linear_hasGradientAt
#print axioms BanditRL.OnlineHuber.huber_linear_convex
#print axioms BanditRL.OnlineHuber.huber_linear_gradient_bound
#print axioms nonzero_feature
#print axioms zero_threshold
#print axioms feature_bound
#print axioms global_convex
end HuberVectorProbe

namespace HuberOGDProbe
open BanditRL.OnlineHuber BanditRL.OnlineGradientDescent
theorem actual_step : step (fullSpace : Domain ℝ) (1/2) (linearLoss 1 (1 : ℝ) 0) 2 = 3/2 := by
  rw [huber_step 1 0 (1/2) (by norm_num) (1 : ℝ) 2]
  have hi : inner ℝ (1 : ℝ) (2 : ℝ) = 2 := by change (2 : ℝ) * 1 = 2; ring
  norm_num [hi, smul_eq_mul, Real.sign]
theorem residual_bound (T : ℕ) :
    regret fullSpace (1/2) (fun _ => linearLoss 1 (1 : ℝ) 0) 2 0 T ≤
      ‖(2 : ℝ) - 0‖ ^ 2 / (2 * (1/2)) + (1/2) / 2 * ((T : ℝ) * (1 * 1) ^ 2) -
      ‖iterate fullSpace (1/2) (fun _ => linearLoss 1 (1 : ℝ) 0) 2 T - 0‖ ^ 2 / (2*(1/2)) := by
  exact huber_regret_fixed 1 1 (1/2) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) (fun _ => 0) 2 0 T (by intro t ht; norm_num)
#print axioms BanditRL.OnlineHuber.project_fullSpace
#print axioms BanditRL.OnlineHuber.huber_regular
#print axioms BanditRL.OnlineHuber.huber_step
#print axioms BanditRL.OnlineHuber.huber_regret_fixed
#print axioms actual_step
#print axioms residual_bound
end HuberOGDProbe


namespace Tests.OnlineHuber
open BanditRL.OnlineHuber BanditRL.OnlineGradientDescent
theorem average_four :
    regret fullSpace (1 / Real.sqrt 4) (fun _ => linearLoss 1 (1 : ℝ) 0) 2 0 4 / 4 ≤ 5/4 := by
  have h := huber_average_bound 1 1 (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) (fun _ => 0) 2 0 4 (by norm_num) (by intro t ht; norm_num)
  norm_num at h ⊢
  exact h
theorem eventually_tenth : ∀ᶠ T : ℕ in Filter.atTop,
    regret fullSpace (1 / Real.sqrt T) (fun _ => linearLoss 1 (1 : ℝ) 0) 2 0 T / T < 1/10 :=
  huber_average_eventually 1 1 (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) (fun _ => 0) 2 0 (by intro t; norm_num) (1/10) (by norm_num)
#print axioms BanditRL.OnlineHuber.huber_three_pieces
#print axioms BanditRL.OnlineHuber.huber_zero
#print axioms BanditRL.OnlineHuber.huber_average_bound
#print axioms BanditRL.OnlineHuber.huber_rate_tendsto
#print axioms BanditRL.OnlineHuber.huber_average_eventually
#print axioms average_four
#print axioms eventually_tenth
end Tests.OnlineHuber
