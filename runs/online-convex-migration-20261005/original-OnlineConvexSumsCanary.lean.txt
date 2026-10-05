import BanditRLProof

noncomputable section
open Set BanditRL.OnlineConvex
namespace Tests.OnlineConvexSums

def spike (c x : ℝ) : EReal := if x = c then ⊥ else ⊤

theorem spike_convex (c : ℝ) : IsConvexExtended (spike c) := by
  have he : realEpigraph (spike c) = {c} ×ˢ (univ : Set ℝ) := by
    ext p
    by_cases hp : p.1 = c <;> simp [realEpigraph, spike, hp]
  change Convex ℝ (realEpigraph (spike c))
  rw [he]
  exact (convex_singleton c).prod convex_univ

theorem naive_sum_not_convex : ¬ IsConvexExtended (fun x => spike 0 x + spike 2 x) := by
  intro hc
  have hx : (0, 0) ∈ realEpigraph (fun x => spike 0 x + spike 2 x) := by
    norm_num [realEpigraph, spike]
  have hy : (2, 0) ∈ realEpigraph (fun x => spike 0 x + spike 2 x) := by
    norm_num [realEpigraph, spike]
  have hm : (1, 0) ∈ realEpigraph (fun x => spike 0 x + spike 2 x) := by
    convert hc hx hy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  norm_num [realEpigraph, spike] at hm

theorem upper_spikes_convex : IsConvexExtended (fun x => upperAdd (spike 0 x) (spike 2 x)) :=
  convex_upperAdd _ _ (spike_convex 0) (spike_convex 2)

theorem mixed_infinity_values : upperAdd (spike 0 0) (spike 2 0) = ⊤ ∧
    spike 0 0 + spike 2 0 = ⊥ ∧ upperAdd (spike 0 1) (spike 2 1) = ⊤ := by
  norm_num [spike, upperAdd]

example : IsConvexExtended (fun x => upperAdd ((0 : EReal) * spike 0 x) ((0 : EReal) * spike 2 x)) :=
  convex_nonneg_linear_combination _ _ (spike_convex 0) (spike_convex 2) 0 0 (by norm_num) (by norm_num)

example (x : ℝ) : upperAdd ((0 : EReal) * spike 0 x) ((0 : EReal) * spike 2 x) = 0 := by
  simp [upperAdd]

theorem positive_combination : IsConvexExtended (fun x : ℝ =>
    upperAdd (((2 : ℝ) : EReal) * ((‖x‖ : ℝ) : EReal))
      (((3 : ℝ) : EReal) * ((‖x‖ : ℝ) : EReal))) :=
  convex_nonneg_linear_combination _ _ (example_2_6 (E := ℝ)) (example_2_6 (E := ℝ))
    2 3 (by norm_num) (by norm_num)

example : upperAdd (((2 : ℝ) : EReal) * ((‖(2 : ℝ)‖ : ℝ) : EReal))
    (((3 : ℝ) : EReal) * ((‖(2 : ℝ)‖ : ℝ) : EReal)) = ((10 : ℝ) : EReal) := by
  rw [← EReal.coe_mul, ← EReal.coe_mul, upperAdd_coe]
  norm_num

#print axioms BanditRL.OnlineConvex.upperAdd_coe
#print axioms BanditRL.OnlineConvex.upperAdd_top
#print axioms BanditRL.OnlineConvex.top_upperAdd
#print axioms BanditRL.OnlineConvex.upperAdd_le_coe_iff
#print axioms BanditRL.OnlineConvex.convex_upperAdd
#print axioms BanditRL.OnlineConvex.positive_mul_le_coe_iff
#print axioms BanditRL.OnlineConvex.convex_nonneg_mul
#print axioms BanditRL.OnlineConvex.convex_nonneg_linear_combination
#print axioms naive_sum_not_convex
#print axioms upper_spikes_convex
#print axioms positive_combination
end Tests.OnlineConvexSums
