import BanditRLProof

noncomputable section
open Set
open BanditRL.OnlineConvex

namespace Tests.OnlineConvexExtended

def restrictedLinear (x : ℝ) : EReal := if 0 ≤ x then (x : EReal) else ⊤

lemma domain_linear : effectiveDomain restrictedLinear = Ici (0 : ℝ) := by
  ext x
  by_cases hx : 0 ≤ x <;> simp [effectiveDomain, restrictedLinear, hx]

lemma no_bot_linear (x : ℝ) : restrictedLinear x ≠ ⊥ := by
  simp only [restrictedLinear]
  split_ifs <;> simp

/-- Invoke the extended-real characterization, not a real-valued replacement. -/
lemma convex_linear : IsConvexExtended restrictedLinear := by
  apply (theorem_2_4 restrictedLinear no_bot_linear
    (by rw [domain_linear]; exact convex_Ici 0)).mpr
  intro x hx y hy θ hθ hθ1
  rw [domain_linear] at hx hy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hz : 0 ≤ θ * x + (1 - θ) * y :=
    add_nonneg (mul_nonneg hθ.le hx) (mul_nonneg (sub_nonneg.mpr hθ1.le) hy)
  simp only [smul_eq_mul, restrictedLinear, if_pos hx, if_pos hy, if_pos hz,
    ← EReal.coe_mul, ← EReal.coe_add]
  exact le_rfl

/-- Two distinct finite values, positive infinity outside the domain, and a meaningful height test. -/
theorem nondegenerate : restrictedLinear (-1) = ⊤ ∧
    restrictedLinear 0 = 0 ∧ restrictedLinear 2 = ((2 : ℝ) : EReal) ∧
    (1, 1) ∈ realEpigraph restrictedLinear ∧ (1, 0) ∉ realEpigraph restrictedLinear := by
  norm_num [restrictedLinear, realEpigraph]

example : restrictedLinear ((1 / 2 : ℝ) • (0 : ℝ) + (1 - 1 / 2 : ℝ) • 2) ≤
    ((1 / 2 : ℝ) : EReal) * restrictedLinear 0 +
      ((1 - 1 / 2 : ℝ) : EReal) * restrictedLinear 2 := by
  exact (theorem_2_4 restrictedLinear no_bot_linear
    (by rw [domain_linear]; exact convex_Ici 0)).mp convex_linear
    0 (by rw [domain_linear]; norm_num) 2 (by rw [domain_linear]; norm_num)
    (1 / 2) (by norm_num) (by norm_num)

/-- Definition2.3 and domain convexity include bottom; noBot is specific to Theorem2.4. -/
example : IsConvexExtended (fun _ : ℝ => (⊥ : EReal)) := by
  simpa [IsConvexExtended, realEpigraph] using
    (convex_univ : Convex ℝ (Set.univ : Set (ℝ × ℝ)))

example : effectiveDomain (fun _ : ℝ => (⊥ : EReal)) = Set.univ := by
  ext x
  simp [effectiveDomain]

example : IsConvexExtended (extendedIndicator (∅ : Set ℝ)) :=
  (convex_indicator_iff _).mpr convex_empty

example : IsConvexExtended
    (fun x : ℝ => restrictedLinear x + extendedIndicator (Icc (0 : ℝ) 1) x) :=
  convex_add_indicator restrictedLinear no_bot_linear convex_linear _ (convex_Icc 0 1)

example : restrictedLinear 2 + extendedIndicator (Icc (0 : ℝ) 1) 2 = ⊤ := by
  norm_num [extendedIndicator, restrictedLinear, EReal.coe_add_top]

example : IsConvexExtended (fun _ : ℝ => (⊤ : EReal)) := by
  apply (theorem_2_4 (fun _ : ℝ => (⊤ : EReal)) (by intro x; simp)
    (by simpa [effectiveDomain] using (convex_empty : Convex ℝ (∅ : Set ℝ)))).mpr
  intro x hx
  simp [effectiveDomain] at hx

#print axioms BanditRL.OnlineConvex.definition_2_2
#print axioms BanditRL.OnlineConvex.convex_effectiveDomain
#print axioms BanditRL.OnlineConvex.effectiveDomain_indicator
#print axioms BanditRL.OnlineConvex.convex_indicator_iff
#print axioms BanditRL.OnlineConvex.realEpigraph_toReal
#print axioms BanditRL.OnlineConvex.convexExtended_iff_toReal
#print axioms BanditRL.OnlineConvex.convex_add_indicator
#print axioms BanditRL.OnlineConvex.theorem_2_4
#print axioms convex_linear
#print axioms nondegenerate

end Tests.OnlineConvexExtended
