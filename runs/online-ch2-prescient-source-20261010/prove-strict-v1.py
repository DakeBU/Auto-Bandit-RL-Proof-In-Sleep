from proof_driver import *
assert load(RUN/'proper-focused-inspected-v1.json')['actual_exit']==0
body='''  have hc := finitePart_convex_of_subdifferentiable f V hV hf hs
  refine ⟨hV, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hfc := hc.2 hp hq ha.le hb.le hab
  have hψs := hψ.2 (hVX hp) (hVX hq) hpq ha hb hab
  simp only [smul_eq_mul] at hfc hψs ⊢
  have hlinear : fderiv ℝ ψ x (a • p + b • q - x) =
      a * fderiv ℝ ψ x (p - x) + b * fderiv ℝ ψ x (q - x) := by
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    have he : b = 1 - a := by linarith only [hab]
    rw [he]
    ring
  have hD : divergence ψ (a • p + b • q) x <
      a * divergence ψ p x + b * divergence ψ q x := by
    unfold divergence
    rw [hlinear]
    have hconst : (a + b) * ψ x = ψ x := by rw [hab, one_mul]
    nlinarith only [hψs, hconst]
  have hweighted := mul_lt_mul_of_pos_left hD (inv_pos.mpr hη)
  nlinarith only [hfc, hweighted]
'''
assert append_proof(1,'strict-attempt-v1',body)
