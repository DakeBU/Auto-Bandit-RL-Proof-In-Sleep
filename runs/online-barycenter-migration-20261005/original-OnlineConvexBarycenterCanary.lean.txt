import BanditRLProof

noncomputable section
open Set Filter MeasureTheory BanditRL.OnlineConvex
open scoped ENNReal
namespace Tests.OnlineConvexBarycenter

def law : Measure ℝ := (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + (1 / 2 : ℝ≥0∞) • Measure.dirac 3

instance law_probability : IsProbabilityMeasure law := by
  constructor
  norm_num [law, ENNReal.inv_two_add_inv_two]

def vector (x : ℝ) : ℝ × ℝ := (x, 0)
def ray : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.2 = 0}

theorem ray_convex : Convex ℝ ray := by
  exact ((convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)).inter
    ((convex_singleton (0 : ℝ)).linear_preimage (LinearMap.snd ℝ ℝ ℝ))

theorem ray_not_closed : ¬ IsClosed ray := by
  intro h
  have hi : IsClosed (Ioi (0 : ℝ)) := by
    convert h.preimage (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))) using 1
    ext x
    simp [ray]
  have he := hi.closure_eq
  rw [closure_Ioi] at he
  have hz : (0 : ℝ) ∈ Ici 0 := by simp
  rw [he] at hz
  exact lt_irrefl (0 : ℝ) hz

theorem vector_integrable : Integrable vector law := by
  have h1 : Integrable vector (Measure.dirac (1 : ℝ)) := integrable_dirac (by simp [vector])
  have h3 : Integrable vector (Measure.dirac (3 : ℝ)) := integrable_dirac (by simp [vector])
  exact (h1.smul_measure (by norm_num)).add_measure (h3.smul_measure (by norm_num))

theorem vector_in_ray : ∀ᵐ x ∂law, vector x ∈ ray := by
  rw [law, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simp [vector, ray]
  · apply Measure.ae_smul_measure
    simp [vector, ray]

theorem mean_in_ray : (∫ x, vector x ∂law) ∈ ray :=
  integral_mem_convex_finiteDimensional law ray ray_convex vector vector_integrable vector_in_ray

theorem vector_mean : (∫ x, vector x ∂law) = ((2 : ℝ), (0 : ℝ)) := by
  have h1 : Integrable vector ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp [vector])).smul_measure (by norm_num)
  have h3 : Integrable vector ((1 / 2 : ℝ≥0∞) • Measure.dirac (3 : ℝ)) :=
    (integrable_dirac (by simp [vector])).smul_measure (by norm_num)
  rw [law, integral_add_measure h1 h3, integral_smul_measure, integral_smul_measure]
  norm_num [integral_dirac, vector, Prod.smul_mk, Prod.mk_add_mk]

theorem nondegenerate_nonclosed : (∫ x, vector x ∂law) ∈ ray ∧
    (∫ x, vector x ∂law) = ((2 : ℝ), (0 : ℝ)) ∧ ¬ IsClosed ray ∧ vector 1 ≠ vector 3 := by
  exact ⟨mean_in_ray, vector_mean, ray_not_closed, by norm_num [vector]⟩

#print axioms BanditRL.OnlineConvex.supporting_functional_ae_eq_mean
#print axioms BanditRL.OnlineConvex.supporting_functional_at_closure
#print axioms BanditRL.OnlineConvex.integral_mem_convex_finiteDimensional
#print axioms mean_in_ray
#print axioms nondegenerate_nonclosed
end Tests.OnlineConvexBarycenter
