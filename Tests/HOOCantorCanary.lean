import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof.HOO
open BanditRLProof.HOO.CantorModel

noncomputable section
namespace HOOCantorCanary

example : Infinite Arm := inferInstance
example : RegularCovering Arm := covering
example : WeaklyLipschitz mean ell (1/2) := weaklyLipschitz
example (x : Arm) (r : ℝ) : law x ≠ Measure.dirac r := law_not_dirac x r

example : (∫ y, y ∂law (fun _ => false)) = (1/2:ℝ) := by rw [law_mean]; norm_num [mean]
example : (∫ y, y ∂law (fun _ => true)) = (1/4:ℝ) := by rw [law_mean]; norm_num [mean]

example : regionSup mean (covering.region poorNode) = 1/4 := poor_sup

example (N : ℕ) :
    (∫ Y, (visits (history 1 (1/2) Y N) poorNode : ℝ)
      ∂trajectory 1 (1/2) (covering.toCovering.nodeLaw law)) ≤
      512 * Real.log (max (N:ℝ) 2) + 4 := expected_poor_visits N

#print axioms BanditRLProof.HOO.CantorModel.covering
#print axioms BanditRLProof.HOO.CantorModel.expected_poor_visits
#print axioms BanditRLProof.HOO.CantorModel.law_not_dirac
#print axioms BanditRLProof.HOO.RegularCovering.exists_finite_packing_bound

end HOOCantorCanary
