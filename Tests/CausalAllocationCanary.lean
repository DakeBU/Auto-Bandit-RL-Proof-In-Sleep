import BanditRLProof
import BanditRLProof.Algorithms.CausalAllocation

namespace Tests.CausalAllocationCanary
open BanditRLProof.Causal

example (b : Bool) : secondMoment (PMF.pure b)
    (mixture (PMF.uniformOfFintype Bool) (fun a => PMF.pure a)) = 2 := by
  simp only [mixture, PMF.bind_pure]
  cases b <;> norm_num [secondMoment, ratio, mass, PMF.uniformOfFintype_apply,
    PMF.pure_apply, Fintype.sum_bool]

#print axioms secondMoment_ge_one
#print axioms uniform_covers
#print axioms uniform_designCost_le_card
#print axioms convexLaw_covers
#print axioms designCost_convex
#print axioms design_sublevel_mass_lower
end Tests.CausalAllocationCanary
