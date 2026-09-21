import BanditRLProof
import BanditRLProof.Algorithms.CausalOptimalAllocation

namespace Tests.CausalOptimalAllocationCanary
open BanditRLProof.Causal

example (q : PMF Bool) : designCost (fun _ : Bool => q)
    (optimalAllocation (fun _ : Bool => q)) = 1 := constant_designCost q _

/-- A simplex boundary allocation remains admissible when all supports coincide. -/
example (q : PMF Bool) : Covers (fun _ : Bool => q)
    (mixture (PMF.pure false) (fun _ => q)) ∧
    designCost (fun _ : Bool => q) (PMF.pure false) = 1 := by
  constructor
  · simpa [mixture] using (show Covers (fun _ : Bool => q) q from fun _ _ h => h)
  · exact constant_designCost q _

#print axioms safeAllocations_compact
#print axioms coordinateCost_continuousOn
#print axioms exists_optimal_allocation
#print axioms optimalAllocation_covers
#print axioms optimalAllocation_minimizes
#print axioms optimalAllocation_cost_le_card
end Tests.CausalOptimalAllocationCanary
