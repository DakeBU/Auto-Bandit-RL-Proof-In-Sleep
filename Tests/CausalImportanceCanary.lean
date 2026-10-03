import BanditRLProof

namespace Tests.CausalImportanceCanary
open BanditRLProof.Causal

example (q : PMF Bool) :
    Covers (fun _ : Bool => q) (mixture (PMF.pure false) (fun _ => q)) := by
  simpa [mixture] using (show Covers (fun _ : Bool => q) q from fun _ _ h => h)

example : ¬ Covers (fun b : Bool => PMF.pure b)
    (mixture (PMF.pure false) (fun b => PMF.pure b)) := by
  intro hc
  have h := hc true true
  norm_num [mass, mixture, PMF.pure_apply] at h

#print axioms mixture_mass
#print axioms positive_allocation_covers
#print axioms importance_identity
#print axioms truncatedMean_add_bias
#print axioms truncationBias_le
#print axioms weightedBit_mean
#print axioms weightedBit_bounds
#print axioms weightedBit_second_le
#print axioms GraphModel.mixture_parent_joint
end Tests.CausalImportanceCanary
