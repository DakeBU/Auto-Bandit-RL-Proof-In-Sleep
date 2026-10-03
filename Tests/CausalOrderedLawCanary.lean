import BanditRLProof

namespace Tests.CausalOrderedLawCanary
open BanditRLProof.Causal

example (g : GraphModel Bool 3) (x : Fin 3 → Bool) (hx : x 1 = false) :
    joint (g.doModel (fun i => if i = 1 then some true else none)).table x = 0 := by
  apply intervention_incompatible_zero g _ x 1 true
  · simp
  · simp [hx]

#print axioms joint_factorization
#print axioms joint_normalized
#print axioms GraphModel.doModel
#print axioms doModel_factorization
#print axioms intervention_incompatible_zero
end Tests.CausalOrderedLawCanary
