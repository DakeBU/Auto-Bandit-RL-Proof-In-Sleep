import BanditRLProof

namespace Tests.CausalMarginalLawCanary
open BanditRLProof.Causal

/-- The target is node one, so a later node is genuinely marginalized out. -/
example (g : GraphModel Bool 3) (z : g.ParentConfig 1) :
    ((joint (g.doModel (fun i => if i = 0 then some true else none)).table).map
      (fun x => (g.parentConfig 1 (history x 1),x 1))) (z,true) =
    g.parentLaw (fun i => if i = 0 then some true else none) 1 z *
      g.parentTable 1 z true := by
  apply g.intervention_parent_mass
  decide

#print axioms joint_map_take
#print axioms joint_map_node_pair
#print axioms GraphModel.table_eq_parentTable
#print axioms GraphModel.intervention_parent_joint
#print axioms GraphModel.intervention_parent_mass
end Tests.CausalMarginalLawCanary
