import BanditRLProof

/-!
# Succinct lower-bound paper-audit canary

This root-import canary fixes the public names of the compiled Definition
3.1--3.2 geometry, source Lemmas 3.1--3.2, and the global `R` boundedness
diagnostic.  It does not check Theorem 3.8.
-/

namespace BanditRLProof.SuccinctLowerBoundPaperAuditCanary

open LowerBounds.Succinct

#check SuccinctUnitSystem
#check SuccinctUnitSystem.sourceQ
#check SuccinctUnitSystem.sourceR
#check SuccinctUnitSystem.IsSuccinctSupport
#check SuccinctUnitSystem.IsSuccinctSupport.inner_basis_basis
#check SuccinctUnitSystem.IsSuccinctSupport.maxAbsCoefficient
#check SuccinctUnitSystem.IsSuccinctSupport.supportCombination
#check SuccinctUnitSystem.IsSuccinctSupport.sourceQ_supportCombination_eq
#check SuccinctUnitSystem.IsSuccinctSupport.sourceRSet_bddAbove
#check SuccinctUnitSystem.IsSuccinctSupport.sourceR_supportCombination_eq
#check SuccinctUnitSystem.sourceRSet_not_bddAbove_of_nonzero_atom_orthogonal

#print axioms SuccinctUnitSystem.IsSuccinctSupport.inner_basis_basis
#print axioms SuccinctUnitSystem.IsSuccinctSupport.sourceQ_supportCombination_eq
#print axioms SuccinctUnitSystem.IsSuccinctSupport.sourceR_supportCombination_eq
#print axioms SuccinctUnitSystem.sourceRSet_not_bddAbove_of_nonzero_atom_orthogonal

end BanditRLProof.SuccinctLowerBoundPaperAuditCanary
