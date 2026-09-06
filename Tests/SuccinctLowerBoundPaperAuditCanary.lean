import BanditRLProof

/-!
# Succinct lower-bound paper-audit canary

This root-import canary fixes the public names of the compiled Definition
3.1--3.3 geometry, source Lemmas 3.1--3.4, and the global `R` boundedness
diagnostic.  It does not check Lemmas 3.5--3.6 or Theorem 3.8.
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
#check SuccinctUnitSystem.SuccinctRepresentation
#check SuccinctUnitSystem.StrictSuccinctRepresentation
#check SuccinctUnitSystem.IsSuccinctAt
#check SuccinctUnitSystem.IsStrictlySuccinctAt
#check SuccinctUnitSystem.SuccinctRepresentation.abs_inner_strictBasis_supportSignCombination_eq_one
#check SuccinctUnitSystem.SuccinctRepresentation.strictSize_le
#check SuccinctUnitSystem.succinctSize_ge_strictSize
#check SuccinctUnitSystem.strictlySuccinctSize_unique
#check SuccinctUnitSystem.sourceRSet_not_bddAbove_of_nonzero_atom_orthogonal

#print axioms SuccinctUnitSystem.IsSuccinctSupport.inner_basis_basis
#print axioms SuccinctUnitSystem.IsSuccinctSupport.sourceQ_supportCombination_eq
#print axioms SuccinctUnitSystem.IsSuccinctSupport.sourceR_supportCombination_eq
#print axioms SuccinctUnitSystem.SuccinctRepresentation.strictSize_le
#print axioms SuccinctUnitSystem.succinctSize_ge_strictSize
#print axioms SuccinctUnitSystem.strictlySuccinctSize_unique
#print axioms SuccinctUnitSystem.sourceRSet_not_bddAbove_of_nonzero_atom_orthogonal

end BanditRLProof.SuccinctLowerBoundPaperAuditCanary
