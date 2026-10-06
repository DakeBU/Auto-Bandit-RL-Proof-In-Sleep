import BanditRLProof.OnlineSubgradientInterior
open Set
open scoped Topology
section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
#synth CompleteSpace F
#check @InnerProductSpace.toDual
#check @InnerProductSpace.toDual_symm_apply
#check @mem_intrinsicInterior
#check @intrinsicInterior_subset
#check @Set.Nonempty.intrinsicInterior
#check @AffineIsometryEquiv.vaddConst
#check @LinearMap.exists_extend
#check @LinearMap.toContinuousLinearMap
end
