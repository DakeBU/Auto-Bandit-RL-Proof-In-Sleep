import Tests.OnlineAffineSubgradientCanary
set_option pp.universes true
#check @BanditRL.OnlineConvex.theorem_2_28
#check @AffineProbe.double_adjoint
#check @AffineProbe.absolute_proper
#check @AffineProbe.nonzero_shifted_support
#check @AffineProbe.neg_abs_proper
#check @AffineProbe.neg_abs_support_empty
#check @AffineProbe.neg_abs_not_convex
#check @AffineProbe.proper_nonconvex_strict_inclusion
#check @AffineProbe.doubleMap
#check @AffineProbe.negAbsLoss
#print BanditRL.OnlineConvex.SourceSubdifferential
#print BanditRL.OnlineConvex.SourceProper
#print BanditRL.OnlineConvex.effectiveDomain
#print BanditRL.OnlineConvex.realEpigraph
#print BanditRL.OnlineConvex.IsConvexExtended
