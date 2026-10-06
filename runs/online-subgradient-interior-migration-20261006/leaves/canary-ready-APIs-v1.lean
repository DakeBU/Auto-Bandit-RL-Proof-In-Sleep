import BanditRLProof.OnlineSubgradientInterior
import Tests.OnlineConvexMinorantCanary
open Set BanditRL.OnlineConvex
open scoped Topology
#check @intrinsicInterior_singleton
#check @interior_singleton
#check @convex_effectiveDomain
#check @convex_indicator_iff
#check @effectiveDomain_indicator
#check @sourceProper_indicator_iff
#check @Tests.OnlineConvexMinorant.loss_noBot
#check @Tests.OnlineConvexMinorant.loss_convex
#check @Tests.OnlineConvexMinorant.loss_domain
#check @Tests.OnlineConvexMinorant.nondegenerate_nonclosed
#check @Tests.OnlineConvexBarycenter.ray_convex
