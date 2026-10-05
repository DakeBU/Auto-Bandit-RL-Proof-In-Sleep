import BanditRLProof
import Tests.OnlineSubgradientBasicCanary
set_option pp.universes true
set_option pp.explicit true
#check @BanditRL.OnlineConvex.subgradient_point_finite
#check @BanditRL.OnlineConvex.theorem_2_21
#check @BanditRL.OnlineConvex.SourceSubdifferential
#check @SubgradientProbe.square_support
#check @SubgradientProbe.square_convex
#check @SubgradientProbe.interval_outside_no_support
