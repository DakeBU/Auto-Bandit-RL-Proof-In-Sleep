import BanditRLProof
import Tests.OnlineConvexExtendedCanary
import Tests.OnlineConvexExamplesCanary
import Tests.OnlineConvexClosuresCanary
import Tests.OnlineConvexSumsCanary

#check @BanditRL.OnlineConvex.definition_2_2
#print axioms BanditRL.OnlineConvex.definition_2_2
#check @BanditRL.OnlineConvex.convex_effectiveDomain
#print axioms BanditRL.OnlineConvex.convex_effectiveDomain
#check @BanditRL.OnlineConvex.effectiveDomain_indicator
#print axioms BanditRL.OnlineConvex.effectiveDomain_indicator
#check @BanditRL.OnlineConvex.convex_indicator_iff
#print axioms BanditRL.OnlineConvex.convex_indicator_iff
#check @BanditRL.OnlineConvex.realEpigraph_toReal
#print axioms BanditRL.OnlineConvex.realEpigraph_toReal
#check @BanditRL.OnlineConvex.convexExtended_iff_toReal
#print axioms BanditRL.OnlineConvex.convexExtended_iff_toReal
#check @BanditRL.OnlineConvex.theorem_2_4
#print axioms BanditRL.OnlineConvex.theorem_2_4
#check @BanditRL.OnlineConvex.convex_add_indicator
#print axioms BanditRL.OnlineConvex.convex_add_indicator
#check @BanditRL.OnlineConvex.convexExtended_coe_iff
#print axioms BanditRL.OnlineConvex.convexExtended_coe_iff
#check @BanditRL.OnlineConvex.example_2_5
#print axioms BanditRL.OnlineConvex.example_2_5
#check @BanditRL.OnlineConvex.example_2_6
#print axioms BanditRL.OnlineConvex.example_2_6
#check @BanditRL.OnlineConvex.convex_comp_affine
#print axioms BanditRL.OnlineConvex.convex_comp_affine
#check @BanditRL.OnlineConvex.convex_iSup
#print axioms BanditRL.OnlineConvex.convex_iSup
#check @BanditRL.OnlineConvex.convex_comp_monotone
#print axioms BanditRL.OnlineConvex.convex_comp_monotone
#check @BanditRL.OnlineConvex.upperAdd_coe
#print axioms BanditRL.OnlineConvex.upperAdd_coe
#check @BanditRL.OnlineConvex.upperAdd_top
#print axioms BanditRL.OnlineConvex.upperAdd_top
#check @BanditRL.OnlineConvex.top_upperAdd
#print axioms BanditRL.OnlineConvex.top_upperAdd
#check @BanditRL.OnlineConvex.upperAdd_le_coe_iff
#print axioms BanditRL.OnlineConvex.upperAdd_le_coe_iff
#check @BanditRL.OnlineConvex.convex_upperAdd
#print axioms BanditRL.OnlineConvex.convex_upperAdd
#check @BanditRL.OnlineConvex.positive_mul_le_coe_iff
#print axioms BanditRL.OnlineConvex.positive_mul_le_coe_iff
#check @BanditRL.OnlineConvex.convex_nonneg_mul
#print axioms BanditRL.OnlineConvex.convex_nonneg_mul
#check @BanditRL.OnlineConvex.convex_nonneg_linear_combination
#print axioms BanditRL.OnlineConvex.convex_nonneg_linear_combination
#check @BanditRL.OnlineConvex.effectiveDomain
#print axioms BanditRL.OnlineConvex.effectiveDomain
#check @BanditRL.OnlineConvex.realEpigraph
#print axioms BanditRL.OnlineConvex.realEpigraph
#check @BanditRL.OnlineConvex.IsConvexExtended
#print axioms BanditRL.OnlineConvex.IsConvexExtended
#check @BanditRL.OnlineConvex.extendedIndicator
#print axioms BanditRL.OnlineConvex.extendedIndicator
#check @BanditRL.OnlineConvex.upperAdd
#print axioms BanditRL.OnlineConvex.upperAdd
#check @Tests.OnlineConvexExtended.restrictedLinear
#print axioms Tests.OnlineConvexExtended.restrictedLinear
#check @Tests.OnlineConvexExtended.domain_linear
#print axioms Tests.OnlineConvexExtended.domain_linear
#check @Tests.OnlineConvexExtended.no_bot_linear
#print axioms Tests.OnlineConvexExtended.no_bot_linear
#check @Tests.OnlineConvexExtended.convex_linear
#print axioms Tests.OnlineConvexExtended.convex_linear
#check @Tests.OnlineConvexExtended.nondegenerate
#print axioms Tests.OnlineConvexExtended.nondegenerate
#check @Tests.OnlineConvexExamples.affine
#print axioms Tests.OnlineConvexExamples.affine
#check @Tests.OnlineConvexExamples.affine_convex
#print axioms Tests.OnlineConvexExamples.affine_convex
#check @Tests.OnlineConvexExamples.norm_convex
#print axioms Tests.OnlineConvexExamples.norm_convex
#check @Tests.OnlineConvexExamples.nondegenerate
#print axioms Tests.OnlineConvexExamples.nondegenerate
#check @Tests.OnlineConvexExamples.norm_midpoint
#print axioms Tests.OnlineConvexExamples.norm_midpoint
#check @Tests.OnlineConvexClosures.shift
#print axioms Tests.OnlineConvexClosures.shift
#check @Tests.OnlineConvexClosures.shifted_indicator_convex
#print axioms Tests.OnlineConvexClosures.shifted_indicator_convex
#check @Tests.OnlineConvexClosures.shifted_values
#print axioms Tests.OnlineConvexClosures.shifted_values
#check @Tests.OnlineConvexClosures.family
#print axioms Tests.OnlineConvexClosures.family
#check @Tests.OnlineConvexClosures.family_convex
#print axioms Tests.OnlineConvexClosures.family_convex
#check @Tests.OnlineConvexClosures.supremum_convex
#print axioms Tests.OnlineConvexClosures.supremum_convex
#check @Tests.OnlineConvexClosures.supremum_values
#print axioms Tests.OnlineConvexClosures.supremum_values
#check @Tests.OnlineConvexClosures.outer
#print axioms Tests.OnlineConvexClosures.outer
#check @Tests.OnlineConvexClosures.outer_monotone
#print axioms Tests.OnlineConvexClosures.outer_monotone
#check @Tests.OnlineConvexClosures.composed_norm_convex
#print axioms Tests.OnlineConvexClosures.composed_norm_convex
#check @Tests.OnlineConvexSums.spike
#print axioms Tests.OnlineConvexSums.spike
#check @Tests.OnlineConvexSums.spike_convex
#print axioms Tests.OnlineConvexSums.spike_convex
#check @Tests.OnlineConvexSums.naive_sum_not_convex
#print axioms Tests.OnlineConvexSums.naive_sum_not_convex
#check @Tests.OnlineConvexSums.upper_spikes_convex
#print axioms Tests.OnlineConvexSums.upper_spikes_convex
#check @Tests.OnlineConvexSums.mixed_infinity_values
#print axioms Tests.OnlineConvexSums.mixed_infinity_values
#check @Tests.OnlineConvexSums.positive_combination
#print axioms Tests.OnlineConvexSums.positive_combination

