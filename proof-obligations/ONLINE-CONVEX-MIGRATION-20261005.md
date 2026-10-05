# Required retained convex endpoints

| Target | Dependencies | State |
|---|---|---|
|definition_2_2||retained; fresh distinct source/body review pending|
|convex_effectiveDomain||retained; fresh distinct source/body review pending|
|effectiveDomain_indicator||retained; fresh distinct source/body review pending|
|convex_indicator_iff|convex_effectiveDomain,effectiveDomain_indicator|retained; fresh distinct source/body review pending|
|realEpigraph_toReal||retained; fresh distinct source/body review pending|
|convexExtended_iff_toReal|realEpigraph_toReal|retained; fresh distinct source/body review pending|
|theorem_2_4|convexExtended_iff_toReal|retained; fresh distinct source/body review pending|
|convex_add_indicator||retained; fresh distinct source/body review pending|
|convexExtended_coe_iff|convexExtended_iff_toReal|retained; fresh distinct source/body review pending|
|example_2_5|convexExtended_coe_iff|retained; fresh distinct source/body review pending|
|example_2_6|convexExtended_coe_iff|retained; fresh distinct source/body review pending|
|convex_comp_affine||retained; fresh distinct source/body review pending|
|convex_iSup||retained; fresh distinct source/body review pending|
|convex_comp_monotone|convexExtended_coe_iff|retained; fresh distinct source/body review pending|
|upperAdd_coe||retained; fresh distinct source/body review pending|
|upperAdd_top||retained; fresh distinct source/body review pending|
|top_upperAdd||retained; fresh distinct source/body review pending|
|upperAdd_le_coe_iff||retained; fresh distinct source/body review pending|
|convex_upperAdd|upperAdd_le_coe_iff|retained; fresh distinct source/body review pending|
|positive_mul_le_coe_iff||retained; fresh distinct source/body review pending|
|convex_nonneg_mul|positive_mul_le_coe_iff,convexExtended_coe_iff|retained; fresh distinct source/body review pending|
|convex_nonneg_linear_combination|convex_upperAdd,convex_nonneg_mul|retained; fresh distinct source/body review pending|

Allowed edits after source-reviewed stabilization: source-qualified comments in these four modules, task-local evidence/contracts and scoped shared Book/contributor mapping. No public header/definition/body change; new target requires new version/review. Preserve accepted OGD/FTL inputs and raw-reader bindings via explicit preedit snapshots if shared readers change. Global SGB untouched; no chapter/Goal/main/live completion.

All22 native fences/source review/body review/public canaries/axioms/root/Tests/full harness/shared graph/shadow/registry/site/contributor/PR gates separately required. Actual22 proofs are not22 original numbered results. Other Chapter2 obligations remain mandatory.
