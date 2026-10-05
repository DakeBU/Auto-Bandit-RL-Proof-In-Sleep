Frozen primary source: Orabona arXiv1912.13213v10, 21 June2026; printed9-10/PDF21-22. Def2.2 convex sets uses every x,y in V and strictly interior real weight. Def2.3 extended-real convexity uses a REAL-height epigraph; f permits both infinities. Domain is f(x)<top and includes bottom. Indicator is zero inside V/top outside. Required unnumbered consequences: convex domain, indicator convex iff V convex, and addition of indicator to noBottom convex f on convex V. Empty sets/domains allowed. Theorem2.4 explicitly assumes noBottom and convex effective domain and quantifies only domain points,0<theta<1. Those hypotheses are retained, not moved into a new definition of convexity. Epigraph/toReal and real-valued coercion iff are proved bridges; toReal is only used on finite values in the characterization.

Example2.5 covers all affine inner-product functions including zero slope and arbitrary intercept; Example2.6 covers all norms, even though its proof is left as an exercise. Abstract real module/normed/inner-product space generality includes source finite-dimensional Euclidean instances. No compactness, closedness, strict positivity of norm values, probability or algorithm premise.

Four required p10 closure bullets: nonnegative linear combinations, affine precomposition, real convex/nondecreasing outer composition, and arbitrary indexed supremum. Affine maps need not be injective/continuous. Supremum has no nonempty index or bounded-family assumption and may take both infinities. Monotone composition keeps the source explicitly REAL-valued f and g and global Monotone g. It does not extend g to EReal.

Convention delta: Orabona does not print a mixed-infinity addition convention. The nonnegative-combination interface explicitly adopts the convex-analysis upper addition upperAdd(a,b)=-(-a+-b), supported by Rockafellar Conjugate Duality and Optimization printed6/PDF17. This is an attributed interpretation, not a literal assertion in Orabona. Ordinary mathlib EReal addition is bottom-dominant and fails the unrestricted closure: the existing public spike counterexample must be freshly compiled. upperAdd agrees with finite addition/top dominance and includes improper functions, disjoint domains, zero weights and zero-times-infinity=0. No noBottom/properness/nonempty-domain restriction is added to the general closure. Indicator addition uses ordinary + with explicit noBottom so there is no mixed-infinity ambiguity.

Migration scope is four existing production modules,22 retained actual proof bodies/five definitions, not22 new source theorems/proofs or Chapter2 completion. Every frozen header stays exact; retained bodies must be inspected/freshly compiled after separate distinct-actor source-contract review. Existing canaries are replayed, not counted new mathematical progress. Legacy same-model reviews remain historical. Native command gates and file/prompt semantic review are separate; no single-runtime enforcement, external human review or independent runtime model attestation claim. Whole Chapters1-16 Goal remains active; other required main text and appendix dependencies are not excluded.

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
