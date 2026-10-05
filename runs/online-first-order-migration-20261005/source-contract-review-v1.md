# First-order migration source-contract review v1

Verdict: **accepted-with-explicit-delta**, stabilization of three retained contracts only. Mathematical repairs: none. Reader corrections below remain required before final reader acceptance.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium. No human, external-model review or independently attested runtime-model claim. Historical same-actor acceptance is not the basis of this decision.

Independently read/hash-checked all 79 fixed rows: zero mismatch. Inventory and actual header-extraction implementation also bound, giving 81 rows. Raw integrity reading of ancillary history does not recertify those packages. Semantic focus: actual public module, scoped context/native headers, shared definitions and pinned APIs, fresh neutral reconstruction and selected first-order reader entries.

Original Orabona v10 PDF SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; printed 10–11 / physical 22–23 read, Theorem 2.7 freshly extracted directly from physical 23. It assumes convex f:R^d→(-infinity,+infinity], x in ambient interior dom f, differentiability at x, and concludes the support inequality for every y in R^d. All three actual extracted headers equal frozen strings and statement hashes. Fresh restricted decoder agrees on the three distinct scopes; actual imported semantics were checked rather than inferred from its report.

## Seven slots per target

### BanditRL.OnlineConvex.finitePart_eventually

Verdict: accepted-with-explicit-delta, representation helper.

1. Objects: EReal f and canonical real conversion in shared complete real inner-product context.
2. Quantifiers: every globally no-bottom f and ambient-interior x; eventually all z near x.
3. Assumptions: global noBottom and ambient interior of domain f<top. Neither convexity nor differentiability is required; shared Hilbert structure is more than this topological fact needs.
4. Guarantee: embedding of (f z).toReal equals f z locally, including at x, not globally.
5. Normalization: exact embedding equality, no approximation.
6. Information/probability: deterministic neighborhood filter; no algorithm or random event.
7. Boundaries: domain alone permits bottom, so hbot is essential here. Top may occur away from x. Relative interior is not a substitute; empty ambient interior gives no admissible x.

### BanditRL.OnlineConvex.convex_gradient_lower_bound

Verdict: accepted-with-explicit-delta, generalized real helper.

1. Objects: everywhere real-valued f, subset V, x/y and ambient gradient in a complete real inner-product space.
2. Quantifiers: all V,f and x,y in V meeting the derivative premise, not y outside V.
3. Assumptions: ConvexOn includes convex V and f's convex inequality; ambient DifferentiableAt at x and both memberships. No openness, interior, closedness, boundedness or differentiability at y.
4. Guarantee: f(x)+inner(gradient f x,y-x)≤f(y), the exact real support bound.
5. Normalization: coefficient one, gradient first, displacement y-x, no residual.
6. Information/probability: deterministic pointwise comparison, no oracle/selected-support premise.
7. Boundaries: boundary points allowed with ambient derivative; empty V has no witnesses. No extended-real local representation is needed by this helper. It is not itself the printed extended-real terminal.

### BanditRL.OnlineConvex.theorem_2_7

Verdict: accepted-with-explicit-delta, source terminal in generalized ambient space.

1. Objects: no-bottom EReal f with convex real-height epigraph, canonical F(z)=(f z).toReal, and gradient F x. Complete real inner-product spaces generalize source Euclidean spaces explicitly.
2. Quantifiers: every such f, every ambient-interior differentiability point x, every y in E without a comparator membership/finite-value condition.
3. Assumptions: global noBottom matches source codomain; epigraph convexity uses shared definition; DifferentiableAt F x only. No global differentiability, closedness, boundedness or Lipschitz restriction.
4. Guarantee: exact EReal inequality f x+coe(inner(gradient F x,y-x))≤f y for all y.
5. Normalization: gradient of precisely canonical F, not an arbitrary chosen vector. Actual gradient is Riesz inverse of fderiv and DifferentiableAt.hasGradientAt gives its derivative meaning. No fallback-zero shortcut under the derivative premise.
6. Information/probability: deterministic support assertion, no learning algorithm or causality claim.
7. Boundaries: interior/noBottom imply finite f(x); domain/noBottom imply finite f(y) when y is in domain. Otherwise f(y)=top, and that case remains in the conclusion. Empty-interior domains have no admissible x; zero dimension is allowed. Infinite values mapping to zero under toReal does not imply global equality with f or global convexity of F.

## Anti-anchoring findings

The canonical representation is locally source-faithful: the neighborhood embedding identity makes the finite source function and F agree near x. It does not prove differentiability from convexity. Global noBottom is retained, not reduced to point finiteness. Arbitrary y and the top branch prevent a restricted-domain-only conclusion. Ambient interior is not relative interior. No mathematical target repair was found.

Existing bodies were read for contradictions, not accepted as a fresh body audit in this contract phase. Direct elaboration/type/API and scoped three-node proof graph are readiness evidence only, not combined project/canary export or safe-verifier proof acceptance. The two helpers must not be attributed as additional printed theorems.

Required reader corrections:
1. Label finitePart_eventually and convex_gradient_lower_bound as library representation/generalized helpers, not additional printed source theorems.
2. Correct the real helper highlight: its everywhere real-valued function, ConvexOn V, x/y membership and ambient DifferentiableAt at x do not require an open V or the extended-real local finite-representation lemma.
3. Qualify the old OGD first_order relationship with its stronger RegularLoss assumptions; distinguish the separately added source-compatible OGD adapter.
4. Keep canonical F(z)=(f z).toReal, global noBottom, ambient interior and local embedding identity explicit together, with all-y/top-comparator scope.

The current positive-half-line example has a nonconstant finite branch and outside top query. Actual canary replay and reader pixel validation are not certified here.

Remaining: separate retained-body/canary/axiom/native-guard review, combined root/Tests/full harness, registry/site/contributor/final reader, immutable bindings and PR delivery. Zero new proof code or registry nodes is this migration's intended scope. Theorem 2.8, other migrations, Chapter 2, whole book/Goal, main integration and live deployment are not accepted. Chapter 2 remains incomplete with unspecified total; Whole Goal active.

## Exact raw reviewed inventory

| Path | SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean` | `c7a80e952f6f577c441b92802fc5020fa63b564b75418fb96e29d4f6813020ca` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean` | `2022754e5f0c541b8ca4271231c95713996d9f4ac1f997e3973ec9e6c7bec7c4` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `Tests/OnlineConvexFirstOrderCanary.lean` | `031451c1602cdcb5bd79054c589f6b9c9045d43273b2b1540b77d7bef768af6c` |
| `conversion-windows/ONLINE-FIRST-ORDER-MIGRATION-20261005.md` | `056b09e81a1705ad182148d070affbef0e847cc2f1ab5b099c7bc3cf60f82776` |
| `docs/contracts/online-first-order-migration-v1/context.lean.txt` | `dd633c0cd797172f8c7d517a08ace6962d285b0d3f346da750dfee92524cd878` |
| `docs/contracts/online-first-order-migration-v1/convex_gradient_lower_bound-header.txt` | `f201a63268760cdc170d78454d08fc18806217e36b772b8076de594074d779e5` |
| `docs/contracts/online-first-order-migration-v1/convex_gradient_lower_bound.json` | `6b544f0d44662e8c5510fcb5a9e5e771bd6e090e88b7d7da9b448f71dbfc81c6` |
| `docs/contracts/online-first-order-migration-v1/finitePart_eventually-header.txt` | `a953a3cf29dc9f5f23970146271df0788776200a4bf57819be2015aec301aef5` |
| `docs/contracts/online-first-order-migration-v1/finitePart_eventually.json` | `231331421ed3509d2f0ee4e0beaedf1dd8d51f6176d4d3aea6fdcaa78cbaa7c7` |
| `docs/contracts/online-first-order-migration-v1/source-card.json` | `f9eac10df8a7d327f33ad4822c8d2e2e034377faddada05bf0f85f317beeba2c` |
| `docs/contracts/online-first-order-migration-v1/source-intent.md` | `ecc0be46a013737c93b824d56bce2ff11b34c9e3a54ab2f82c630a79b06421ae` |
| `docs/contracts/online-first-order-migration-v1/theorem_2_7-header.txt` | `d2a4b7f0f72360bd91d34a96065d0459d0612d60fde42b256e2bacc3acebd7eb` |
| `docs/contracts/online-first-order-migration-v1/theorem_2_7.json` | `00d37ea466eb85d3901279734f73058caa9f95330d462bc9a8399c5993e5a3c6` |
| `docs/contracts/online-first-order-v1/context.json` | `9fdee08f514ad7d74f4c854acce8195534b5528de92a4ce7062899722b28b3e0` |
| `docs/contracts/online-first-order-v1/contract.md` | `4e36b91cfcb95eaef9a162500cd91b4a38a5a688433c76549c80a43bff56c7a4` |
| `docs/contracts/online-first-order-v1/convex_gradient_lower_bound.json` | `04b1703dd904514ca835f29d8b254687ad5ccb186f6dbb3a817abe81b18c13bb` |
| `docs/contracts/online-first-order-v1/finitePart_eventually.json` | `4e163e2f67fd08d135e822626e3943f9aaa2ca6e40c934abdeb912b15f1a2510` |
| `docs/contracts/online-first-order-v1/headers.json` | `142095f55c843c8ce02200cc6a6accd4a4a6344cc3b6ae1250afa170610505d2` |
| `docs/contracts/online-first-order-v1/theorem_2_7.json` | `679d7a6a3eb4b6694db20a45f4f383643e01ebbf5d7310a15b8a690365a2f0d2` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-FIRST-ORDER-MIGRATION-20261005.md` | `db6e7b9ef1bf598717100b18c0735d2c59133de6267976a54c066b3e8c751bf6` |
| `runs/online-finite-loss-20261005/accepted-decision-v1.json` | `580749e836dd899e35a3694be0a9070c91ad25a38cc0f4dacd5421296820bbe4` |
| `runs/online-finite-loss-20261005/native-acceptance-overlay-v2.json` | `300d8e20ca01ea543d9be02f34db1926318599398b38afded941a2d0cb7b5ac9` |
| `runs/online-first-order-migration-20261005/00_context.md` | `605a3c4f401b241a73fc5656874f0bdead40fb9fe74d532246d3cae66dff20e8` |
| `runs/online-first-order-migration-20261005/10_upper_director-v1.md` | `9f58d109ab5cba0a0de01c0f14e1de1a85f500941913362eb305021c542ac02d` |
| `runs/online-first-order-migration-20261005/20_architect-v1.md` | `924e189e8602c19467c62f6beab89d2455564cf9c1d0764c7cd1cadec9b00b81` |
| `runs/online-first-order-migration-20261005/actual-pinned-API-retrieval-v1-01-exit.json` | `0050f61da106af4ebfae79282730e21348d9080af99ce874f1ab075114dada06` |
| `runs/online-first-order-migration-20261005/actual-pinned-API-retrieval-v1-01.log` | `5268e2caccf652285c5d9cd4d3a2531283a6cee1eac76ce6add296bd91f69c6a` |
| `runs/online-first-order-migration-20261005/actual-public-types-v1-01-exit.json` | `a204d253760e2151f4d70f43a454c86948417267f5d80264c12abbda351cf7a5` |
| `runs/online-first-order-migration-20261005/actual-public-types-v1-01.log` | `9f3c11379cc5d7f33dcbc455f1c49ad75d5d87fba2a5f3fb99e92b5cf671bb01` |
| `runs/online-first-order-migration-20261005/actual-scoped-graph-v1-01-exit.json` | `b4ab0bbcc29576028a4cabb0a684224d303db650c8dff0686c4c676c7755fa97` |
| `runs/online-first-order-migration-20261005/actual-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-first-order-migration-20261005/blind-packet-v1.md` | `0c48ea772dfffc7df98f06c3f59a4a49206642fb2e7a991e2b3fcfac51c78974` |
| `runs/online-first-order-migration-20261005/blind-receipt-v1.json` | `449f84bc98c3bb21c23774a0ee3b0c8db407c93a69aa586de77b7bffa969f366` |
| `runs/online-first-order-migration-20261005/blind-reconstruction-v1.md` | `3a34df8a3b7cdc854996b838ea89e14e06684b6eed644089a372a27359186f1c` |
| `runs/online-first-order-migration-20261005/compiled-scoped-graph-v1.json` | `976fd7b94807c638855507a80e02421fb48b9f3af43e93d320eca4469f5cb04b` |
| `runs/online-first-order-migration-20261005/draft-fence-convex_gradient_lower_bound-v1-exit.json` | `c200bc868754489f11d956ed4b251d77079bd7eda80bdab4b419a9d6f231bb5d` |
| `runs/online-first-order-migration-20261005/draft-fence-convex_gradient_lower_bound-v1.log` | `9016ed9624ef6ba51da67a4868e96f9bf51b7ed03a44410d376b567b14d57ca2` |
| `runs/online-first-order-migration-20261005/draft-fence-finitePart_eventually-v1-exit.json` | `52f715a2af28b589980fbd2fc968c8945ce7114445b002ef0a96a3bd9d898997` |
| `runs/online-first-order-migration-20261005/draft-fence-finitePart_eventually-v1.log` | `30fa071efd5cdcbbdc40321eb2f17444d9bfa01936be82242aca96d69e1788de` |
| `runs/online-first-order-migration-20261005/draft-fence-theorem_2_7-v1-exit.json` | `3c9210c99a80fc198499e148b4bfa95f684d0353cdf04596d38a3cf4b78a90c6` |
| `runs/online-first-order-migration-20261005/draft-fence-theorem_2_7-v1.log` | `7559c115d2f0fcb741415bb545354709fdc50f59ec9d480e87e43ce87f024159` |
| `runs/online-first-order-migration-20261005/draft-freeze-v1.json` | `f8514dc2b091b047a350c92a02f2f3aae7ff8a1e06626e388fa42001afeb55b5` |
| `runs/online-first-order-migration-20261005/draft-lifecycle-v1-exit.json` | `a0881924c46fb7c0cf384bd23713f99b5deb3c222cbc72a19893020cbfd0c279` |
| `runs/online-first-order-migration-20261005/draft-lifecycle-v1.log` | `ca5578205d9aade2280a4db87c3509fd7a449ee09d61961c6f24eafbf7178501` |
| `runs/online-first-order-migration-20261005/existing-public-retrieval-v1-exit.json` | `69b7b951a87c630c58d4ff9216d1b74452279ccc6686f2ad17f8b0f4f9a9cf5c` |
| `runs/online-first-order-migration-20261005/existing-public-retrieval-v1.log` | `bb1bd5dacd9c2eeca56c1ab7c572b85d260befac276e4d482fd2e7a819cb03fd` |
| `runs/online-first-order-migration-20261005/leaves/actual-public-types-v1.lean` | `2069969deb444882d0559f18845f0da6ce5546992c7d2c7728039f5796d340d8` |
| `runs/online-first-order-migration-20261005/leaves/export-scoped-dependencies-v1.lean` | `d4718787e8e779a67c040e23914b0b977d05c26d81c31bc2fe68c46868b0dc40` |
| `runs/online-first-order-migration-20261005/native-draft-fences/convex_gradient_lower_bound.json` | `9016ed9624ef6ba51da67a4868e96f9bf51b7ed03a44410d376b567b14d57ca2` |
| `runs/online-first-order-migration-20261005/native-draft-fences/finitePart_eventually.json` | `30fa071efd5cdcbbdc40321eb2f17444d9bfa01936be82242aca96d69e1788de` |
| `runs/online-first-order-migration-20261005/native-draft-fences/theorem_2_7.json` | `7559c115d2f0fcb741415bb545354709fdc50f59ec9d480e87e43ce87f024159` |
| `runs/online-first-order-migration-20261005/new-task-v1-01-exit.json` | `9291ac1a566bd0e48c8317ded8770841ab3d44d5400f77f4b25bfd173721cf1b` |
| `runs/online-first-order-migration-20261005/new-task-v1-01.log` | `1ef28cbb4b3504b79e6d6e66f83ca2713217d820f712c02c434c850c5dc549c0` |
| `runs/online-first-order-migration-20261005/original-OnlineConvexFirstOrder.lean.txt` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `runs/online-first-order-migration-20261005/original-OnlineConvexFirstOrderCanary.lean.txt` | `031451c1602cdcb5bd79054c589f6b9c9045d43273b2b1540b77d7bef768af6c` |
| `runs/online-first-order-migration-20261005/prepare-draft-v1-01-exit.json` | `cb6decd93a1ae1022d6f0eec5e68ba8e86e85934968837dd403a2a8daeb60016` |
| `runs/online-first-order-migration-20261005/prepare-draft-v1-01.log` | `a9da8c51700d3cea71ebf00095509ba6e8c1065c004c8a9a40e990e45aa83ea9` |
| `runs/online-first-order-migration-20261005/prepare-draft-v1.py` | `8ce371faaf06832a8bc789073c8c771ba53fa87846b889f422f94ef53d085ddc` |
| `runs/online-first-order-migration-20261005/prepare-source-review-v1.py` | `36c4ecc8815136f36ad96bd14f534cc4652bf25a18a78479a5d0673ed87b7da4` |
| `runs/online-first-order-migration-20261005/proof-obligations-v1.json` | `e45929643a2193050564c25ca1052d2743cd99cffe097117729d5852aa215734` |
| `runs/online-first-order-migration-20261005/ready-dependencies-v1.json` | `d5448357a17e5a1b6e1e4a4c51295ecfa68fe8cb0c01efa1dca2b5d876af869e` |
| `runs/online-first-order-migration-20261005/retained-module-types-v1-01-exit.json` | `cb937647ea8062b7aacda4d38a4a25f79c40399fcd03aa16f703eaa01903aa7a` |
| `runs/online-first-order-migration-20261005/retained-module-types-v1-01.log` | `4a1e659bd1089abe409c47c5093626fce3f984b22c1b2174d12d3120e12525fd` |
| `runs/online-first-order-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-first-order-migration-20261005/source-printed10-11-pdf22-23.txt` | `aa1beb88cb259fd36ccd1131074d331b44cf2d0e8fd768c0c60023881d0071da` |
| `runs/online-first-order-migration-20261005/source-review-packet-v1.md` | `fba587f831532efbfeaf359ee7c4b1a287a2b10b658b0560c19dc6ae0d0a2d9c` |
| `tasks/ONLINE-FIRST-ORDER-MIGRATION-20261005.md` | `f378c3a90053ee8e98e0d6de625bfc65a7a7dc354b863410290bf75c54937610` |
| `tmp/online-first-order-migration-scoped-graph-v1.json` | `976fd7b94807c638855507a80e02421fb48b9f3af43e93d320eca4469f5cb04b` |
| `website/content/chapters.json` | `2f206212e987c98305d909b7f290113636e509dc190f0a2a6def8edec3414252` |
| `website/content/highlights.json` | `5c25596c5e1a3cbcbba3d0846f4fc46063c3b33437d9e55f9647e60ccc59e066` |
| `website/content/readings.json` | `bd1c2402cf14e6879ea08c663846ab5824cab5f4ec615fbf8d5ab4995f6f4868` |
| `runs/online-first-order-migration-20261005/contract-source-inputs-v1.json` | `6b2297375f9de89e0aadcc6701cba0b48010a9168ece0b3b3ff56e693425e018` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
