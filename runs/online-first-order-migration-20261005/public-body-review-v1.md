# Retained first-order public body review v1

**Verdict: accepted-with-explicit-delta**, limited to three actual retained bodies and the actual public canary. No mathematical repair found. Reader corrections remain separate and pending; this is not integrated/package acceptance.

Actor: `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium. No human/external-model review or runtime-model attestation. The body verdict follows fresh term inspection, not inheritance from the contract verdict.

## Binding and evidence

Independently read/hash-checked all 131 fixed input rows, zero mismatch. Independently resolved all 81 previous contract receipt rows using the explicit historical resolution table. The old module row resolves to the exact pre-integration snapshot, not today's changed comment bytes. Comment-stripped token comparison between original and current module is equal; public canary is byte-identical to original. Three actual extracted headers still match frozen statements and hashes. Original source PDF was independently hashed (`cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`) and Theorem 2.7 freshly read directly at printed 11 / physical 23. Its all-y inequality and no-bottom codomain agree with the source terminal. The fresh neutral reconstruction remains consistent with actual imported semantics.

The supplied focused build actually completed 9088 jobs, exit 0, including a shared-root rebuild. Separate direct module/canary elaborations exited 0. The finitePart unused-section-variable warning is not a failed proof. Actual log has 12 named checks/axiom lists, all only propext/Classical.choice/Quot.sound. Three actual safe-guard logs report identical header hashes and retained assumption fragments; guards are not compilation. No new compiler invocation by this reviewer is claimed.

Scoped compiled graph has three actual public proof values and 416 reported direct edges, not a full project or canary export. Independently checked terminal value dependencies on finitePart_eventually, convex_gradient_lower_bound and convexExtended_iff_toReal. The real helper genuinely uses the convex slope API. Raw-reading ancillary administrative evidence does not independently certify all earlier packages.

## Seven-slot body audit per target

### BanditRL.OnlineConvex.finitePart_eventually — accepted-with-explicit-delta

1. Objects: EReal function and canonical toReal conversion, shared complete real inner-product context.
2. Quantifiers: every globally no-bottom f, every x in ambient interior domain, eventually every z near x.
3. Assumptions: only hbot and interior membership are consumed. No convexity/differentiability or wished-for local identity premise.
4. Producer: isOpen_interior.mem_nhds gives a real neighborhood; interior_subset gives f(z)<top; EReal.coe_toReal consumes both top exclusion and hbot z to prove exact embedding equality.
5. Normalization: equality after real embedding, not equality with an arbitrary surrogate.
6. Information/probability: deterministic neighborhood filter, no stochastic or algorithmic claim.
7. Boundaries: local only; bottom cannot pass the conversion guard; top outside the neighborhood is allowed. Ambient, not relative, interior. This is a library representation helper, not an additional printed theorem.

### BanditRL.OnlineConvex.convex_gradient_lower_bound — accepted-with-explicit-delta

1. Objects: everywhere real f, V, x/y and ambient gradient in complete real inner-product E.
2. Quantifiers: every x,y in V under ConvexOn and ambient differentiability at x, not arbitrary y outside V.
3. Assumptions: ConvexOn includes convexity of V; membership of both endpoints and DifferentiableAt at x suffice. No open V, derivative at y or global convexity is assumed.
4. Producer: DifferentiableAt.hasGradientAt supplies the real Fréchet derivative. The explicit affine line x+t(y-x) has derivative y-x at 0. Composing it with f gives the actual directional derivative. ConvexOn.comp_affineMap and the pinned le_slope_of_hasDerivAt compare derivative at 0 with secant 0→1. Endpoint identities and Riesz evaluation turn this into the desired support inequality; linarith only rearranges it. No supporting-plane bound is passed as a premise.
5. Normalization: gradient first, y-x second, coefficient one; no error or residual term.
6. Information/probability: deterministic comparison, no selected-support oracle.
7. Boundaries: x may be on V's boundary provided the derivative is ambient; empty V supplies no endpoints. The real helper does not use finitePart_eventually. General complete Hilbert scope explicitly extends source Euclidean scope.

### BanditRL.OnlineConvex.theorem_2_7 — accepted-with-explicit-delta

1. Objects: convex real-height epigraph of no-bottom EReal f; canonical F(z)=(f z).toReal and gradient F x.
2. Quantifiers: all such f, interior differentiability points x, every ambient y without a membership/finite-comparator restriction.
3. Assumptions: global hbot, epigraph convexity, ambient interior, DifferentiableAt F x only. No extra closedness, boundedness, full-domain, Lipschitz or global differentiability assumption appears.
4. Producer: local identity at x is obtained via self_of_nhds and supplies a finite embedding and x's domain membership. For y in domain, convexExtended_iff_toReal produces actual ConvexOn on that domain and invokes the real helper. Both finite embeddings and coe_add transfer its real inequality back to EReal. For y outside domain, order gives f(y)=top, then le_top proves the original all-y bound. Neither comparator finiteness nor the final inequality is assumed.
5. Normalization: exact EReal support inequality with canonical derivative. The derivative's meaning is local: f and embedded F agree near x. It never asserts that infinite loss globally equals zero or that F is globally convex.
6. Information/probability: deterministic source theorem, not an optimization algorithm or minimizer-existence statement.
7. Boundaries: finite x guaranteed, finite in-domain y guaranteed by global noBottom, outside y top handled explicitly. Empty-interior domains have no admissible x, zero dimension is not excluded. Euclidean source to complete real Hilbert scope is the explicit generalization.

## Canary audit and nonvacuity

The entire public file was read: one definition, eight named proofs, and one anonymous outside-comparator instance. `loss_noBot` splits the actual branch; `loss_domain` proves exactly Ioi 0. `loss_convex` constructs the actual identity-plus-indicator function, proves equality to loss, and uses convex_add_indicator; it does not assume the source convexity conclusion. `interior_one` derives interior membership from this domain. `loss_hasDeriv` establishes actual neighborhood equality to identity around 1, then transfers derivative 1. `loss_gradient` derives gradient 1 from that derivative. `instantiated_bound` applies the actual public theorem to these producers and simplifies the real inner product for every y. `nondegenerate` proves finite distinct values 1 and 2, top at -1, and nonzero gradient. The anonymous instance specializes y=-1 and the actual displacement -2. Thus the example is neither a constant zero-gradient shortcut nor solely an infinity-vacuous test; finite y=2 also gives an exact nontrivial bound. The open domain is unbounded and not closed. Canary acceptance does not assert coverage of every possible degenerate domain.

## Repairs and limits

Mathematical repairs: none. Current leading source comment correctly labels helpers and local representation. Website reader corrections remain pending:
1. Label finitePart_eventually and convex_gradient_lower_bound as library representation/generalized helpers, not additional printed source theorems.
2. Correct the real helper highlight: its everywhere real-valued function, ConvexOn V, x/y membership and ambient DifferentiableAt at x do not require an open V or the extended-real local finite-representation lemma.
3. Qualify the old OGD first_order relationship with its stronger RegularLoss assumptions; distinguish the separately added source-compatible OGD adapter.
4. Keep canonical F(z)=(f z).toReal, global noBottom, ambient interior and local embedding identity explicit together, with all-y/top-comparator scope.

Required later gates: separately recorded combined root/Tests/full harness, current reader/site/registry/contributor, final independent reader review, immutable binding and PR delivery. The focused build's root dependency does not replace that combined acceptance. No whole Chapter 2/book/Goal, other historical migrations, main/live, or package acceptance follows. Historical inputs and previous report remain preserved.

## Exact raw reviewed files

| Path | SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean` | `c7a80e952f6f577c441b92802fc5020fa63b564b75418fb96e29d4f6813020ca` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean` | `2022754e5f0c541b8ca4271231c95713996d9f4ac1f997e3973ec9e6c7bec7c4` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `BanditRLProof/OnlineGradientDescent.lean` | `9300cb2735da9f125e404f78b86509df47fe65a5f4d89abc469e071bdffdb871` |
| `BanditRLProof/OnlineGradientDescentSource.lean` | `627df452453bbdfa2ecf4ddac8b5b85bfd750c74f1db5b81a26e6e20ca2eeec7` |
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
| `runs/online-first-order-migration-20261005/30_lower_worker-body-audit-v1.md` | `d1aca5d5fe6f09d15f0ca2dc007c4619c743565bb40777ee44a34e99ca694d26` |
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
| `runs/online-first-order-migration-20261005/contract-binding-audit-v1.json` | `976305418e016ec06e60bbc6d906331564c2237ddab9a42fb2e7040f93a972dc` |
| `runs/online-first-order-migration-20261005/contract-source-inputs-v1.json` | `6b2297375f9de89e0aadcc6701cba0b48010a9168ece0b3b3ff56e693425e018` |
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
| `runs/online-first-order-migration-20261005/focused-v1-01-exit.json` | `3436cab011c291c066d68eaf243bbcbdd9b877c4d2b442df6a3614d806011819` |
| `runs/online-first-order-migration-20261005/focused-v1-01.log` | `c6c3b604740b6730ea03ac9c4885da2f7fb8a194c0aa0d1ae09e59e750a0b84f` |
| `runs/online-first-order-migration-20261005/historical-raw-supersession-v1.json` | `9697a6b4b134e279b85d011eca97629b561770fe8b251fa07c550f3207a73e6b` |
| `runs/online-first-order-migration-20261005/leaves/actual-public-types-v1.lean` | `2069969deb444882d0559f18845f0da6ce5546992c7d2c7728039f5796d340d8` |
| `runs/online-first-order-migration-20261005/leaves/export-scoped-dependencies-v1.lean` | `d4718787e8e779a67c040e23914b0b977d05c26d81c31bc2fe68c46868b0dc40` |
| `runs/online-first-order-migration-20261005/leaves/pre-integration-BanditRLProof--OnlineConvexFirstOrder.lean.txt` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `runs/online-first-order-migration-20261005/leaves/pre-integration-website--content--chapters.json.txt` | `2f206212e987c98305d909b7f290113636e509dc190f0a2a6def8edec3414252` |
| `runs/online-first-order-migration-20261005/leaves/pre-integration-website--content--highlights.json.txt` | `5c25596c5e1a3cbcbba3d0846f4fc46063c3b33437d9e55f9647e60ccc59e066` |
| `runs/online-first-order-migration-20261005/leaves/pre-integration-website--content--readings.json.txt` | `bd1c2402cf14e6879ea08c663846ab5824cab5f4ec615fbf8d5ab4995f6f4868` |
| `runs/online-first-order-migration-20261005/leaves/public-axioms-v1.lean` | `ca587e12495d7a94007c7b2a4e738ca6dc698e55c915603acc9f8c4d4aa079a9` |
| `runs/online-first-order-migration-20261005/native-draft-fences/convex_gradient_lower_bound.json` | `9016ed9624ef6ba51da67a4868e96f9bf51b7ed03a44410d376b567b14d57ca2` |
| `runs/online-first-order-migration-20261005/native-draft-fences/finitePart_eventually.json` | `30fa071efd5cdcbbdc40321eb2f17444d9bfa01936be82242aca96d69e1788de` |
| `runs/online-first-order-migration-20261005/native-draft-fences/theorem_2_7.json` | `7559c115d2f0fcb741415bb545354709fdc50f59ec9d480e87e43ce87f024159` |
| `runs/online-first-order-migration-20261005/new-task-v1-01-exit.json` | `9291ac1a566bd0e48c8317ded8770841ab3d44d5400f77f4b25bfd173721cf1b` |
| `runs/online-first-order-migration-20261005/new-task-v1-01.log` | `1ef28cbb4b3504b79e6d6e66f83ca2713217d820f712c02c434c850c5dc549c0` |
| `runs/online-first-order-migration-20261005/original-OnlineConvexFirstOrder.lean.txt` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `runs/online-first-order-migration-20261005/original-OnlineConvexFirstOrderCanary.lean.txt` | `031451c1602cdcb5bd79054c589f6b9c9045d43273b2b1540b77d7bef768af6c` |
| `runs/online-first-order-migration-20261005/prepare-body-review-v1.py` | `538bef35b2a01e4d9ef5b7600f5713c77992e2b9f12053a95dc9947bcc38f3f8` |
| `runs/online-first-order-migration-20261005/prepare-draft-v1-01-exit.json` | `cb6decd93a1ae1022d6f0eec5e68ba8e86e85934968837dd403a2a8daeb60016` |
| `runs/online-first-order-migration-20261005/prepare-draft-v1-01.log` | `a9da8c51700d3cea71ebf00095509ba6e8c1065c004c8a9a40e990e45aa83ea9` |
| `runs/online-first-order-migration-20261005/prepare-draft-v1.py` | `8ce371faaf06832a8bc789073c8c771ba53fa87846b889f422f94ef53d085ddc` |
| `runs/online-first-order-migration-20261005/prepare-proving-v1-01-exit.json` | `7224c6292acce25ed6abde343ed442768b0043a27229e094432ada60485c0d9c` |
| `runs/online-first-order-migration-20261005/prepare-proving-v1-01.log` | `713bc5951d861f8568c919674e6e914552a8a2d1979c42d382c04bf9b13976b7` |
| `runs/online-first-order-migration-20261005/prepare-proving-v1.py` | `fc9c166c7bc1e877a60c6b896e1cd7b2a21cf0a5814e482c8f597a3f7ab6011b` |
| `runs/online-first-order-migration-20261005/prepare-source-review-v1-01-exit.json` | `8905baa42fa15d0805e7ae4c7daf99f96eb4bd227d23943f42de8facb3af6718` |
| `runs/online-first-order-migration-20261005/prepare-source-review-v1-01.log` | `20302ca4ec2b582da5011070e77e6a3ce47e90ffe179ae70a7ccfbdd43e185ef` |
| `runs/online-first-order-migration-20261005/prepare-source-review-v1.py` | `36c4ecc8815136f36ad96bd14f534cc4652bf25a18a78479a5d0673ed87b7da4` |
| `runs/online-first-order-migration-20261005/prior-contract-binding-v1.json` | `f9311f3c73960bf4fc1969fd6964143bd667a7e9537c1909bcc15784fed17d98` |
| `runs/online-first-order-migration-20261005/proof-obligations-proving-v1.json` | `8681e86271b16ed8389d2972f4b1e262b2662e3e62a9ffc6bec7647ed132274a` |
| `runs/online-first-order-migration-20261005/proof-obligations-v1.json` | `e45929643a2193050564c25ca1052d2743cd99cffe097117729d5852aa215734` |
| `runs/online-first-order-migration-20261005/proving-lifecycle-v1-exit.json` | `292f7037cb00dc35f32f182de0ba3870c95ffcf46e2fcd63b04c09394bcf77ab` |
| `runs/online-first-order-migration-20261005/proving-lifecycle-v1.log` | `228c1b64dfbfc7ce65dac93d132c66f5452d61f790fea3068d73160b3e064540` |
| `runs/online-first-order-migration-20261005/public-actual-bindings-v1.json` | `da48ac0f17fc006cb3d391078609a7440cfdecdcfe5a62da6cd0372a0f6d071b` |
| `runs/online-first-order-migration-20261005/public-axioms-v1-01-exit.json` | `4c071c7140fa1d366cbe3f22f394f7f19889567e83ded66f04a26c965f5148b3` |
| `runs/online-first-order-migration-20261005/public-axioms-v1-01.log` | `435d1e055ebdecdf499406e9006a4cada03c277e670030c71ed56a60350cfcdf` |
| `runs/online-first-order-migration-20261005/public-body-inputs-v1.json` | `941b28dd03e1f80795df776daa972c0174d570ff49a086ba48052ad21992c3e0` |
| `runs/online-first-order-migration-20261005/public-body-review-packet-v1.md` | `ee701a09e07ef97494a61e9aa2804cb4e198383b08b2aeda080f05ba2584e785` |
| `runs/online-first-order-migration-20261005/public-body-v1-01-exit.json` | `9ff9b20d3f7421d53bffb5724078b1e050de64e4f1ef1a5883c07acbaabc9230` |
| `runs/online-first-order-migration-20261005/public-body-v1-01.log` | `d3db46f06a09725c9aac48c4bbf42e7532a21eca7e61495226d5ea257ed9851a` |
| `runs/online-first-order-migration-20261005/public-canary-v1-01-exit.json` | `4c2b420cf4b3ed3bb5bae147ac7e95b3f01c20bfcb36195f92fd9cd435463371` |
| `runs/online-first-order-migration-20261005/public-canary-v1-01.log` | `1acd4317a866774732fb79574402fd75450a8f8521036fa35a61bcb15138aec4` |
| `runs/online-first-order-migration-20261005/public-comment-delta-v1.json` | `a5abb365e0cb00116f23a2159f2ea7b3d92c4b4efc527b6b9c204b149656e0f3` |
| `runs/online-first-order-migration-20261005/public-named-declarations-v1.json` | `2f0e8e024e3524626dfbd15fafe590e95ae5c7820361441f3d64489ae0fb805b` |
| `runs/online-first-order-migration-20261005/public-safe-guard-audit-v1.json` | `72c1c8a9f4485e154bc64089e5bd4cfc612cfd523b2aec7268aaed5ae7509fce` |
| `runs/online-first-order-migration-20261005/qualify-public-v1-01-exit.json` | `eee603c4fdd9c00633798cc8c1d8ed22027717bec6686dc02c429a144e2dbddb` |
| `runs/online-first-order-migration-20261005/qualify-public-v1-01.log` | `4ef3c53cb77c4f6caa70028e92ff67406d99f53f1aee2da3e6f6020b1a1c1091` |
| `runs/online-first-order-migration-20261005/qualify-public-v1.py` | `9625d48ddabaca66ba91783fe06434c46a69507b535be0c4f881fbec4200dad0` |
| `runs/online-first-order-migration-20261005/ready-dependencies-v1.json` | `d5448357a17e5a1b6e1e4a4c51295ecfa68fe8cb0c01efa1dca2b5d876af869e` |
| `runs/online-first-order-migration-20261005/retained-body-trial-v1-exit.json` | `9f3bd5b66e62f588f3d383b1f8b6503c36901aac230390197175bb1692aaa2b6` |
| `runs/online-first-order-migration-20261005/retained-body-trial-v1.log` | `b1b68c5f76aa02f92321d5170a30070cb4f2495aaa79b2699b5bef16549f1f3b` |
| `runs/online-first-order-migration-20261005/retained-module-types-v1-01-exit.json` | `cb937647ea8062b7aacda4d38a4a25f79c40399fcd03aa16f703eaa01903aa7a` |
| `runs/online-first-order-migration-20261005/retained-module-types-v1-01.log` | `4a1e659bd1089abe409c47c5093626fce3f984b22c1b2174d12d3120e12525fd` |
| `runs/online-first-order-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-first-order-migration-20261005/safe-public-v1-convex_gradient_lower_bound-exit.json` | `88af1857c859b6e2fdfa0768839acb69144c7001cdeace216228ce21b3bfc709` |
| `runs/online-first-order-migration-20261005/safe-public-v1-convex_gradient_lower_bound.log` | `60b471025c09cc5e0808343967ad915d667295240eb7c52415d7ee03a971bb7c` |
| `runs/online-first-order-migration-20261005/safe-public-v1-finitePart_eventually-exit.json` | `95e900d1d7a48a9f9cf6a56b1c989e2051137c556a9eaadafca7c9e4ecba9df5` |
| `runs/online-first-order-migration-20261005/safe-public-v1-finitePart_eventually.log` | `b4e34d0f789daec59fccc8f39e0909adb3f541a08f83b34802eb9c1bc25c1f5f` |
| `runs/online-first-order-migration-20261005/safe-public-v1-theorem_2_7-exit.json` | `ffaaadc33feb848d9a0e0d3dbb378ecbc9c970a0d93023d6c2a4f5a2171d2b54` |
| `runs/online-first-order-migration-20261005/safe-public-v1-theorem_2_7.log` | `dc0c59056fd3dc1ab73cd4eb605fca0283259e235a8608fca37343521d02c778` |
| `runs/online-first-order-migration-20261005/source-contract-receipt-v1.json` | `18fc8d4c2c2c50de32aaa0535685530472c393c27445e6283ff77ae55fefa2e5` |
| `runs/online-first-order-migration-20261005/source-contract-review-v1.md` | `243944e7ed32fa2576050e2a05e0eaa810b8a0311f6bb84f59074848818e7d5a` |
| `runs/online-first-order-migration-20261005/source-printed10-11-pdf22-23.txt` | `aa1beb88cb259fd36ccd1131074d331b44cf2d0e8fd768c0c60023881d0071da` |
| `runs/online-first-order-migration-20261005/source-review-packet-v1.md` | `fba587f831532efbfeaf359ee7c4b1a287a2b10b658b0560c19dc6ae0d0a2d9c` |
| `runs/online-first-order-migration-20261005/stabilized-lifecycle-v1-exit.json` | `c893495061126f6913aaf5bead7f9a09b25e01f68660e324aa9d36181741fe09` |
| `runs/online-first-order-migration-20261005/stabilized-lifecycle-v1.log` | `a1c506f799f10132c413f920dafa893909a940bc19dff936900874a473f3af23` |
| `runs/online-first-order-migration-20261005/verify-public-fences-v1-01-exit.json` | `372a7da88e13a3c9f86901a52897c48608377494de34339821084aa60b75cabe` |
| `runs/online-first-order-migration-20261005/verify-public-fences-v1-01.log` | `69911ad7dc884585d970dce8dbf25764a55820a9d56428be3c8064e459b6a69d` |
| `runs/online-first-order-migration-20261005/verify-public-fences-v1.py` | `9c7250f7218b76a820c5c68616d043dd48b9bf6f3dcc572f70ccb70132e1bbba` |
| `tasks/ONLINE-FIRST-ORDER-MIGRATION-20261005.md` | `f378c3a90053ee8e98e0d6de625bfc65a7a7dc354b863410290bf75c54937610` |
| `tmp/online-first-order-migration-scoped-graph-v1.json` | `976fd7b94807c638855507a80e02421fb48b9f3af43e93d320eca4469f5cb04b` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `website/content/chapters.json` | `2f206212e987c98305d909b7f290113636e509dc190f0a2a6def8edec3414252` |
| `website/content/highlights.json` | `5c25596c5e1a3cbcbba3d0846f4fc46063c3b33437d9e55f9647e60ccc59e066` |
| `website/content/readings.json` | `bd1c2402cf14e6879ea08c663846ab5824cab5f4ec615fbf8d5ab4995f6f4868` |
