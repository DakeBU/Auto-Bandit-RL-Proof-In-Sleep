# Distinct source CONTRACT review — differentiability migration

Verdict: **accepted-with-explicit-delta**, contract stabilization only. No mathematical target repair is required. This is a distinct automated reviewer task `/root/source_reviewer`, requested GPT-6 Astra / medium; no independent human, external-model, or runtime model attestation is asserted. The reviewer has prior project context; the new decoder has its own restricted packet, rather than this reviewer being claimed history-free.

I independently recomputed all 273 fixed input raw hashes: zero mismatches. The inventory itself is additionally bound below. Binary inputs are byte-bound; the original physical page 29 image was actually viewed. Semantic scrutiny concentrates on the actual source page, complete definition, eleven declarations/scoped types and bodies (contradiction checks only), imported APIs, neutral reconstruction, old canaries, planned diagnostic headers, and selected reader. Auxiliary scripts, historical records and snapshots are integrity/provenance inputs, not newly accepted mathematical claims.

The original PDF raw SHA-256 is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Printed page 17 / physical PDF page 29 states convexity, finiteness at x, the complete differentiability/singleton equivalence and gradient identity. Neither properness nor interior nor closedness is an added source terminal premise. The adjacent introductory prose must remain in this convex scope.

## Full definition and source interpretation

`SourceDifferentiableAt f x` means existence of a real function h whose real embedding agrees with f eventually in the ambient neighborhood of x, together with real Frechet differentiability of h at x. Its actual @type has NormedAddCommGroup and real InnerProductSpace, but no FiniteDimensional binder. All eleven theorem interfaces retain finite dimensionality. This is a precise interpretation of extended-real differentiability, not differentiation within the effective domain. It allows top away from the neighborhood, and excludes bottom/top within the germ. Equality at x follows from the genuine neighborhood; it is not punctured agreement.

The generic global support definition itself also accepts improper functions. That broad definition does not silently add source assumptions: singleton plus finite x yields nowhere-bottom through the actual support inequality; forward finite germ plus convexity yields affine contact and hence nowhere-bottom. Properness and ambient interior can therefore be derived when used. Effective-domain membership alone is not a finite-real witness when bottom is allowed; the interfaces here retain appropriate guards. The gradient companion quantifies over every representative and supplies existence as well as uniqueness. The source Euclidean space is represented by an abstract finite-dimensional real inner-product space; completeness is derived and dimension zero remains allowed.

A real singleton indicator at 1 is a decisive planned diagnostic: its toReal is zero globally despite infinite values elsewhere; its ambient germ fails, while all real slopes support it at 1. These three headers are mathematically appropriate but their empty by slots are parser previews, not proofs. Existing six canaries include constrained interval interior, nonzero quadratic slope 2, the full reverse implication, and boundary slopes 0 and -1. No new canary body is accepted here.

## Eleven target comparisons

### `BanditRL.OnlineConvex.subgradient_norm_le_lipschitz_ball`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: All f,x,r,K,g; every finite point of a positive ball and every given global support.
- **assumptions**: r>0; K:NNReal; actual finite real witnesses throughout ball; LipschitzOnWith of toReal on ball. No convexity or global noBottom premise.
- **conclusion**: norm g <= K.
- **constants**: Positive r; nonnegative K includes zero.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: g=0 and K=0 allowed; positive ball prevents empty-neighborhood shortcut.

### `BanditRL.OnlineConvex.subgradients_locally_bounded`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every convex nowhere-bottom f and ambient-interior x; produces r,K uniformly for every nearby y and every support.
- **assumptions**: Global noBottom, convex epigraph, ambient interior domain.
- **conclusion**: A positive ball and finite NNReal uniform norm bound for all supports.
- **constants**: Existential r>0,K>=0, not pre-supplied desired bound.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Does not itself assert existence or uniqueness of supports.

### `BanditRL.OnlineConvex.subgradient_limit_of_continuousAt`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every index type, nonbottom filter, convergent xs and gs, eventually global supports.
- **assumptions**: NeBot l; global noBottom; ambient-interior x; continuity of finite part; both limits. No convexity assumed.
- **conclusion**: Limit g is a global support at x.
- **constants**: No quantitative rate or boundedness parameter.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: NeBot excludes empty-filter false limits; top comparison points handled by order, not fake real values.

### `BanditRL.OnlineConvex.singleton_subgradient_tendsto`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every nonbottom filter and support selection eventually along xs converging to x.
- **assumptions**: Global noBottom, convexity, ambient interior, singleton support at x; no assumed gs limit.
- **conclusion**: gs converges to singleton member g.
- **constants**: No convergence rate.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Finite-dimensional compactness is substantive; not asserted in arbitrary infinite dimensions.

### `BanditRL.OnlineConvex.singleton_subdifferential_interior`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every f,x,g with singleton full global support and finite f(x).
- **assumptions**: Convexity plus finite real witness and singleton equality only.
- **conclusion**: x belongs to ambient interior of effective domain.
- **constants**: No radius input.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Not relative interior; no properness, closedness or interior supplied; zero-dimensional ambient allowed.

### `BanditRL.OnlineConvex.singleton_subdifferential_hasGradientAt`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every finite x and singleton member g.
- **assumptions**: Convexity, finite witness, singleton equality only.
- **conclusion**: Actual HasGradientAt f.toReal g x.
- **constants**: Full Frechet little-o residual, not directional derivative or quantitative rate.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Use of toReal is justified by derived neighborhood finiteness; no naive boundary conversion.

### `BanditRL.OnlineConvex.sourceDifferentiableAt_regular`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every f,x with an ambient real differentiable representative germ.
- **assumptions**: SourceDifferentiableAt only, no convexity or global noBottom.
- **conclusion**: Eventually real-finite values, ambient interior domain, differentiability of canonical toReal.
- **constants**: Neighborhood/filter rather than fixed radius.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Does not alone prove global properness; infinity may occur away from neighborhood.

### `BanditRL.OnlineConvex.subgradient_eq_gradient_at_interior`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every given global support g at x.
- **assumptions**: Global noBottom, ambient interior, differentiability of toReal. Convexity absent.
- **conclusion**: g equals canonical gradient.
- **constants**: Exact identity.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Conditional uniqueness is not existence; it is not the whole source theorem.

### `BanditRL.OnlineConvex.theorem_2_22_gradient`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: For EVERY differentiable real h agreeing with f near x.
- **assumptions**: Convex f and finite f(x), eventual representative agreement and differentiability of h.
- **conclusion**: Whole global support set equals singleton gradient h x.
- **constants**: Exact equality, no approximation.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: No added proper/interior/closedness; representation independence; top outside neighborhood allowed.

### `BanditRL.OnlineConvex.theorem_2_22_forward`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every convex f and finite x having a genuine ambient differentiable germ.
- **assumptions**: Convexity, finite real witness, SourceDifferentiableAt.
- **conclusion**: Existence of g with whole global support set {g}.
- **constants**: Exact singleton.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: Forward direction only; companion and reverse remain required, and are separately present.

### `BanditRL.OnlineConvex.theorem_2_22`

Contract verdict: accepted-with-explicit-delta.

- **objects spaces**: Finite-dimensional real inner-product E; f:E->EReal; global SourceSubdifferential and real-height epigraph. CompleteSpace is derived, not an additional supplied class.
- **quantifiers**: Every convex extended-real f and every finite queried x.
- **assumptions**: Only convex real-height epigraph and finite real witness, besides ambient finite-dimensional real inner-product classes.
- **conclusion**: SourceDifferentiableAt iff existence of g with full global support set {g}.
- **constants**: Exact iff, no asymptotic parameter.
- **information probability**: Deterministic mathematical assertion; no algorithm, causality, probability, measurability or executable support oracle.
- **boundaries**: No proper/interior/closed/lsc/bounded premise; dimension zero included; no relative-domain derivative.

## Producer and readiness contradiction checks

The retained reverse chain does not consume the desired derivative. Boundary separation yields a nonzero normal and a second global support; singleton forces ambient interior. Local finite-part convexity gives uniform support bounds; a nonbottom-filter closed-graph limit and finite-dimensional compact ball identify cluster points. Actual neighboring supports then squeeze the full Frechet residual. The forward route uses finite-neighborhood contact, obtains nowhere-bottom, produces the global gradient support via the first-order theorem, and proves any support equals it by a local minimum derivative and Riesz injectivity. These observations support consistency of the contracts; they are not this round's separate BODY acceptance.

Actual API outputs preserve the supporting functional at closure, finite-neighborhood contact, interior support existence, first-order all-ambient inequality, local Lipschitz, unique cluster limit and little-o interfaces. The readiness graph has twelve nodes (eleven proofs and one full definition), 1880 direct references and fourteen required value-call pairs. It is not a full-library or canary graph. The neutral reconstruction correctly distinguishes every-representative identity, NeBot filters, supplied versus derived interior, and the absence of main properness. No contradiction was found.

Preparation v1 failed on the guessed firstorder directory; v2 failed on a missing task constant. Both original failures are retained; v3 is authoritative. Neither failure is a mathematical proof repair. Existing retained elaboration and @type evidence do not certify the three planned tests or future combined gates.

## Required reader corrections / integration checks

These are publication obligations, separate from mathematical repairs; several are already partly stated in the current reader and must remain explicit through integration.

1. Preserve one printed Theorem 2.22 anchor and distinguish eleven retained proof declarations plus one definition from eleven source results; report zero new production mathematical nodes.

2. Keep the complete ambient local-real representative definition visible, including every-representative gradient identity; distinguish it from toReal alone and relative-domain differentiability.

3. Explain the three planned singleton-{1} diagnostics as unproved until actual body gates: toReal is identically zero and smooth, genuine ambient germ fails, and every real g is a global support. Do not generalize the real singleton-empty-interior claim to dimension zero.

4. Clarify main versus helper assumptions: properness/interior are derived in the main directions; noBottom, NeBot, finite ball, local Lipschitz and continuity hypotheses belong to their particular helpers, not the source terminal.

5. State actual finite-dimensional real inner-product scope, derived completeness and permitted dimension zero. Do not imply an arbitrary infinite-dimensional theorem or an empty ambient carrier.

6. Explain actual reverse normal perturbation, bounded-support compactness and Frechet residual; proof-internal support selection is not an algorithm or computational oracle. Forward contact and global first-order support are actual producer dependencies.

7. Keep source introductory differentiability prose under the convex theorem hypothesis; do not claim every differentiable nonconvex function has a unique global subgradient.

8. Refresh candidate/readiness status only from subsequent actual gates: current twelve-node/1880-reference graph and fourteen value pairs are scoped readiness, not full/canary export or final package acceptance. Keep six old canaries versus three planned diagnostics separate.

9. Preserve Theorem 2.23 and remaining Chapter 1/2/book obligations; a four-declaration teaching route is not exhaustive proof dependency coverage or chapter completion.

## Limits and remaining gates

Required mathematical repairs: none. Contract-only acceptance does not accept retained bodies afresh, new diagnostic bodies, public integration, root/Tests/full harness, named kernel audits, current registry/site/visual/immutable binding or PR delivery. Those phases remain separate. One printed theorem, eleven retained proofs, one full definition and zero new production mathematical nodes is the scope. Chapter 1 migration, Chapter 2 incomplete/null total, adjacent sum rules and the whole active book Goal remain open. No merge, deployment or retirement is certified.

## Exact raw input receipt

| Path | SHA-256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean` | `d3eef88863cfdb6c1169b957335ff87ff6e06116f45dae96ad0e220a2f5da0da` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean` | `ec09dfe037c654dc65051e22fd9e1d76055ef340089a631c304b700d0406109e` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Continuous.lean` | `fc5abf90af9414961438d0001a0e2766c397d879422338dac9febae6fe97b0f2` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean` | `6e25613a0a200590fe3510cb618efd1addac49928d5b6361c2be2cf3951908c3` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean` | `5725482a0b5c23d49eb1168550d084f8f1fb09d9f514eeb97deecc8eccd81175` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineConvexBarycenter.lean` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `BanditRLProof/OnlineConvexMinorant.lean` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientDifferentiability.lean` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `BanditRLProof/OnlineSubgradientInterior.lean` | `72cf2057e9dee7a1e8c4f92bb7878cffbb9b7603ff6afbac4f90ee5af11db9d2` |
| `MANIFEST.md` | `24200d35209b133039415ade3e5fa167ae4e99e744acc818a39d6f3023fba618` |
| `Tests.lean` | `aa0f1f04e1264a90d6006957a7c219640afc36359712d4ce44ce4514f8240755` |
| `Tests/OnlineSubgradientDifferentiabilityCanary.lean` | `078d21522145b948421a81eb99f66298fb141688858dad3502572fba703b0106` |
| `conversion-windows/ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007.md` | `f72bc5d73138e488f7814cf726f706ffed3235f26c12a534eb65f36b39e554ab` |
| `docs/contracts/online-barycenter-migration-v1/integral_mem_convex_finiteDimensional-header.txt` | `41b6ac00a399c7563f8649aff881d221bf00368a95d564c645da5345601d1f24` |
| `docs/contracts/online-barycenter-migration-v1/integral_mem_convex_finiteDimensional.json` | `4b794c9bbd3e79c648f94315c9f0bcb154df988ecd3cbea80d99007f94e6d923` |
| `docs/contracts/online-barycenter-migration-v1/scoped-contexts.json` | `b28181ee60e5a9d4bd636f71fac87826897f9822e58b60d674f3fe2132f84634` |
| `docs/contracts/online-barycenter-migration-v1/source-card.json` | `7c219502f544c670ab1b7f5e81628bb7b1506cd068797aa6e8e147e5d16c24d7` |
| `docs/contracts/online-barycenter-migration-v1/source-intent.md` | `a448cb43a6ef2631f179e28eb26174f2644dbbbca50add65b3c07f831e7871ec` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_ae_eq_mean-header.txt` | `f2c7ff1bb073e956a2f840829843f3e62002f255f2c88df8f15bbddcc90022ca` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_ae_eq_mean.json` | `a0757c9f4feed80e519618d6aaacb2830f8714c25cc2e9c9b00b018e8e823ad0` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_at_closure-header.txt` | `04203cec9cdcdd7717909c970a5f8bad28e068ec722322ff237a0c69f76d1811` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_at_closure.json` | `d4fa06954fbe16bc5ae924a222e9c284205fc591f6242ce68e43be6c6354ef79` |
| `docs/contracts/online-first-order-migration-v1/context.lean.txt` | `dd633c0cd797172f8c7d517a08ace6962d285b0d3f346da750dfee92524cd878` |
| `docs/contracts/online-first-order-migration-v1/convex_gradient_lower_bound-header.txt` | `f201a63268760cdc170d78454d08fc18806217e36b772b8076de594074d779e5` |
| `docs/contracts/online-first-order-migration-v1/convex_gradient_lower_bound.json` | `6b544f0d44662e8c5510fcb5a9e5e771bd6e090e88b7d7da9b448f71dbfc81c6` |
| `docs/contracts/online-first-order-migration-v1/finitePart_eventually-header.txt` | `a953a3cf29dc9f5f23970146271df0788776200a4bf57819be2015aec301aef5` |
| `docs/contracts/online-first-order-migration-v1/finitePart_eventually.json` | `231331421ed3509d2f0ee4e0beaedf1dd8d51f6176d4d3aea6fdcaa78cbaa7c7` |
| `docs/contracts/online-first-order-migration-v1/source-card.json` | `f9eac10df8a7d327f33ad4822c8d2e2e034377faddada05bf0f85f317beeba2c` |
| `docs/contracts/online-first-order-migration-v1/source-intent.md` | `ecc0be46a013737c93b824d56bce2ff11b34c9e3a54ab2f82c630a79b06421ae` |
| `docs/contracts/online-first-order-migration-v1/theorem_2_7-header.txt` | `d2a4b7f0f72360bd91d34a96065d0459d0612d60fde42b256e2bacc3acebd7eb` |
| `docs/contracts/online-first-order-migration-v1/theorem_2_7.json` | `00d37ea466eb85d3901279734f73058caa9f95330d462bc9a8399c5993e5a3c6` |
| `docs/contracts/online-minorant-migration-v1/affine_minorant_of_domain_interior-header.txt` | `e16cefb3e30853d0df6ec288ce03a4758d780c6a9a2f8a86706ac69c22b5572e` |
| `docs/contracts/online-minorant-migration-v1/affine_minorant_of_domain_interior.json` | `dd9b877532e0a48c63b85c836cb6e44335e7da0825aeddf229b41cc5101ea388` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_domain_interior-header.txt` | `fda28878ba9fa50df397d14a5e84a77633b65ff0eae910d7400d9117ffa14411` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_domain_interior.json` | `5db5c71696ae56c4503ad5676f7e508d5b312920624d6b582c05c0a6937a8cc3` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_finite_neighborhood-header.txt` | `ee5209701c49ae62f99ee486fd7770167a64f2de81877feb1c03edbaff66bbb2` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_finite_neighborhood.json` | `4f824209315e12bc1bb44e352e92a4fccce4ddfb573dbdfc9235333cc862a025` |
| `docs/contracts/online-minorant-migration-v1/convex_affine_minorant-header.txt` | `d15bc60b7b96d4ecd80fe67518dd4fabfdda6aace2dcb240b0dfb11af38a6b7f` |
| `docs/contracts/online-minorant-migration-v1/convex_affine_minorant.json` | `7599f9bcb7e91849b9fed7a2296f58c4edd2897e624712babafe60f25eb19d37` |
| `docs/contracts/online-minorant-migration-v1/scoped-contexts.json` | `3ccb611c3c7f88afdcd9a8dd8622df32391751715e3aaabd4a68e8e164566273` |
| `docs/contracts/online-minorant-migration-v1/source-card.json` | `db310db9797d1f84248fc7b0acd4cc020ae4d653d09d9401ead4bbdc79c2b9e8` |
| `docs/contracts/online-minorant-migration-v1/source-intent.md` | `78f3c4ee825b9a11b7b07e479cd7577d3d117b54478da8d4d8e309ad08ca025d` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/dependency-DAG-v1.json` | `9d9c6af7e1b7a3d036b6c73c9314fa03fcb80ffbc2ae377cd917d5103ed6a70e` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/headers.json` | `6be24efdabc55ce4a25d4afed47df44f446bd160a9d8a9cac3ee766ba64adea6` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/new-canary-terminals-v1.json` | `16d6fff3a655810b9901714deef09cabdae3ca5e96dcc03d4005a32690ecf96e` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/scoped-contexts.json` | `22415309433d0e8465553ab3b05d0f893726022fde0b9d7fdcdcd8ef72410c77` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/source-card.json` | `370156fa9c3b224fa93ebbe74b05fa8c6471e8b1a191871b90754e2a180ad836` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/source-intent.md` | `1a730fc9eae224025dfc48b2ff603bd858aa9111ba6630b7ec5b295e14d4addf` |
| `docs/contracts/online-subgradient-differentiability-public-v1/integration.json` | `788600f455b28ddc95a8299f60a1bdec558171802467a92e5dfe2b3b4f212223` |
| `docs/contracts/online-subgradient-differentiability-public-v1/singleton_subdifferential_hasGradientAt.json` | `5452051a53c953cf723a91bb012113ff50631abc8f821c464b648e6591ea8a96` |
| `docs/contracts/online-subgradient-differentiability-public-v1/singleton_subdifferential_interior.json` | `f0675e1188dd7a71a4603b1a9a27d7b064794a13be6eb844c5b06239f468babe` |
| `docs/contracts/online-subgradient-differentiability-public-v1/singleton_subgradient_tendsto.json` | `140797673857bc71958df5901136a8812302a401557517600ceee43faed48d4e` |
| `docs/contracts/online-subgradient-differentiability-public-v1/sourceDifferentiableAt_regular.json` | `609bf9a7c5f16da9dd655a06219faf8426c8213d3f3d2a549f8bb2c063cef771` |
| `docs/contracts/online-subgradient-differentiability-public-v1/subgradient_limit_of_continuousAt.json` | `c1141cb199d9b017ce01c96b12b46c91aaf058f1eb036e2b0262c9e354de0962` |
| `docs/contracts/online-subgradient-differentiability-public-v1/subgradient_norm_le_lipschitz_ball.json` | `50fb7974d0095b689f992cca91dd0e96b0e9745bc82cd63dad96e2ee8ebe7f9e` |
| `docs/contracts/online-subgradient-differentiability-public-v1/subgradients_locally_bounded.json` | `44d2512337a31bea70027dc39f86c2f26639e0af422d6e42e68171e1c9447ab6` |
| `docs/contracts/online-subgradient-differentiability-public-v1/theorem_2_22.json` | `b10bb4207121e3b8214c741fbe3673b71189fad2bd824ce4593fb64d81c22c3e` |
| `docs/contracts/online-subgradient-differentiability-public-v1/theorem_2_22_forward.json` | `6627ffde25c51d0505da9ddf55227bb235767ec8d8c64b199d8f41cc7abc67af` |
| `docs/contracts/online-subgradient-differentiability-public-v1/theorem_2_22_gradient.json` | `6f473c75286b83437cf1b3646162f563b9609eb933ca49cbd6bbdfa5624a71d4` |
| `docs/contracts/online-subgradient-differentiability-v2/closed-graph-header.txt` | `f392f01d6ab01909d659ccea479110ea69c2318d2a0bddad9906a97a465dfaac` |
| `docs/contracts/online-subgradient-differentiability-v2/context.txt` | `0638affef80952cde5777ece5cdcf2fa8ec46efd2c3ada2c670de2b0df8f5348` |
| `docs/contracts/online-subgradient-differentiability-v2/continuity-header.txt` | `7f1ac2d804d06287afacb7bb66cdf201cf82a7df996d3a3b492c33418b0b7af7` |
| `docs/contracts/online-subgradient-differentiability-v2/contract-manifest.json` | `f33c4e9c593d4bfec82f8d03df348654ab1e207032daff31aa2daf92712e970f` |
| `docs/contracts/online-subgradient-differentiability-v2/contract.md` | `9a44687bb43edd524ec3dcbca227410d507295681d19ca731463ffb03a9d64fe` |
| `docs/contracts/online-subgradient-differentiability-v2/forward-header.txt` | `8d57ee05bec2c84bfa50f883c9f7dae35aa3beffa29e099884f2d2d359f92705` |
| `docs/contracts/online-subgradient-differentiability-v2/full-header.txt` | `7029e22ec2d7e84879a3c97109e5d17709372628fa516b309c2d5391ef5e94b9` |
| `docs/contracts/online-subgradient-differentiability-v2/gradient-header.txt` | `fd8f6b3d690b24692f0ab8462f8ab9a842b9381c96717da81c217ecf9254381e` |
| `docs/contracts/online-subgradient-differentiability-v2/interior-header.txt` | `051a7e1df02b4405a9dcebc5a48a586aee4a9f909ff862e28fb5ea4deb66f9dd` |
| `docs/contracts/online-subgradient-differentiability-v2/local-bound-header.txt` | `f490845dd72bc3039d5738dfc11c85d363869aefd74471e060a311441ee20347` |
| `docs/contracts/online-subgradient-differentiability-v2/local-regularity-header.txt` | `af64d78681612e43dbf1f52d95a6d634b581fa8039e52438048103fdf44a8f18` |
| `docs/contracts/online-subgradient-differentiability-v2/norm-bound-context.txt` | `7346065759b2c2edd3e3a2a0ae2056b75077f4026f80dd5c7acc99a4b035755c` |
| `docs/contracts/online-subgradient-differentiability-v2/norm-bound-header.txt` | `a338e1fa99a9c19ef13a936d71cbd7743d6ecad6a8a87930d91ec969700380fd` |
| `docs/contracts/online-subgradient-differentiability-v2/reverse-gradient-header.txt` | `33050b4367a30a1c4b0dc81810782256bfcb36ad43f6319f61f9da15eb1df835` |
| `docs/contracts/online-subgradient-differentiability-v2/singleton_subdifferential_continuousAt.json` | `5012fa9d0487c5f51c563cda62ea96362b625347b97cb0f5fab6f69c447bb254` |
| `docs/contracts/online-subgradient-differentiability-v2/singleton_subdifferential_hasGradientAt.json` | `ee93ee890ef88e2e30a60d3302c8926fcf161fe0ff9676585977c1563af8b61e` |
| `docs/contracts/online-subgradient-differentiability-v2/singleton_subdifferential_interior.json` | `95eb77ddcc0553334048ea32b02a3f583b48e14d1dfb5abba5cc38892df6a7b4` |
| `docs/contracts/online-subgradient-differentiability-v2/singleton_subgradient_tendsto.json` | `daad0bd72cd78cc7d4e01217f35a7aa2ce065c17b9f52f928771bc9ec689718a` |
| `docs/contracts/online-subgradient-differentiability-v2/sourceDifferentiableAt_regular.json` | `078a740df46c0ed7c9dcd419ec91ec14e1b5cf83fcb08300b437b8a1ff106bcf` |
| `docs/contracts/online-subgradient-differentiability-v2/subgradient_limit_of_continuousAt.json` | `b261d84b0af15b23b04f9ac35ea899273bc4b859d924394398b63fed32d136b0` |
| `docs/contracts/online-subgradient-differentiability-v2/subgradient_norm_le_lipschitz_ball.json` | `989214d05992add7eda747421a578017702034ac0c7dc16fc072d7ee3d8f63fe` |
| `docs/contracts/online-subgradient-differentiability-v2/subgradients_locally_bounded.json` | `6151ac32dcb63bbbf27f22c2f3fbd13450309cbddf9cf8a26084a91cb3d31809` |
| `docs/contracts/online-subgradient-differentiability-v2/support-tendsto-header.txt` | `cf18fe3243075af16f8d3617285b7007960e5e58b12ba9324074606668787fbd` |
| `docs/contracts/online-subgradient-differentiability-v2/theorem_2_22.json` | `0d3fcb39c2b52f111b2e815db711542022974c0d26c09c8c55fdad2d1a0402be` |
| `docs/contracts/online-subgradient-differentiability-v2/theorem_2_22_forward.json` | `aec87f1f886a0deec15705223f68a618676417e61432d77e7a2da7adea48cfa8` |
| `docs/contracts/online-subgradient-differentiability-v2/theorem_2_22_gradient.json` | `72e70b0279650067ab6c093f704ad1f56777a86d42baab20c855f5e177f78962` |
| `docs/contracts/online-subgradient-interior-migration-v1/canary-headers-v1.json` | `7c4a817a05bd8d2061e9de64ab1b47065d23f2958528fb6bbde4552d355e01e2` |
| `docs/contracts/online-subgradient-interior-migration-v1/dependency-DAG-v1.json` | `d93bb5987013b55f996672264284e36201eeeb70139ca6ddc74ed4d1988ef523` |
| `docs/contracts/online-subgradient-interior-migration-v1/headers.json` | `50dab3f99b37bff7e3bc757d00aaf54f531e340dce515685f1c7d04bb426b900` |
| `docs/contracts/online-subgradient-interior-migration-v1/planned-canary-headers-only-v1.lean.txt` | `55cd228f09df9961fb966cf6e1a8b14cae7e32eba1d8f49092a6289ffd0086f4` |
| `docs/contracts/online-subgradient-interior-migration-v1/planned-headers-only-v1.lean.txt` | `35a9fa661f36c0222af4ccc262f06c06cb79d5608a54f11a5f9173bca3e41902` |
| `docs/contracts/online-subgradient-interior-migration-v1/scoped-contexts.json` | `1331836519e6588247feece22bfdfaed12ca1e199fac933a814c0ac9352a3b59` |
| `docs/contracts/online-subgradient-interior-migration-v1/source-card.json` | `ee4c6abc77f9039d6a34d291fcee7b54e5c5142631625d7c60a46202ae413651` |
| `docs/contracts/online-subgradient-interior-migration-v1/source-intent.md` | `92e6bf6e817336f96790c6cbe3948f2d3f94cd7642b6af480818a2a4e5d4caf4` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007.md` | `f72bc5d73138e488f7814cf726f706ffed3235f26c12a534eb65f36b39e554ab` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-barycenter-migration-20261005/accepted-decision-v1.json` | `5f23be0e6b4dc407d991084751dacadd21379b2755d84118e5150dd5c28388b9` |
| `runs/online-barycenter-migration-20261005/pr-delivery-v1.json` | `a2cbf7ccb2f87d1ddd164f033f307959023b417e0dbc473ca94a40155a696a97` |
| `runs/online-first-order-migration-20261005/accepted-decision-v1.json` | `2b5d59dbc78014ffc8c85e6fb333d9879cd833a0dba1223b46be59678abc4a8f` |
| `runs/online-first-order-migration-20261005/pr-delivery-v1.json` | `e5b057ceace37a4454366b4a2197dc481ce3fdf0b5f02755c79be51c0246acce` |
| `runs/online-minorant-migration-20261005/accepted-decision-v1.json` | `d753bc6f1fb4e3e007b7e532e529fc79feef1e7dea0e626ecea3a1f60169a6f4` |
| `runs/online-minorant-migration-20261005/pr-delivery-v1.json` | `da526e8bbd9dab512bc5020a6d0c1e8e08e63321d83c76abf382e27c386b5463` |
| `runs/online-subgradient-differentiability-migration-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-subgradient-differentiability-migration-20261007/00_context.md` | `f924c93b99b34ed0912a93b2449ad525f059523a0c28468fbf0219efc5ad3c9f` |
| `runs/online-subgradient-differentiability-migration-20261007/10_upper_director-v1.md` | `8a503f0ad6ed8029a45cdef9561adc2f65b439a0650623dbe2ec034d1b277b81` |
| `runs/online-subgradient-differentiability-migration-20261007/20_architect-v1.md` | `9fb3aff8a138fcd49b93c7dbfae2bb56b53359f018b7cc075ce987142f7c8ebc` |
| `runs/online-subgradient-differentiability-migration-20261007/actual-types-v1-01-exit.json` | `e12220fa054febd525738eb60024146ba8c2ac18abe21e723c79f6bbadbe7166` |
| `runs/online-subgradient-differentiability-migration-20261007/actual-types-v1-01.log` | `4deacc429c3a881f02a90dc5d24390e6ec8a652f8573929d271b64905e6f9528` |
| `runs/online-subgradient-differentiability-migration-20261007/authoritative-private-workflow-binding-v1.json` | `e15a1e7890dfc844960403df526b5814b605704c21b0c28c72be114547b5f2be` |
| `runs/online-subgradient-differentiability-migration-20261007/blind-packet-v1.md` | `9bfed496da1d70d4ab6fa4e55328e60a1cfe1a1cd32fca38f5400eba04df71c7` |
| `runs/online-subgradient-differentiability-migration-20261007/blind-receipt-v1.json` | `4e370fa40f0e59d1fa3494d1b0a54e14c8fcb0bed2ae9763e5f9d5056b154a0f` |
| `runs/online-subgradient-differentiability-migration-20261007/blind-reconstruction-v1.md` | `828939d109a4d65efc5107c545fb82da8dd3374df1e07f7ed505b255d31ce3f5` |
| `runs/online-subgradient-differentiability-migration-20261007/bootstrap-generated-before-use-v1.json` | `a37ec4199af5f3fb9398f91590c0a12269fd22c69764936f8e3f13e7c6895623` |
| `runs/online-subgradient-differentiability-migration-20261007/bootstrap-v1.py` | `8806154054b8f10553ec4154d85b125a1916c8866b8673286b0c7af9389cd004` |
| `runs/online-subgradient-differentiability-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `cb097e2372469dbf1b8b2a453004d2a61a15148839269968bf382572b86336c1` |
| `runs/online-subgradient-differentiability-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-differentiability-migration-20261007/compiled-ready-graph-v1.json` | `0bb3e522ff38b410595a5fcdc66f636a0402a2198d773d1bed3299d1c32cad17` |
| `runs/online-subgradient-differentiability-migration-20261007/compiled-ready-graph-v2.json` | `0bb3e522ff38b410595a5fcdc66f636a0402a2198d773d1bed3299d1c32cad17` |
| `runs/online-subgradient-differentiability-migration-20261007/compiled-ready-graph-v3.json` | `0bb3e522ff38b410595a5fcdc66f636a0402a2198d773d1bed3299d1c32cad17` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-singleton_subdifferential_hasGradientAt-v1-exit.json` | `77c9263e907ccc4078c1a6a3e2ce92449dc970ba16b252d9c1a72d446c1cedff` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-singleton_subdifferential_hasGradientAt-v1.log` | `c65db84c014b12521e8e11907f4e2f691721f7553260aab3dd5b03741bfe9ca9` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-singleton_subdifferential_interior-v1-exit.json` | `0f805be9053b6eded9bbef888156b21d2fde42ab321cdc37150cbff223120adb` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-singleton_subdifferential_interior-v1.log` | `86f557abfb7e7ec7c91fa4d684c1cc6f62ca34720a55333b9637f3d32ad0c2e3` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-singleton_subgradient_tendsto-v1-exit.json` | `841586daf4a98c358a77c2bb722448c09899a24d09efe2f83e055278e5406957` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-singleton_subgradient_tendsto-v1.log` | `ce4c843ebc834cf2068209dcddebcb18966585aa758e986e3f325cd2b8f2a0d9` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-sourceDifferentiableAt_regular-v1-exit.json` | `0a4a3c7b03b7785384fa374d6c353e11aeb16c0c1e92e6d52129f71961b5c775` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-sourceDifferentiableAt_regular-v1.log` | `198589c77b0bc2b9bc909ef6c05ab11789da85419c16a3c9f5c5a56c757abc70` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradient_eq_gradient_at_interior-v1-exit.json` | `72665cd1521e39656449b0ff4db2d1933984d1b3a2523eb3937a1ff8ed9bbd97` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradient_eq_gradient_at_interior-v1.log` | `179e4dfab03f59ec9304f8772c580d2edf72bd8a0351cc460bd2af38bf5cffe2` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradient_limit_of_continuousAt-v1-exit.json` | `1e2f73646aefbfdbb7275f6a93535aefc9ccab72ca8ba179cd5c8abbf1e51858` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradient_limit_of_continuousAt-v1.log` | `85144f4e4a369dec3d84c757036388ca019d31bfb13a4b6b0501853f36c16b61` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradient_norm_le_lipschitz_ball-v1-exit.json` | `6ff82041215fd23f4b2220c559f309fbf043a058665ca9d346545612841b42e2` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradient_norm_le_lipschitz_ball-v1.log` | `9df18c0da8b144b3ae35e079b9412bd9e732b00b05a2eb03201d02838c4ec700` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradients_locally_bounded-v1-exit.json` | `55a2703886c6fe4bc1c1cc7d291ae581c1faf708427f6169f6e3ea22d8dff86f` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-subgradients_locally_bounded-v1.log` | `c3ac801ef84484181248e490c9524a97895c29b903502e4363d796cffd5e3e65` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-theorem_2_22-v1-exit.json` | `05d71001575cd6b462baedbc210db924b6e47f38904ef829ca0091968eb63329` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-theorem_2_22-v1.log` | `d103d04ace6ffa1e3c10eafeae39e022c21311feda3e1eaab6c7e2589b73793f` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-theorem_2_22_forward-v1-exit.json` | `d9b744bc09cd4211e9fe79ea559546249b3a316cbf17bd08df05312b62cfc904` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-theorem_2_22_forward-v1.log` | `042e3ef58c5136437971ee8a7be962ee0a4a9e9dba267c73a66be75f04c57843` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-theorem_2_22_gradient-v1-exit.json` | `139e390fb9af31bf10da99a734f7642dcf7b114563660129a02367267b74331f` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-fence-theorem_2_22_gradient-v1.log` | `f5ba01150c7eba3cf730023622e68cb6c60545dccf850e162131a2aee9768b7b` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-freeze-v1.json` | `a58c0cccf4164747614c91a49bb1d495dd9e26c129732a9ae0327e39349d391a` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-generated-before-use-v1.json` | `54bdc62e0d3ab5a9893bd302f3440e6645904392eaf1115c008d1adc2fb242b5` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-lifecycle-v1-exit.json` | `573dc8c1a28402a3b3510b1de5e576115ef6b95be85d308b091dec9514e67fc8` |
| `runs/online-subgradient-differentiability-migration-20261007/draft-lifecycle-v1.log` | `b7f81bb0d80ad90363a582b5637eaeafe656e76a1292d1e6bb0b740ec6df9c71` |
| `runs/online-subgradient-differentiability-migration-20261007/historical-raw-supersession-v1.json` | `051c845c5f97044bcb4db5c9b229b3f97104b42a13fb916adef9ec6e0d7290e5` |
| `runs/online-subgradient-differentiability-migration-20261007/historical-raw-supersession-v2.json` | `502b66907131fa19f7c57cfb7ab2acb7f2370eff2e76db52d3f602e9dc2c1d4c` |
| `runs/online-subgradient-differentiability-migration-20261007/historical-raw-supersession-v3.json` | `0fa36f2349755dfcb93b54bdfd4149eaeab777ff7c985dc95b499513c0f03cf6` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/actual-types-v1.lean` | `1dd87ed85f0c2c2cc43b6b542bdebc508a7daa0ac2f28d2500e92b0758626ad4` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/export-scoped-dependencies-v1.lean` | `47f70e629d9ec6b802f0dd6abe7fe57648d4197fd54caea4f20fa8b147fe878e` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/new-boundary-canary-headers-v1.lean.txt` | `73d8530df219032467c87fd12f1ffdb522c303c0076e0e49b6015ea4d15698f4` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pinned-required-APIs-v1.lean` | `9cbb21a88c8516d171371711b09d647505e1d03cf4cb50da97364ae0d15f4abe` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof--OnlineConvexBarycenter.lean.txt` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof--OnlineConvexFirstOrder.lean.txt` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof--OnlineConvexMinorant.lean.txt` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof--OnlineSubgradientDifferentiability.lean.txt` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof--OnlineSubgradientInterior.lean.txt` | `72cf2057e9dee7a1e8c4f92bb7878cffbb9b7603ff6afbac4f90ee5af11db9d2` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-MANIFEST.md.txt` | `24200d35209b133039415ade3e5fa167ae4e99e744acc818a39d6f3023fba618` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-Tests--OnlineSubgradientDifferentiabilityCanary.lean.txt` | `078d21522145b948421a81eb99f66298fb141688858dad3502572fba703b0106` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-Tests.lean.txt` | `aa0f1f04e1264a90d6006957a7c219640afc36359712d4ce44ce4514f8240755` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-runs--lifecycle_sessions.jsonl.txt` | `965b92dee63637d88660d30080848f214b6822e8352aab719266cbfd726247b1` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-runs--trials.jsonl.txt` | `a5e886d508dcc7cc4b6ab2cbb8ff2058d296de6d451ef2da00dc51bf52bb43a0` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-website--content--chapters.json.txt` | `853af78af62b00470d887b90420d59d7635ea2814738e0b4a814e73038af26bb` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-website--content--highlights.json.txt` | `934dc9e5b3788dde002c8662e5a1dd44ba7c7f87740a631b881e76a086bb79dd` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v1-website--content--readings.json.txt` | `198a0e543d32cd1061b2aad3744687c5270b76a440069e241269eb5b39d7f503` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineConvexBarycenter.lean.txt` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineConvexFirstOrder.lean.txt` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineConvexMinorant.lean.txt` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientDifferentiability.lean.txt` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientInterior.lean.txt` | `72cf2057e9dee7a1e8c4f92bb7878cffbb9b7603ff6afbac4f90ee5af11db9d2` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-MANIFEST.md.txt` | `24200d35209b133039415ade3e5fa167ae4e99e744acc818a39d6f3023fba618` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-Tests--OnlineSubgradientDifferentiabilityCanary.lean.txt` | `078d21522145b948421a81eb99f66298fb141688858dad3502572fba703b0106` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-Tests.lean.txt` | `aa0f1f04e1264a90d6006957a7c219640afc36359712d4ce44ce4514f8240755` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-runs--lifecycle_sessions.jsonl.txt` | `965b92dee63637d88660d30080848f214b6822e8352aab719266cbfd726247b1` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-runs--trials.jsonl.txt` | `a5e886d508dcc7cc4b6ab2cbb8ff2058d296de6d451ef2da00dc51bf52bb43a0` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-website--content--chapters.json.txt` | `853af78af62b00470d887b90420d59d7635ea2814738e0b4a814e73038af26bb` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-website--content--highlights.json.txt` | `934dc9e5b3788dde002c8662e5a1dd44ba7c7f87740a631b881e76a086bb79dd` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v2-website--content--readings.json.txt` | `198a0e543d32cd1061b2aad3744687c5270b76a440069e241269eb5b39d7f503` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof--OnlineConvexBarycenter.lean.txt` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof--OnlineConvexFirstOrder.lean.txt` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof--OnlineConvexMinorant.lean.txt` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof--OnlineSubgradientDifferentiability.lean.txt` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof--OnlineSubgradientInterior.lean.txt` | `72cf2057e9dee7a1e8c4f92bb7878cffbb9b7603ff6afbac4f90ee5af11db9d2` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-MANIFEST.md.txt` | `24200d35209b133039415ade3e5fa167ae4e99e744acc818a39d6f3023fba618` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-Tests--OnlineSubgradientDifferentiabilityCanary.lean.txt` | `078d21522145b948421a81eb99f66298fb141688858dad3502572fba703b0106` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-Tests.lean.txt` | `aa0f1f04e1264a90d6006957a7c219640afc36359712d4ce44ce4514f8240755` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-runs--lifecycle_sessions.jsonl.txt` | `965b92dee63637d88660d30080848f214b6822e8352aab719266cbfd726247b1` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-runs--trials.jsonl.txt` | `a5e886d508dcc7cc4b6ab2cbb8ff2058d296de6d451ef2da00dc51bf52bb43a0` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-website--content--chapters.json.txt` | `853af78af62b00470d887b90420d59d7635ea2814738e0b4a814e73038af26bb` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-website--content--highlights.json.txt` | `934dc9e5b3788dde002c8662e5a1dd44ba7c7f87740a631b881e76a086bb79dd` |
| `runs/online-subgradient-differentiability-migration-20261007/leaves/pre-integration-v3-website--content--readings.json.txt` | `198a0e543d32cd1061b2aad3744687c5270b76a440069e241269eb5b39d7f503` |
| `runs/online-subgradient-differentiability-migration-20261007/local-declarations-v1-01-exit.json` | `2b208e94c0db0746c6273fc0a0e0539fe00fd761cd38703415372de3e486ac2d` |
| `runs/online-subgradient-differentiability-migration-20261007/local-declarations-v1-01.log` | `018a8a055eb819d6ebc413b5cc7f327ca0bdc1e136be2e11b21f925a81623f5c` |
| `runs/online-subgradient-differentiability-migration-20261007/local-memory-v1-01-exit.json` | `76d220e3ca5736960155b7cd22461af97faeef252070205ae229fd7f54e1d211` |
| `runs/online-subgradient-differentiability-migration-20261007/local-memory-v1-01.log` | `3a87f266c650bec3553be37505b517b639686f79c4e2e5f57cb3eb341b319eff` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/singleton_subdifferential_hasGradientAt.json` | `c65db84c014b12521e8e11907f4e2f691721f7553260aab3dd5b03741bfe9ca9` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/singleton_subdifferential_interior.json` | `86f557abfb7e7ec7c91fa4d684c1cc6f62ca34720a55333b9637f3d32ad0c2e3` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/singleton_subgradient_tendsto.json` | `ce4c843ebc834cf2068209dcddebcb18966585aa758e986e3f325cd2b8f2a0d9` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/sourceDifferentiableAt_regular.json` | `198589c77b0bc2b9bc909ef6c05ab11789da85419c16a3c9f5c5a56c757abc70` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/subgradient_eq_gradient_at_interior.json` | `179e4dfab03f59ec9304f8772c580d2edf72bd8a0351cc460bd2af38bf5cffe2` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/subgradient_limit_of_continuousAt.json` | `85144f4e4a369dec3d84c757036388ca019d31bfb13a4b6b0501853f36c16b61` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/subgradient_norm_le_lipschitz_ball.json` | `9df18c0da8b144b3ae35e079b9412bd9e732b00b05a2eb03201d02838c4ec700` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/subgradients_locally_bounded.json` | `c3ac801ef84484181248e490c9524a97895c29b903502e4363d796cffd5e3e65` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/theorem_2_22.json` | `d103d04ace6ffa1e3c10eafeae39e022c21311feda3e1eaab6c7e2589b73793f` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/theorem_2_22_forward.json` | `042e3ef58c5136437971ee8a7be962ee0a4a9e9dba267c73a66be75f04c57843` |
| `runs/online-subgradient-differentiability-migration-20261007/native-draft-fences/theorem_2_22_gradient.json` | `f5ba01150c7eba3cf730023622e68cb6c60545dccf850e162131a2aee9768b7b` |
| `runs/online-subgradient-differentiability-migration-20261007/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-differentiability-migration-20261007/original-OnlineConvexFirstOrder.lean.txt` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `runs/online-subgradient-differentiability-migration-20261007/original-OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-differentiability-migration-20261007/original-OnlineSubgradientDifferentiability.lean.txt` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `runs/online-subgradient-differentiability-migration-20261007/original-OnlineSubgradientDifferentiabilityCanary.lean.txt` | `078d21522145b948421a81eb99f66298fb141688858dad3502572fba703b0106` |
| `runs/online-subgradient-differentiability-migration-20261007/original-OnlineSubgradientInterior.lean.txt` | `72cf2057e9dee7a1e8c4f92bb7878cffbb9b7603ff6afbac4f90ee5af11db9d2` |
| `runs/online-subgradient-differentiability-migration-20261007/original-Tests.lean.txt` | `aa0f1f04e1264a90d6006957a7c219640afc36359712d4ce44ce4514f8240755` |
| `runs/online-subgradient-differentiability-migration-20261007/pinned-APIs-v1-01-exit.json` | `6ee13d163a0c17b3355fafcd0f200dabe612e8b3029d499d60ba2364703e6957` |
| `runs/online-subgradient-differentiability-migration-20261007/pinned-APIs-v1-01.log` | `4a47ebf040aa9fb377dc5e13acb77d135c91428faebbb7f14657197981aca154` |
| `runs/online-subgradient-differentiability-migration-20261007/preparation-export-path-diagnostic-v1.md` | `e4f30aa7eac1e8b66e2cace45e3d790b6a98b03d099ef7251f2b63cadbca33c5` |
| `runs/online-subgradient-differentiability-migration-20261007/preparation-read-diagnostics-v1.md` | `b9e58c468dea3ed7a006773ecca7bd8c3652e6d725b9d99b34c97712048bed52` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-draft-v1-01-exit.json` | `8b16b32e7e028acec269ff2f9df49a0dc423cd309622d4158d79169b114b1b51` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-draft-v1-01.log` | `751ad4bfad14cbf08193e553417d8572ece4fae16eff171406d5f45d8711803c` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-draft-v1.py` | `4f77c830b4cfa80c778780527deb6ebc7ecc9cc0604d352b8e6b5e21cd24e8d6` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-ready-v1-01-exit.json` | `e701d91980af56a972148e217cf1708a19725cc8c04c193b7bf71e62c51bfb58` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-ready-v1-01.log` | `93375d0d90a241a5ffb94a39efe3a5aa9d4ffe0a55081137d8f40229ece8449c` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-ready-v1.py` | `dfd88f9e160783ebb9bd5d24283ab0c08231b8c15541a1a19014c91641a53358` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v1-01-exit.json` | `bf191e5dad93a53a0acd1eafc75560760c52fd89a8ff9f846264bb299bc9c887` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v1-01.log` | `8be3d6697375afcb96baf95bf7cbad2e40971f53ad26e433345ec6e6775148de` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v1.py` | `330f372db30dc6e2e56cbfcdf5fa6d3e797c17b2a5c10133cd66da2258c27f9e` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v2-01-exit.json` | `09a7d35580747b5b6467c5270fd8578798ee726582e6d6ad199011b3ea2594c3` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v2-01.log` | `086000e34eb79230837abac8ad80ce13c3ca9fbb34accbb56181dd7c098b38f7` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v2.py` | `1bb30c50aa6a4d0f52fb6c795b6dc2e641fb8ba992909788a0a6ff75e79a65ac` |
| `runs/online-subgradient-differentiability-migration-20261007/prepare-source-review-v3.py` | `d9adb9a5ae1c199f54ebd0e36b17b3df291ccddd0ab4029d743b9dc1f6c333b8` |
| `runs/online-subgradient-differentiability-migration-20261007/proof-obligations-v1.json` | `363c4eb9d00807fb93f807da9305e2a30727773f57ae6a3d19beb0ba385e0ddd` |
| `runs/online-subgradient-differentiability-migration-20261007/public-named-declarations-v1.json` | `7d0a9d9cc626c288212f425ffd808a8ee79a7a571c2ea580cc6e4329960b7d29` |
| `runs/online-subgradient-differentiability-migration-20261007/ready-dependencies-v1.json` | `9717a13ca6ae3e1f109dd92b6281d39873d52a9a87f95b1465d057830731b9a5` |
| `runs/online-subgradient-differentiability-migration-20261007/ready-dependencies-v2.json` | `9717a13ca6ae3e1f109dd92b6281d39873d52a9a87f95b1465d057830731b9a5` |
| `runs/online-subgradient-differentiability-migration-20261007/ready-dependencies-v3.json` | `9717a13ca6ae3e1f109dd92b6281d39873d52a9a87f95b1465d057830731b9a5` |
| `runs/online-subgradient-differentiability-migration-20261007/ready-generated-before-use-v1.json` | `566d4b602751c0615c2a3e3a5fb1f8294b211da6f805dff97baefebb137f70e2` |
| `runs/online-subgradient-differentiability-migration-20261007/retained-module-v1-01-exit.json` | `b19839a019d451adbff6ca24207b8b2718c8064ca2b14fbb86fadcbb05e32157` |
| `runs/online-subgradient-differentiability-migration-20261007/retained-module-v1-01.log` | `42a4fb31382bd1acb0fe079bdd90977868a3b4cb66ac1f261e25ea016eed4a02` |
| `runs/online-subgradient-differentiability-migration-20261007/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-subgradient-differentiability-migration-20261007/source-printed17-pdf29.txt` | `38f58d214ab8616aef7b7147338f7fd91ecdcf159b5286ea47092cf4ece81c46` |
| `runs/online-subgradient-differentiability-migration-20261007/source-render-binding-v2.json` | `78a3e2b29ffa5c2657b8e9906588e8fdd6faeb2e325e17f546b5968c4627d317` |
| `runs/online-subgradient-differentiability-migration-20261007/source-render-v2-01-exit.json` | `40525bc85f488e6312c0ef615d8c674bad1e7c8831dd014a2a53f0ccf40e438b` |
| `runs/online-subgradient-differentiability-migration-20261007/source-render-v2-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-differentiability-migration-20261007/source-review-helper-before-use-v2.json` | `81198be1fc6187df954feddd1439e68358bd48741a730ad30a34c95321945e39` |
| `runs/online-subgradient-differentiability-migration-20261007/source-review-helper-before-use-v3.json` | `3b67d7d167d278390ec7411cdc049ef99e113ba0db478a84d2063a6412ee0faf` |
| `runs/online-subgradient-differentiability-migration-20261007/source-review-packet-v1.md` | `983454f488df7b47955a4070695a3f4acaadb5d6fedf42c8897ffe611e74f65d` |
| `runs/online-subgradient-differentiability-migration-20261007/source-review-packet-v2.md` | `40775cca34101784e1c0958c98e46fef6c47c28528af3455b3b8d6cca62b3b55` |
| `runs/online-subgradient-differentiability-migration-20261007/source-review-packet-v3.md` | `6ade35b38997b26831e930a1ff625388ecd1bd4f6e30c7131057fdec312fdeb2` |
| `runs/online-subgradient-differentiability-migration-20261007/workspace-audit-v1.json` | `5c4200a35f2af4a04e5eb2fdf3a258e70b65ad73e3e871426516797f3b57d8fb` |
| `runs/online-subgradient-interior-migration-20261006/accepted-decision-v1.json` | `b0034ef2191f116def408cca806c1cddbde80d0c071d4378070983480cdf4df9` |
| `runs/online-subgradient-interior-migration-20261006/delivery-v1.md` | `97af42fb1b66a36bc8b20d586d578eb17e9a103845094e18131bd83531e8062f` |
| `tasks/ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007.md` | `f72bc5d73138e488f7814cf726f706ffed3235f26c12a534eb65f36b39e554ab` |
| `tmp/online-subgradient-differentiability-migration-graph-v1.json` | `0bb3e522ff38b410595a5fcdc66f636a0402a2198d773d1bed3299d1c32cad17` |
| `tmp/online-subgradient-differentiability-source-pdf29-v2.png` | `7bc9bb6f72b9a03ee6d6c203fbe5db1c1f177a242f8375d0e0d1b60c2575c146` |
| `website/content/chapters.json` | `853af78af62b00470d887b90420d59d7635ea2814738e0b4a814e73038af26bb` |
| `website/content/highlights.json` | `934dc9e5b3788dde002c8662e5a1dd44ba7c7f87740a631b881e76a086bb79dd` |
| `website/content/readings.json` | `198a0e543d32cd1061b2aad3744687c5270b76a440069e241269eb5b39d7f503` |
| `runs/online-subgradient-differentiability-migration-20261007/contract-source-inputs-v3.json` | `53eb2c0648bb4c639f631532b30c2b4223cf0e9293e171648497c5bc650b390b` |
