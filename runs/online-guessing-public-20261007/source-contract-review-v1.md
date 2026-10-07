# Canonical Example2.32 — current CONTRACT source review

**Verdict: accepted-with-explicit-delta, CONTRACT stabilization only.** No blocking mathematical or contract-metadata repair found. Future reader obligations R1–R8 below are not yet discharged.

Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, runtime unverified. Root formalizer and osd_blind decoder are distinct automated actors. Prior staged source-review history, including the separate policy-family package, is disclosed. This is not blind/human/external review or runtime-model attestation.

All111 fixed raw inputs were independently hashed before and after review. Original v10 PDF was freshly hashed to `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. I actually viewed original PDF13/27/31/32 pixels and reread bound source texts13/14/15/27/28/31/32. PDF13 alone begins with an IID example; PDF14 removes that restriction and PDF15 discusses adversarial data. No IID/probability premise is imported into this deterministic comparator statement. PDF32 gives the three support sets and O(sqrtT); PDF31 transfers gradient analysis to actual global subgradients and PDF27 equation2.1 supplies finite D=G=1 tuning, while expressly warning against future-energy optimization.

## Complete definition and imported context

Owned `loss (y x : Real) : EReal := embed(|x-y|)` is complete and finite everywhere. SourceSubdifferential is global against every ambient real point, not merely [0,1]. Its generic EReal definition is broader than the source proper-function convention, but this specialization is genuinely proper. SubdifferentiableOn includes properness AND nonempty global supports at every feasible query. Actual currentSubgradient is classical choice if nonempty, zero otherwise; nonemptiness prevents fallback from faking support legality. No arbitrary tie value is stipulated. Step/iterate use shared nearest projection and recursion; no duplicate domain/project or new public definition is requested.

The exact twelve current headers match the frozen complete headers. Neutral aliases specialize every shared type to the real scalar setting. The actual comparison file explicitly closes all binders, maps Q01–Q12 to S01–S12 and supplies twelve rfl equalities. Recorded neutral and bridge commands exit0 (10.253s and10.295s). These prove proposition identity under the explicit map, not the target propositions or source fidelity. The fresh decoder reconstruction agrees on full support sets, canonical scope and quantifier order; its disclosed prior neutral history is retained. Existing bodies were read as contradiction/interface checks, not retrospectively accepted as this phase's BODY gate.

## Per-header seven-slot decisions

### loss_subdifferential_translate — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | All real y,x; both whole global support sets. |
| assumptions | No hypotheses. |
| operation_information | Translate query to x-y and test every ambient real comparison point. |
| conclusion | Equality of full shifted and unshifted support sets, both inclusions. |
| constants_indices | Exact shift x-y, no time/rate. |
| source_delta_boundaries | All real labels/queries generalize source interval game; not equality of unshifted losses or a chosen support. |

### loss_subgradient_positive — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | All real y,x and every possible support. |
| assumptions | Strict y<x only. |
| operation_information | Classify global supports above loss center. |
| conclusion | Whole set equals {1}. |
| constants_indices | Exact positive sign and singleton. |
| source_delta_boundaries | Tie excluded; no feasible-label/query restriction; stronger global helper. |

### loss_subgradient_zero — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Every real y with query y. |
| assumptions | No extra hypothesis. |
| operation_information | Classify global support set at equality. |
| conclusion | Whole set equals closed Icc(-1,1). |
| constants_indices | Both endpoints and every intermediate support included. |
| source_delta_boundaries | No zero tie selection assertion; extends beyond source label interval. |

### loss_subgradient_negative — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | All real y,x and every possible support. |
| assumptions | Strict x<y only. |
| operation_information | Classify global supports below loss center. |
| conclusion | Whole set equals {-1}. |
| constants_indices | Exact negative sign, not magnitude-only. |
| source_delta_boundaries | Tie excluded; arbitrary real values, global helper extension. |

### example_2_32_subdifferential — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | All real y,x and the entire support set. |
| assumptions | No extra hypothesis. |
| operation_information | Nested tests y<x then x=y, real order determines final x<y branch. |
| conclusion | Exhaustive {1}/closed[-1,1]/{-1} equality. |
| constants_indices | Exact signs, closed endpoints and branch order. |
| source_delta_boundaries | One printed example classification, not three chosen-support facts; arbitrary-real extension disclosed. |

### loss_on_unitInterval — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Every real y; support existence at every feasible query. |
| assumptions | None. |
| operation_information | Use exact SubdifferentiableOn conjunction. |
| conclusion | Nowhere-bottom plus an ambient finite witness AND nonempty global supports at all x in [0,1]. |
| constants_indices | Closed feasible endpoints0 and1; no rate or horizon. |
| source_delta_boundaries | Ambient finite witness need not lie in V; real loss finite everywhere. Arbitrary y extension, no computable oracle claim. |

### loss_subgradient_bound — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Every real y,x,g. |
| assumptions | g belongs to global SourceSubdifferential(loss y)x. |
| operation_information | Take norm of any actual support. |
| conclusion | Norm g <=1, not only the canonical selected support. |
| constants_indices | Exact constant1 attained at both kink endpoints. |
| source_delta_boundaries | Global support prevents domain-boundary normal additions; no assumed bound and no restricted-domain support. |

### current_subgradient_bound — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Every real y and feasible real x. |
| assumptions | x belongs to closed [0,1], retained exactly. |
| operation_information | Evaluate existing currentSubgradient on current whole loss and point. |
| conclusion | Norm of that actual choice <=1. |
| constants_indices | Exact bound1; no specified numerical tie value. |
| source_delta_boundaries | One permitted noncomputable canonical selection. Proper/nonempty support producer makes empty-set fallback irrelevant; not the entire policy family. |

### loss_step_clamp — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Every real eta,y,x. |
| assumptions | None. |
| operation_information | Actual shared projection of x-eta*currentSubgradient(loss y)x. |
| conclusion | Full equality to min(max(raw,0),1). |
| constants_indices | Subtraction sign, lower0 upper1; eta may be zero or negative. |
| source_delta_boundaries | Unconditional algebraic identity beyond feasible source runs; no performance claim for nonpositive eta or infeasible initialization. |

### guessing_prefix — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Every eta,etaPrime,y,yPrime,x1 and natural t. |
| assumptions | Schedules and labels agree for every s<t; same initial x1. |
| operation_information | Compare the actual canonical iterates before current loss is used. |
| conclusion | Exactly equal outputs at time t. |
| constants_indices | Strict prefix0 through t-1; at t0 both equal x1. |
| source_delta_boundaries | No future feasibility/positivity; no independently chosen initialization or rate independence, stochastic filtration or finite-query execution certification. |

### example_2_32 — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Fix y,x1,T then every feasible comparator u on one common run. |
| assumptions | Feasible x1; T>0; each played y(t) in [0,1]. No externally supplied support/norm/regret premise. |
| operation_information | Actual canonical iterate with constant eta=1/sqrt(T). |
| conclusion | Finite real absolute-loss comparator sum <=sqrt(T), all u in [0,1]. |
| constants_indices | D=G=1, source round1=Lean0; T terms end at iterate(T-1), not endpoint iterate(T). |
| source_delta_boundaries | Source-unused hy preserved. Exact constant is derived from eq2.1/OSD transfer, not verbatim printed numerical theorem; T0 excluded, negative regret possible. |

### example_2_32_average_eventually — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar losses loss(y,x)=embed(|x-y|) and shared ambient/global support or canonical projected OSD as applicable. |
| quantifiers | Fix y,x1,u,epsilon then eventual natural T. |
| assumptions | Feasible x1,u; every label feasible; epsilon>0. |
| operation_information | For each T run the same canonical selector with its separately prescribed constant1/sqrt(T). |
| conclusion | Eventually signed real regret/T <epsilon. |
| constants_indices | Same T is horizon/rate parameter/denominator; eventual T0 exception harmless. |
| source_delta_boundaries | Derived one-sided upper family consequence, not signed Tendsto0, absolute Big-O, common anytime run or expected-regret theorem. |

## Source-fidelity judgment and remaining reader obligations

No hidden convexity, differentiability, supplied norm/regret certificate, chosen-zero kink rule, comparator-dependent path or future-loss selector input was found. Canonical selection is one valid realization of Algorithm2.2, not every allowed history-dependent support choice. The separate PR182 package now supplies that played-legal family and is not missing mathematical work here. Its accepted/delivered references are bounded dependency evidence, not a reason to count new closures in this reuse task. Historical module/contract comments about the formerly missing family remain historical bytes; current reader prose must explicitly reflect the new state rather than silently reopening the completed family.

Source support identities extend to arbitrary real labels/queries; selected canonical bound retains x feasibility; clamp/prefix are broader algebraic identities. The finite sqrtT bound and eventual upper-family consequence are explicit derived refinements. There is no assertion that signed regret tends to zero or that one run is anytime. Reused sharp regret analysis retains its negative terminal term; the coarse source-example bound may subsequently discard a nonnegative term.

- **R1 (future mandatory)**: Attribute one printed Example2.32; distinguish twelve existing library declarations, supporting refinements and derived finite/eventual consequences. Zero new mathematics in this reuse migration.

- **R2 (future mandatory)**: Display all global shifted support branches with full closed[-1,1], every ambient comparison point, arbitrary-real helper extension and no zero tie rule.

- **R3 (future mandatory)**: Explain complete finite EReal loss definition, produced properness/nonempty supports and all-support norm bound; current-bound feasible-query premise must not disappear.

- **R4 (future mandatory)**: Identify canonical noncomputable current whole-loss/current-point selection, actual projection/recursion and strict-prefix scope, with no external-parameter independence/randomized-law/executable-oracle inference.

- **R5 (future mandatory)**: State arbitrary-real clamp/prefix/helper generalizations separately from source-valid positive-rate feasible-initialization performance; T0 is algebraic/eventual boundary only.

- **R6 (future mandatory)**: Keep source labels/initialization/comparators in[0,1], positive knownT and same eta=1/sqrtT path for allu. Exact finite constant1 is D=G=1 refinement; finite conversion and actual norm/diameter producers are required, no regret oracle.

- **R7 (future mandatory)**: State only eventual signed-average upper control of separately tuned horizon family, not signed zero limit/absolute Big-O/anytime; negative residual remains in reused sharp fixed bound before coarse specialization.

- **R8 (future mandatory)**: Replace stale current-reader claims that generic played-legal history-family coverage is missing: PR182 separately accepted/delivered it. Preserve its four notes/two cards/math and distinguish this zero-new-proof canonical migration. Keep remaining migration/maintext/appendices/nineOTHERChapter1 gaps/Chapter2 incomplete/wholeGoal active and future gates explicit.

Required mathematical repairs: none. Required blocking contract metadata repairs: none. No current BODY, canary replay, root/Tests/full harness, reader/FINAL, native acceptance or PR delivery is certified. All12 proofs, one loss definition and existing canary predate this task; zero newly authored mathematical results are accepted here. Chapter2 remains incomplete and the whole Goal remains active.

## Raw reviewed inventory

Every fixed row was read for byte verification; semantic review focused on the original source, full contracts/context, actual headers, canonical definitions, neutral bridge and reconstruction. Inventory inclusion does not independently reaccept all historical proof packages or canary bodies.

| Path | SHA-256 |
|---|---|
| `BanditRLProof/OnlineGuessingSubgradient.lean` | `95d206190d443939115037f9bf6d0eeb1e3229f3ae52eb4150927fbe69e89348` |
| `Tests/OnlineGuessingSubgradientCanary.lean` | `b6a6e3f5c019172e2ee46d3caf03fcbc65d9bbe3a90474b03532ca560f849a61` |
| `BanditRLProof.lean` | `7cdb1969bad2f7b42cfd7a25f6d15747d0d49178dadc244b70ab1f9b8c92c5ad` |
| `Tests.lean` | `2b3615efabe9c94eff5dade925783e7d0ebacd3139a7ab65a5d46ba2c695ef77` |
| `BanditRLProof/OnlineGuessingSubgradientPolicy.lean` | `ed32d846509d0dc34eb05ce6fad5d3af8aa6dbf92a8c8a78cc8859b0e42e6b0e` |
| `Tests/OnlineGuessingSubgradientPolicyCanary.lean` | `16591f7ee319275d2fe9399d6ad89b2aec179b97f0c80f12d5c2633428074658` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineSubgradientPolicy.lean` | `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `bf3e8d97f67b78e7ad230b8efd321948f4d7ba1a0e9cde31e8d85c1e9019442b` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineGradientDescent.lean` | `9300cb2735da9f125e404f78b86509df47fe65a5f4d89abc469e071bdffdb871` |
| `BanditRLProof/OnlineGuessingOGD.lean` | `12792af1571fde0fe37796686b044f0df0990ca3d808a89431804605d0ee8d00` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `research-wiki/contribution-contracts/ONLINE-GUESSING-OSD-20261004.json` | `388e8d2338a4d31ee8a309de3b2748c40ed1310867d9d8455e00c3c40fe3bfc1` |
| `research-wiki/contribution-contracts/online-guessing-osd-policy-20261007.json` | `c57f6bbd824259c22446fdaf85934ea879c947f017c9d2af53da06d397f1d7c5` |
| `runs/online-guessing-osd-20261004/accepted-decision.json` | `87f8e846ef7653a037b4da7ecc6538d7625858593d54a0154cd12dbfcb03b8a3` |
| `runs/online-guessing-osd-20261004/delivery.json` | `801540af28ac50d8d16a9eaffa782d180b9f77f85cc2e19abd4a54300e0c1328` |
| `runs/online-guessing-osd-policy-20261007/accepted-decision-v1.json` | `49c647d14a2c9a76d20515db9de8196a68e316892d9a73d6f852207ba8fea0e3` |
| `runs/online-guessing-osd-policy-20261007/delivery-obligations-overlay-v1.json` | `16b2a7dd760c1bba527c67e1c9f3edb7cd2b71729ca8094d88235597bd9e955b` |
| `website/content/readings.json` | `d5bffc978fd1c9cc224cd05583a6a6d5aef164f2e32742ade6fef576b09816a5` |
| `website/content/highlights.json` | `efa559d37c05f21556ef0ede3f71ee5cd5d219f0027c4e4d7fbb30dfaaa9c6cb` |
| `website/content/chapters.json` | `ff6e01e04b9690c622e543495cdd5bdbd7461abca574c40aa9d052cebca3ead0` |
| `docs/contracts/online-guessing-osd-v1/context.txt` | `deb0e9a941ba4b4d47b8bb786462ef7440bef3c10803adf695caffb043e2f799` |
| `docs/contracts/online-guessing-osd-v1/contract-manifest.json` | `b1d1d0d25a6b710f749737bbf1e58ca2fc2fcc98fb935bef526ca843503c371d` |
| `docs/contracts/online-guessing-osd-v1/contract.md` | `3b236291e115bc6cc627fcd9b827293eccabc352b2f64221dbdc5c4159f52aaf` |
| `docs/contracts/online-guessing-osd-v1/current_subgradient_bound-header.txt` | `cf33e00553af8f12b3fb7cc16d9667093d031c33c48f5eb537ac920088ac7b01` |
| `docs/contracts/online-guessing-osd-v1/current_subgradient_bound.json` | `4dbcd582cabb166461b00314f5428be3c562cc7251a059e2230a00d671c4d3e3` |
| `docs/contracts/online-guessing-osd-v1/example_2_32-header.txt` | `c783a2dc477402bf38fd856d55570133c5324206a2ab189d41561fab8d03c3ac` |
| `docs/contracts/online-guessing-osd-v1/example_2_32.json` | `b51f3c0671d78988ba358c92b9b4790b59974d824a65668a78e9ad1043b61d06` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_average_eventually-header.txt` | `0cd31eb16ead30a23bed6ffa30c7c0952d69f37270f5740cc55f995870e16439` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_average_eventually.json` | `9eb36a77d2fb1b97d849c49c4ad86f838f1f8255c9d29e73c5b22f45ba7c1e34` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_subdifferential-header.txt` | `61d8e03bcb2e643daee7b008f5d3bc3908a02a4339dd9f92fa5af002bdbc6d2c` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_subdifferential.json` | `e287c2ed89ca0e4f3f4c59f0b95d953bb187be1a4f2d09ae0392407c1aea828c` |
| `docs/contracts/online-guessing-osd-v1/guessing_prefix-header.txt` | `85bd7478cc9b46e4ddcb882e03e904834cd07c7bc623ecdeb0bf5a23f0b3b77d` |
| `docs/contracts/online-guessing-osd-v1/guessing_prefix.json` | `b9782c4f0191ec5a884f3471f69ef41aa7386a4106d2df270f6cdd062a11cc60` |
| `docs/contracts/online-guessing-osd-v1/loss_on_unitInterval-header.txt` | `bc224e1366aa5de2f5eb46311b3134c56b391cb598d137c914acc183db715064` |
| `docs/contracts/online-guessing-osd-v1/loss_on_unitInterval.json` | `6f494a3958af3d95bbc255e21230cecd365c92f889006e9d3e985735ef88b046` |
| `docs/contracts/online-guessing-osd-v1/loss_step_clamp-header.txt` | `f41c0649d2b82da6bd391a1bd69b03d5efabc6bc8a8f8bcae529b0f10c555001` |
| `docs/contracts/online-guessing-osd-v1/loss_step_clamp.json` | `20cf4696a13bf4e5f2f40309b8296954e044ec416da1c3acd9a98db7391a9613` |
| `docs/contracts/online-guessing-osd-v1/loss_subdifferential_translate-header.txt` | `3e303b7cb3bb4d4fd51349d19ed4c30ca952d8d57ced97fc74ba266ef7fcb811` |
| `docs/contracts/online-guessing-osd-v1/loss_subdifferential_translate.json` | `7d16d3f25a0cf06e7ca447651408b82515638322c4bdb06b5e06cf0b2faea3be` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_bound-header.txt` | `934b033137d815b54dd7973a328f2fffe8933908e0437b8358ea02c168edfe3d` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_bound.json` | `98335caa7f1149b998c959ad4fedd44f2b48654712812b9afcb712fc65cb22ec` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_negative-header.txt` | `5745e4574dfaaf95ca5ea2e87220307b4e8401505750d7eb8eb49eb645361f4f` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_negative.json` | `61ed853fa8ac292f6147f9bbcf7ff819351c3ad3193d338107553f1560f76b5b` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_positive-header.txt` | `eb6f103874810ecfbbe56892bc55e73f5f9de60c0ba0482b421a32dddc0b131f` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_positive.json` | `8a85b389d9219679900e837098e322af7f7d7780c04340d927863ff48b5fae49` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_zero-header.txt` | `ef40090cc45c6b5f9f8533128d513def4c209a25c33aacf3100405f386f6ae99` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_zero.json` | `918ab9f31624ea291033f6c2e74551e80a98b5384dff1d687774ac2342bde953` |
| `docs/contracts/online-guessing-public-v1/actual-context-v1.txt` | `deb0e9a941ba4b4d47b8bb786462ef7440bef3c10803adf695caffb043e2f799` |
| `docs/contracts/online-guessing-public-v1/contract-manifest-v1.json` | `58bfea372b6cd3753cc0394a4a4270068c1353f2428458c5bc0d0a6304f51162` |
| `docs/contracts/online-guessing-public-v1/contract-v1.md` | `4bdb32b931f89b395aa67b11466e82e9826c279ef767ddc111cd3f40fb3a2a25` |
| `docs/contracts/online-guessing-public-v1/conversion-window-v1.md` | `356e767fd4f357c8bebca489f1d6a797749b10ae1e816612af2485bab8b4f9af` |
| `docs/contracts/online-guessing-public-v1/dependency-DAG-v1.json` | `18cda3b08acde5e9293b0bfaa87aed2d85334e5c87fcbcaa68b5ea849e63ff49` |
| `docs/contracts/online-guessing-public-v1/headers-v1.json` | `986af56ef8e30e4e0b7f9ccefba51a3857a0e0279c4707f8cfb60c7030b7eb1d` |
| `docs/contracts/online-guessing-public-v1/native-statement-fingerprints-v1.json` | `cfa9e89eec0560c92e0b89eb794f3e56a86aa735599fff3faf27c501823734d5` |
| `docs/contracts/online-guessing-public-v1/raw-statement-fingerprints-v1.json` | `9a255a4d784677b46bffa810f9b0aa734fba8485a899a4e0afe8c322cf879192` |
| `docs/contracts/online-guessing-public-v1/semantic-signature-v1.json` | `09b8a931f6c601f257a5f115c6f14242572f319ccc43ddcffc6e93be03f086b5` |
| `docs/contracts/online-guessing-public-v1/source-card-v1.json` | `0bfeaddb5de58a6347323634cc19d35b7850d6cf88ae25bf4e7cff38c0d97d8f` |
| `runs/online-guessing-public-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-guessing-public-20261007/00_context.md` | `591b9e3d49b82ae1b3e0940686122c1c381ff6131d8682d0520c5ced8dcc4fdf` |
| `runs/online-guessing-public-20261007/10_upper_director-v1.md` | `79c166765898a50945f37d9331e8cfc0f824a6cf60af426101dda16f433cc399` |
| `runs/online-guessing-public-20261007/20_architect-v1.md` | `e6e963d9daf16fd8330f31e1a789df75b1cf6235e195d70189acea3ea05ab245` |
| `runs/online-guessing-public-20261007/base-PR182-fresh-v1.json` | `d039781399f7723ae1b7266dfb4ed87fb0932e3df0808ea5b9b9c7aab402f06c` |
| `runs/online-guessing-public-20261007/blind-decoder-receipt-v1.json` | `170cec92fd2b84f8168a2b0e3a4dff5ad4c4eb284575e4d239d49c0ce3cf5ac0` |
| `runs/online-guessing-public-20261007/blind-decoder-v1.md` | `9511514ce492b920d703bb8bf7ec0557c477bb962843fd99d104ec6f8facd52a` |
| `runs/online-guessing-public-20261007/blind-packet-v1.md` | `066703b42b5bb41b5979ab2fdb2f134ed00119639f04eea09de567a719274cb5` |
| `runs/online-guessing-public-20261007/canonical-worktree-audit-v1.json` | `a4aeccc2e39840cddfa8080af69dae4f600f52f61ecf771de2d837525f18f0b1` |
| `runs/online-guessing-public-20261007/closed-type-comparison-v1-01-exit.json` | `358d0775a6245344fa5b4611f735ca6d6339b8ae49349c86078e164c3ac97dfa` |
| `runs/online-guessing-public-20261007/closed-type-comparison-v1-01.log` | `47676f0e048704e8657524424deafa29af31a341e8e96b69bbcdf056594d4784` |
| `runs/online-guessing-public-20261007/closed-type-comparison-v1.json` | `aae2378aca0ea5fff70273f05d82079df81d4dbfb13f0a49a8596c0cd75c8c77` |
| `runs/online-guessing-public-20261007/draft-event-v1-01-exit.json` | `20004e942b407359856ebee4c898f9b56755ce6bb5b4e7b31276e0f85914337e` |
| `runs/online-guessing-public-20261007/draft-event-v1-01.log` | `790d13a011b91d984f9b0a19c117fe15e9962bb637d1e52f03c400031feb06f2` |
| `runs/online-guessing-public-20261007/draft-freeze-v1.json` | `ed67a8ad06bd833306a8049d9716420314f62979c770306e47e42eadf0f20420` |
| `runs/online-guessing-public-20261007/fresh-fetch-v1-01-exit.json` | `24d873dd71b9a56f089a838777c2067088e506e9bac4aeacf67feadab2bbbd36` |
| `runs/online-guessing-public-20261007/fresh-fetch-v1-01.log` | `43d6c5fb95289456ec8b226a0a4a45bf3caf4e494b578d8c2421a3f157a7239c` |
| `runs/online-guessing-public-20261007/historical-PR148-fresh-v1.json` | `eed1e4be0584dc25af563c03c40046a2beaa2c4cf10f748f7b880798167ce11c` |
| `runs/online-guessing-public-20261007/leaves/closed-type-comparison-v1.lean` | `5e72ea93122a8f5b4930c110a15cca8c9ed2a9cc35bbddd896c6f6da28ffe3b5` |
| `runs/online-guessing-public-20261007/leaves/neutral-propositions-v1.lean` | `c686346712ba80ca00b4e651b3f158f9fe57f79d99a283b625f9877fbfaaebba` |
| `runs/online-guessing-public-20261007/local-API-search-v1-01-exit.json` | `f40ce9fdb2a4e6689d9bbe45e336e18c99d01a3e1d6064390958ff4838a7a2a6` |
| `runs/online-guessing-public-20261007/local-API-search-v1-01.log` | `7f7ba982963e13be175c916d33515ded14386d3db8666714be928ef82c87e871` |
| `runs/online-guessing-public-20261007/mathlib-API-search-v1-01-exit.json` | `8b4dd695e0009be3214a529432d706cff5f64c171f6f491ad590c60239181357` |
| `runs/online-guessing-public-20261007/mathlib-API-search-v1-01.log` | `d6904072b6e66b7c7e0f80850e3e7125cd874301104d352d674ceb8010044ed4` |
| `runs/online-guessing-public-20261007/memory-digest-draft-v1.md` | `1c9e60914dbe7235e4ff2f33873eb215d902fdf129faf4986e16bd6d621c87f9` |
| `runs/online-guessing-public-20261007/neutral-map-v1.json` | `5d37974f0676f0f1259d0177797537c325014d63a78475a80a076b3516e106e4` |
| `runs/online-guessing-public-20261007/neutral-propositions-v1-01-exit.json` | `519d0ffecc0bcf42009452a5ecafa268d3b66d1590c6fad4f48a5f9b5525f474` |
| `runs/online-guessing-public-20261007/neutral-propositions-v1-01.log` | `d182805c5de1913916417ef3b53444e4a558d086c78c0c103ac9148ce42d1bb5` |
| `runs/online-guessing-public-20261007/new-task-v1-01-exit.json` | `0d42c7bfa349912438e3ad78a7c5f87836d42168c5fb0b5c8e94030a4aa1b17a` |
| `runs/online-guessing-public-20261007/new-task-v1-01.log` | `6d7739fa053eb18863527ea2403ca33da68d1dcd0c393706c369dce03bb41187` |
| `runs/online-guessing-public-20261007/paper-boundary-v1.json` | `dae89e7ae9e0499b4d371a595aea19637b9e6430ce98331ca4ae4388b5747155` |
| `runs/online-guessing-public-20261007/proof-obligations-draft-v1.json` | `46a95a2a0c48065e3c8e41856e3c0971eedc02176e6027173aec6155c1902454` |
| `runs/online-guessing-public-20261007/reuse-decision-v1.md` | `6a8f053121f57220f66ea7727ded4b7f909f94894e32f8dd108b320d94369fce` |
| `runs/online-guessing-public-20261007/source-pdf13-v1.txt` | `b16d82b563558afaaa14776c6015a78be9e0daa3d888a9a0593c057a54d2288b` |
| `runs/online-guessing-public-20261007/source-pdf14-v1.txt` | `3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66` |
| `runs/online-guessing-public-20261007/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |
| `runs/online-guessing-public-20261007/source-pdf27-v1.txt` | `aed61245f25b365224da1ea1ca3a2d3f8439365707e6cca6e1f08b05087eaf42` |
| `runs/online-guessing-public-20261007/source-pdf28-v1.txt` | `a9d4910e2c687a25babd24d5b4c30f4e6c4d1fdc4018c29ad239c327bacfd87c` |
| `runs/online-guessing-public-20261007/source-pdf31-v1.txt` | `7709a706da7b5320555f5ef19e07fa798affde6a077363425b929c07af0b9a99` |
| `runs/online-guessing-public-20261007/source-pdf32-v1.txt` | `3cb9fb0c18b5b9c63c280944188334305bd9a042fed58fad67e797b6d7b76bdd` |
| `runs/online-guessing-public-20261007/source-pixel-inspection-v1.json` | `bea3b09356181b08d3a693f13a098496a8f0a87a388ffa92b4bf9fa32b50eb9e` |
| `runs/online-guessing-osd-policy-20261007/source-pdf13-v1.png` | `228ea769f7cec2ba5fe2d5e416b4ac5f60c93ec38f83a2dd7a537c2a51d2c5f4` |
| `runs/online-guessing-osd-policy-20261007/source-pdf27-v1.png` | `6df81ff53a64e9721ff400bcd3b41566aabdfacbe59da1eaf8b1331929836d49` |
| `runs/online-guessing-osd-policy-20261007/source-pdf31-v1.png` | `c1cb49ac038e88055cb4651f70755c456ccbc817a70c5a06c818f5967676bfa2` |
| `runs/online-guessing-osd-policy-20261007/source-pdf32-v1.png` | `ef5bdf4653f3d3a12dfd1809478e362e034bfb6b184a88c0ed199d98bd115b22` |
| `tasks/ONLINE-GUESSING-PUBLIC-20261007.md` | `144a72a5a9ef61be235a651178b89ce420ffa55ae58d398128fe546f093f6f79` |
| `conversion-windows/ONLINE-GUESSING-PUBLIC-20261007.md` | `144a72a5a9ef61be235a651178b89ce420ffa55ae58d398128fe546f093f6f79` |
| `proof-obligations/ONLINE-GUESSING-PUBLIC-20261007.md` | `144a72a5a9ef61be235a651178b89ce420ffa55ae58d398128fe546f093f6f79` |
| `runs\online-guessing-public-20261007\source-contract-packet-v1.md` | `7571626172329bfc10598e023fa7d98cd8d4ec60589e5a7d8ad1da936633de7a` |
| `runs\online-guessing-public-20261007\source-contract-inputs-v1.json` | `768ed8a328891f1f9b445ec27f7243b0e652c9af3a626b9721c99f3e0515972f` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
