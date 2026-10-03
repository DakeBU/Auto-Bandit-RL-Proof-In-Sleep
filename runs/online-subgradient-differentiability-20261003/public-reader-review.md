# Public reader and canary review: Theorem 2.22

Verdict: **accepted-with-explicit-delta for the inspected public reader, public canaries, source mapping, and import exposure**. No blocking semantic repair is required. This receipt does not certify the pending combined project/harness gate, generated site, final LF-normalized bindings, merge or live deployment.

Actor: `/root/source_reviewer`, a distinct automated source-review actor; requested model GPT-6 Astra, reasoning medium; date 2026-10-03. This is not external-human review. The prior `full-source-review.md` is preserved unchanged. The present task reviews public presentation and concrete tests against its previously inspected actual source/proof chain; compilation evidence is considered separately.

## Read scope and raw bindings

Worktree: `E:/ABRL/worktrees/research-online-book`; canonical research repository: `E:/ABRL/research`. The public proof/support files retain the same raw hashes as the preceding full-source inspection. The inventory below includes the preserved prior proof, context, reconstruction and review artifacts as well as every newly inspected production/log file. Hashes are raw bytes, not normalized text.

New read scope: the complete `Tests/OnlineSubgradientDifferentiabilityCanary.lean`; the relevant import lines in `BanditRLProof.lean` and `Tests.lean`; the Online Learning book record and new `online-subgradient-differentiability` chapter/reader/highlights; the Theorem 2.22 inventory record plus neighboring completion context; and the public canary log's target/build/axiom output. Other entries of the containing website and inventory files are not semantically approved by this targeted review. Prior proof/context files in the inventory were inspected during the immediately preceding full-source review and freshly rehashed here.

| File relative to worktree | Raw SHA256 |
| --- | --- |
| `BanditRLProof/OnlineSubgradientDifferentiability.lean` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `BanditRLProof/OnlineConvexMinorant.lean` | `33fc76b3f18e2686963ca59a895f320b21f8b437b0d27ff2d16bba37e7b08ea7` |
| `BanditRLProof/OnlineSubgradientInterior.lean` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `tmp/online-subgradient-full.lean` | `342c6c9430b22f5dc09b584a75389c0bac6f3df5f9daad88c507fcd58afe4dcc` |
| `runs/online-subgradient-differentiability-20261003/full-theorem02.log` | `d7c17e501a0d3f86c5af7b2c67e59f801cb05cd381f76cb451e9e4f51c268d1c` |
| `runs/online-subgradient-differentiability-20261003/reverse-gradient03.log` | `ced04583ef52a5e19cc6f6f2c2bdd19b250f866bf6ad0d44c37ac17420fa516c` |
| `docs/contracts/online-subgradient-differentiability-v2/contract.md` | `9a44687bb43edd524ec3dcbca227410d507295681d19ca731463ffb03a9d64fe` |
| `runs/online-subgradient-differentiability-20261003/blind-reconstruction-v2.md` | `89e90ba9abad3c07c3c7150f50fff62cef83b97a56ed4c22dc408285ca3d56a9` |
| `runs/online-subgradient-differentiability-20261003/full-source-review.md` | `3f3879582d6796e6edda2221cb8b2b1af65ac33f5d1d9108b01f22be8426a14f` |
| `Tests/OnlineSubgradientDifferentiabilityCanary.lean` | `078d21522145b948421a81eb99f66298fb141688858dad3502572fba703b0106` |
| `BanditRLProof.lean` | `fe07cfaadbef5f14118e347e21a4056e2f043ba6a9dd0b191b8f04e447bd87e8` |
| `Tests.lean` | `1520101caa18584aa7647a3717c1590f2ab8bb2df8df72b6ac0bf2e384a09a4e` |
| `website/content/books.json` | `a78dc57de707f7c79f622e366e5caac552b0ea50ca161572238b27e4c53cc642` |
| `website/content/chapters.json` | `79a137cb2db98f2cd979dd62bfda89d4e90ca7ba1e2a847fac821292ffaa8b38` |
| `website/content/readings.json` | `ece6f08b14601b0b98674a81ebc6c2f1915ae5f5a597e2b135224bc0ce9a2eaa` |
| `website/content/highlights.json` | `81e5a48ed734fa03d126fef9da0b9b65b97124febf5c1a7610ce80da6782cb12` |
| `docs/contracts/online-book-v1/source-inventory.json` | `3742415ee505a04b6049f2647c471b78a36474e1d13cfb5870a760f15dc9c0cc` |
| `runs/online-subgradient-differentiability-20261003/public-canary01.log` | `8a2325c5039e230733172fb43b2261b7cfca613fd7f226a0598c1941a703d3ff` |

The pinned original source PDF, freshly verified during the preceding full-source review, is `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Its directly extracted physical page 29 / printed page 17 is the source anchor. This receipt does not replace that source binding or certify a different PDF edition.

## Seven semantic slots

| Slot | Public presentation and canary assessment |
| --- | --- |
| 1. Objects/spaces | The reader explicitly retains extended-real f and finite-dimensional real inner-product geometry representing source Euclidean space. The real-representative definition is explained, and examples use the actual extended indicator, not a finite penalty surrogate. |
| 2. Quantifiers | The contract states equivalence with existence of a singleton global support set and identifies its element for every admissible local representative h. Support inequalities range over every ambient y. No merely local/domain-restricted support is substituted. |
| 3. Assumptions | Convexity and finite f(x) remain terminal inputs. Properness, ambient interior, local Lipschitz bounds and continuity are described as derived. Neither prose nor canaries replaces the full terminal by an interior-only theorem. The constrained examples prove their concrete local facts rather than adding them to the theorem statement. |
| 4. Conclusions | Reader states the full iff and separate actual-gradient identity. The reverse canaries use the full equivalence and the stronger exact HasGradientAt producer. Boundary nondifferentiability is concluded from two distinct actual supports, not from failed proof search or a missing gradient instance. |
| 5. Constants/normalization | Indicator values are zero/top. Quadratic support and derivative at 1 are exactly 2. Boundary supports 0 and -1 are distinct and admissible. The residual proof bridge retains the norm product and little-o interpretation. |
| 6. Probability/feedback | All claims are deterministic convex analysis. Classical support selection and compactness are not presented as an online algorithm, random estimator, or measurable selection. |
| 7. Boundaries/completion | The reader excludes general infinite-dimensional equivalence and sum/max rules. The chapter explicitly limits completion to Theorem 2.22 and gradient identity; later Chapter 2 and book obligations remain mandatory. Candidate/local compilation is kept separate from combined acceptance and deployment. |

## Canary verification by source inspection

The public canary imports `BanditRLProof`, and that root imports the actual differentiability module. `Tests.lean` imports the new canary. Thus the visible examples are routed through the shared project; they do not define an isolated per-book library or redeclare the source theorem.

- **Genuine constrained interior:** the indicator of [0,2] has positive-infinite values outside the interval. At 1, the canary constructs neighborhood equality to the zero real function and invokes the generic gradient identity to obtain support set {0}. A second theorem invokes the reverse implication of the full equivalence to produce `SourceDifferentiableAt`. This exercises the actual reverse endpoint with an extended-real function.
- **Nonzero derivative:** the quadratic support set at 1 is identified as {2} through the generic gradient identity plus the shared actual quadratic support. The next test invokes `singleton_subdifferential_hasGradientAt` to produce exactly `HasGradientAt (fun y => y^2) 2 1`. The reverse test therefore checks a nonzero gradient and the stronger exact producer, rather than merely an existential differentiability output.
- **Finite boundary:** the indicator at 0 is finite. The canary directly proves every nonpositive scalar is a global support there, with separate interior-of-interval and positive-infinite-exterior cases. In particular 0 and -1 are supports. Assuming differentiability, the full forward theorem would make both equal one singleton element, a contradiction. This faithfully demonstrates ambient nondifferentiability at a finite boundary point.

The support singleton used by the reverse canaries is obtained through an independently available forward/gradient route; this is a useful integration round trip, not a proof that the reverse theorem is correct merely because it recovers a known derivative. The separately inspected reverse construction remains the mathematical evidence for generality. These three examples do not establish all boundary cases or any infinite-dimensional extension.

## Reader formulas, proof bridge and dependencies

The prose and contract accurately preserve the source assumptions and distinguish the full equivalence from its gradient companion. The display `f differentiable at x iff partial f(x)={gradient f(x)}` is a schematic summary whose rigorous reading is supplied immediately by the fallback and contract: the iff is with existence of a singleton, and the singleton equals `gradient h x` for every differentiable local real representative. It must not be interpreted as introducing a total extended-real gradient unrelated to that representative. The highlight for the full terminal uses the explicit existential singleton formula.

The proof bridge correctly describes derived interior membership, uniform bounds on all nearby supports, compact cluster-point identification and the Frechet residual. It does not replace a uniform neighborhood statement by convergence along a single direction or assume the derivative being constructed. The forward explanation correctly uses local finiteness to derive nowhere-bottom before applying the shared first-order theorem.

The eight new highlights summarize intermediate dependencies, the exact reverse producer, and the two source endpoints. Their source-position text calls intermediate declarations proof dependencies rather than independently printed source theorems. Local dependency arrays are partial teaching links, not an exhaustive actual proof-term graph: for example the full theorem reaches its gradient companion through the forward helper, while some dependency arrays are empty despite real imported prerequisites. No conclusion that a declaration has no dependencies follows from an empty teaching list. A generated actual declaration graph must be validated separately. The finite-neighborhood helper's highlight presents its inner-product specialization used here; the inspected helper itself is more generally stated on finite-dimensional normed space. This is a valid specialization, not an added input to the source endpoint.

## Inventory and evidence status

The Theorem 2.22 source-inventory record points to both `theorem_2_22` and `theorem_2_22_gradient`, remains required, and currently says `public-compiled-candidate; combined acceptance pending`. That is consistent with the reader's candidate status and is not a merged/live claim. The Online Learning book record remains source-mapped with scoped results and explicit remaining obligations. The new chapter's completion definition is only this theorem plus its gradient clause.

The public canary log ends with **Build completed successfully (9074 jobs)** and records builds of the shared root and `Tests.OnlineSubgradientDifferentiabilityCanary`. Its displayed canary and endpoint axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. These are observed compilation-log facts, not the reason for source-semantic acceptance. This receipt neither reran that command nor extends it to an unseen combined `Tests`/harness gate.

## Verdict, remaining work and frozen scope

**Accepted-with-explicit-delta**, preserving the coordinate-free finite-dimensional and local-real-representative interpretations from the full-source receipt. No proof, formula, reader or canary edit is required by this review.

The byte bindings above are the reviewed snapshot. Any later inventory change from candidate to accepted-local is a new metadata revision and must have its delta and gate evidence bound separately; this receipt does not pre-authorize or certify that future status. Final LF-normalized review bindings must explicitly relate their normalized bytes to this raw snapshot rather than replacing raw hashes silently.

This is only local automated semantic/public-presentation review. Combined acceptance, generated-site validation, final binding verification, merge and live publication remain separately evidenced steps. Chapter 2 and the book remain incomplete.

## Final curated-route update before receipt freeze

The complete current `online-subgradient-differentiability` reader entry was reread after the schema-driven teaching-route reduction. Final raw SHA256 of containing `website/content/readings.json`: `e27b728dfac0c1137884d7b9b66cf42265c0a56e55b87dc27d89ce3e3a0d2c12`. The earlier hash `ece6f08b14601b0b98674a81ebc6c2f1915ae5f5a597e2b135224bc0ce9a2eaa` remains above as the initially reviewed snapshot; this appendage binds the final reader version rather than silently overwriting it.

The four selected route declarations are `singleton_subdifferential_interior`, `singleton_subdifferential_hasGradientAt`, `theorem_2_22`, and `theorem_2_22_gradient`. This is a curated reading route, not an exhaustive proof dependency graph. Omitting the local-bound, closed-graph and compactness declarations from this short route does not remove them from the proof: the detailed reader bridge still explains them and the actual Lean proof retains them. The current formulas, assumptions, gradient companion, constrained/nonzero/boundary examples and completion limits remain accurate.

Verdict remains **accepted-with-explicit-delta**, with no mathematical repair required. The reported initial site-schema failure is not superseded into a successful site build by this semantic review; its historical log must remain preserved and later site validation is separately required. This receipt is now frozen at the explicitly recorded raw snapshots.
