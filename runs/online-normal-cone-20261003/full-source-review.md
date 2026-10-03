# Example 2.25 full source/body review

Verdict: **accepted-with-explicit-delta for all three inspected public proof bodies and their canaries**. Coordinate-free finite-dimensional real inner-product presentation and the shared EReal indicator/support representation are explicit deltas. No mathematical repair required. This is not final reader/package acceptance, root/harness/site validation, committed-byte binding, main/live status, external-human review, older-stack migration or chapter/book completion.

Actor: `/root/source_reviewer`, distinct automated anti-anchored reviewer, requested GPT-6 Astra / medium; 2026-10-03. All previous receipts and failed evidence remain untouched.

## Original source and read scope

I freshly extracted original PDF physical30/printed18 and independently rehashed the pinned Orabona v10 PDF as cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Example 2.25 states the indicator-normal-cone correspondence, zero interior cone, and full nonnegative radial normal cone of the closed unit ball at norm-one points. All three have actual bodies here.

I read complete OnlineNormalCone.lean and OnlineNormalConeCanary.lean, all three frozen headers, successful full-leaf03/full-canary01 logs and public-frozen-check JSON, and public-focused01 completion/canary-axiom tail. Failed full-leaf01/02 inspection covers error and sorryAx lines, not all diagnostics or saved candidate snapshots. The v1 context/contract/manifest/native JSONs, neutral packet and complete blind reconstruction were read in the preceding continuous contract review; their meanings are retained and hashes rebound here. The reconstruction's final boundary assessment was reread. Existing Basic/Extended/ClosedProper inspection is scoped to the shared definitions and proper-indicator/domain/point-finiteness interfaces described in the draft receipt, not unrelated proofs. No gate was rerun by this reviewer.

## Seven semantic slots

| Slot | Body-level finding |
| --- | --- |
| 1. Objects/spaces | All three source terminals retain explicit FiniteDimensional over a real inner-product space. Normal cone includes feasible query membership. Indicator is the existing zero/top function. |
| 2. Quantifiers | First equality holds at every x and every candidate g, with support tested globally over ambient y. Cone tests all feasible y. Interior is ambient interior. Unit-ball equality characterizes every normal g through an existential nonnegative coefficient. |
| 3. Assumptions | Nonempty convex V retained in first two, despite some unused warnings. No new closedness, boundedness, full-dimensionality or assumed normal/decomposition hypothesis. Unit-ball input is norm(x)=1. |
| 4. Conclusions | Full exact set equalities, both necessity and sufficiency. The hard radial reverse inclusion constructs alpha=norm(g), rather than assuming parallelism or giving only alpha*x inclusion. |
| 5. Signs/constants | Outward inner(g,y-x)<=0; unit radius1; positive displacement coefficient; ray coefficient>=0 including0. No orientation flip, strict-ray replacement or open-ball substitution. |
| 6. Probability/information | Pure deterministic geometry, no algorithm, stochastic or causal claim. |
| 7. Boundaries | Indicator supports empty outside V; zero normal included; interior conclusion only for ambient interior points; thin singleton can have all normals; unit-boundary zero vector case handled explicitly. |

## Actual producer audit

Indicator equality derives SourceProper of the indicator from the actual nonempty premise. Given a support g at arbitrary x, subgradient_point_finite and effectiveDomain_indicator derive x in V; query feasibility is not an extra input or assumed conclusion. For any y in V the global support inequality reduces to the real normal inequality. Conversely the actual guarded normal supplies query feasibility; feasible test y uses its inequality after finite coercion, while infeasible test y has top on the right. This proves both directions for every x, including the outside-domain regime.

For interior normals, a nonzero candidate g has positive norm. Ambient interior supplies r>0 with the metric ball inside V. The proof constructs a=r/(2*norm(g))>0 and proves norm(a*g)=r/2; consequently x+a*g is genuinely feasible. Its normal inequality becomes a*norm(g)^2<=0, contradicting positivity. The reverse direction constructs the zero normal from interior_subset and the zero inner product. It neither assumes an available feasible direction nor silently applies relative interior.

At unit-ball boundary, the zero normal is split off and represented by coefficient0. For nonzero g, the normalized vector g/norm(g) is proved feasible by norm normalization and tested in the actual normal inequality. This yields norm(g)<=inner(g,x). Cauchy–Schwarz with norm(x)=1 gives the reverse inequality, so inner(g,x)=norm(g). The norm-square identity then proves norm(g-norm(g)*x)^2=0 and hence g=norm(g)*x. The coefficient is constructed and nonnegative. The converse takes any a>=0 and derives inner(a*x,y-x)<=0 for every norm(y)<=1 via Cauchy and norm(x)=1; x feasibility follows from the same boundary hypothesis. Thus full ray equality, including zero, is genuinely produced.

Original finite-dimensional and source nonempty/convex premises remain in the exact terminal headers; unused-variable warnings are not grounds to silently remove them. No additional EReal infinity convention is needed: indicator values are0 or top, with finite inner products. Empty V remains excluded because the unguarded support predicate for its identically-top indicator would disagree with the guarded empty cone.

## Canary semantics

Public canaries import the actual module. At the left endpoint of [0,1], they admit normal -1, exclude +1 and prove the indicator support set empty at2. The singleton {0} consumer proves the complete support set univ and membership of7; it does not itself include a separate theorem that the singleton's ambient interior is empty, so that informal description must not be advertised as an additional canary conclusion. The interval midpoint consumer uses both indicator equality and the actual interior theorem to obtain {0}.

The geometric boundary consumer uses EuclideanSpace real (Fin2) with actual orthogonal coordinate vectors e0/e1. It proves2*e0 and0 belong at e0, excludes the tangential e1 by its second coordinate, and excludes -e0 using the first coordinate and coefficient nonnegativity. This tests direction and sign in genuine two-dimensional Euclidean norm geometry, not merely a one-dimensional scalar instance.

## Compilation, fence and blind evidence

full-leaf03 reports all three source declarations with only propext, Classical.choice and Quot.sound. full-canary01 reports the same for all three declarations and four canaries. public-focused01 reports successful public build3289 jobs and four public canary axiom results. Only unused source-parameter warnings appear in the displayed successful evidence. public-frozen-check reports all three original statement hashes unchanged, including explicit FiniteDimensional binders. These observed focused results support implementation status but are not a reviewer-run or combined root/harness/site gate.

full-leaf01 and full-leaf02 contain actual rewrite failures and sorryAx for the unit-ball theorem. Both are rejected validation attempts; their logs/snapshots remain historical and are not retroactively accepted. The third run's success is the relevant later evidence. Source and log raw hashes are bound separately; logs are not themselves immutable execution-to-source manifests.

The fresh neutral decoder correctly reconstructs all three original statements, guards, quantifiers, signs and boundaries. Its statement-only work is separate from this actual-body audit and not an external-human review. The native statement fences preserve the source-facing contract; API retrieval and unused source assumptions do not add or remove mathematical claims.

## Limits and next stage

No versioned mathematical correction is needed for the inspected bytes. Reader/status/source-inventory review, root/Tests and full harness/site evidence, contribution/registry/graph gates and immutable binding are outside this receipt and remain separate. Future max/hinge/affine/Lipschitz/OSD/linearization, older-stack migration and whole-book obligations are not certified.

## Independently measured raw SHA256

Current raw bytes, without newline normalization or reserialization. Paths relative to E:/ABRL/worktrees/research-online-book. Containing-file hashes do not expand the scoped read claim.

| File | Raw SHA256 |
| --- | --- |
| `BanditRLProof/OnlineNormalCone.lean` | `95fa41f9bf3f04354b0175c1f755786e86c103040f54aed9eab5fbf8a206539d` |
| `Tests/OnlineNormalConeCanary.lean` | `b893dad6e8128fe674acb19fd7774de036e953dee8d446d1cd214d20476a2790` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `runs/online-normal-cone-20261003/full-leaf01.log` | `5ec3226c6bf1eb141eac1483e85166e196b2f5ef3010f2c56b304d021c697bda` |
| `runs/online-normal-cone-20261003/full-leaf02.log` | `5ec3226c6bf1eb141eac1483e85166e196b2f5ef3010f2c56b304d021c697bda` |
| `runs/online-normal-cone-20261003/full-leaf03.log` | `3d17ce8c5be56b7674ca85de195b020d7d63923ae7877c34616f424812106255` |
| `runs/online-normal-cone-20261003/full-canary01.log` | `e90d011347e2558c0eb0f361a8d0c82682fa6e55b236ebe69ac2bb8a3916bd89` |
| `runs/online-normal-cone-20261003/public-focused01.log` | `964c31fd66d3d60daff8a3a64a2e0cf447bd52d83d5af4a4631fb909f8bf2628` |
| `runs/online-normal-cone-20261003/public-frozen-check.json` | `d286e94a0e20d076d99135973f1eb24cad3c875cf91be40fd9d402d55ff86d5b` |
| `runs/online-normal-cone-20261003/blind-packet.txt` | `0136781723e141c14e87ef5b545c9b0eccea3e8051f636693e49088101e83aca` |
| `runs/online-normal-cone-20261003/blind-reconstruction.md` | `e5b917f3c71c0978f903b70b2e77971a7ffcd26b0c6ff7a6551305ffc2d45b3a` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `docs/contracts/online-normal-cone-v1/context.txt` | `068e3271455ee2598a947fc435ae78be3fcc49ed465cde68bdded7bf9c4df8ea` |
| `docs/contracts/online-normal-cone-v1/contract-manifest.json` | `d4b497e5826568219537d53d6151af1fc4929d6da67d839afa1ee2e9e6795500` |
| `docs/contracts/online-normal-cone-v1/contract.md` | `b571970881b07ffab41ccae79b52fb6e204c57c285a2f3f29ca13979869a69f2` |
| `docs/contracts/online-normal-cone-v1/indicator_subdifferential_eq_normalCone-header.txt` | `91c76b33e4552368f14ab3f59f2ef31dd3cef7415f89973508ce7ecd2cac0b5c` |
| `docs/contracts/online-normal-cone-v1/indicator_subdifferential_eq_normalCone.json` | `055435f3b6c3566ae6c2b92ab02cdf403565729d05d97a530fa18545c0a83a49` |
| `docs/contracts/online-normal-cone-v1/normalCone_interior_eq_zero-header.txt` | `db5028f1286da0c04191937a156d37acb9532c58d0732127b90179cf70fee50c` |
| `docs/contracts/online-normal-cone-v1/normalCone_interior_eq_zero.json` | `e5cb693a137886ea057180d0e4f27d33e0cb72a235e2accb72823634fd5745a4` |
| `docs/contracts/online-normal-cone-v1/normalCone_unitBall_boundary-header.txt` | `b64fb6f90981f9585ccfaa2f85168cf66383e179abbdb4472457c5ae97134779` |
| `docs/contracts/online-normal-cone-v1/normalCone_unitBall_boundary.json` | `a3ab600507e3c1499a4219204a5f23d2c62ca5c4a5eae3d5c9c5b68bcf8b1ae2` |
