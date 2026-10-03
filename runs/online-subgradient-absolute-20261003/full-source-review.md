# Example 2.24 full source/body review

Verdict: **accepted-with-explicit-delta for the four inspected public proof bodies and their scalar canaries**. The delta is the finite real-to-EReal embedding used to share SourceSubdifferential. No mathematical repair required. This is not final public-package/reader acceptance, combined harness/site evidence, committed-byte binding, external-human review, merge/main/live status or Chapter 2/book completion.

Actor: `/root/source_reviewer`, distinct automated reviewer, requested GPT-6 Astra / medium; 2026-10-03. Earlier draft and failed records remain untouched.

## Source and scope

I freshly extracted the original pinned PDF physical page30/printed18 and independently rehashed it as cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Example 2.24 gives exactly {1} for x>0, [-1,1] for x=0, and {-1} for x<0.

I read the complete actual public module and public canary, all four frozen headers, full-leaf02 and full-canary02 logs, public-focused01 completion/axiom tail and public-frozen-check JSON. For failed full-leaf01/full-canary01 logs I inspected error and sorryAx lines, not every diagnostic context. The v2 packet/reconstruction and native contract files were fully read in the preceding contract pass; their semantics are retained for comparison and current hashes bound here. The v2 reconstruction's concluding scalar/boundary assessment was reread. Imported Basic inspection is limited to imports, namespace/typeclass context and actual SourceSubdifferential definition, not other production proofs. No build was rerun by this actor.

## Seven semantic slots

| Slot | Body-level result |
| --- | --- |
| 1. Objects/spaces | Fixed scalar real absolute value, finitely embedded into EReal. No arbitrary-dimensional norm theorem is claimed. Generic Basic context is a real inner-product space, specialized here to real numbers. |
| 2. Quantifiers | Every real query x, every candidate slope g, every real comparison point y. Necessity uses selected witnesses from that global inequality; sufficiency reintroduces arbitrary y, including the opposite sign. |
| 3. Assumptions | Positive and negative leaves assume only their respective strict sign; zero has no premise; the whole-line terminal has no extra premise. No convexity/properness/differentiability/support-existence assumption is inserted. |
| 4. Conclusion | Exact set equalities with both containment directions. The proof determines every support, rather than selecting a convenient slope. |
| 5. Constants | Slopes exactly +1 and -1; origin interval includes both endpoints. Real inner product/coercion reduction introduces no scale or reversed sign. |
| 6. Probability/information | Deterministic scalar analysis; no stochastic, causal, algorithm or regret scope. |
| 7. Boundaries | Zero is handled separately with the entire closed interval. Whole-line if branches are exhaustive; final branch derives x<0 from not(0<x) and x!=0. No point is dropped. |

## Actual necessity/sufficiency audit

At zero, necessity applies the assumed global support at y=1 and y=-1. Reversing EReal.coe_add and using coe_le_coe_iff reduces to real inequalities giving g<=1 and g>=-1. Sufficiency takes an arbitrary g in Icc and an arbitrary y. For y>=0, multiplying g<=1 by y yields yg<=y=abs(y). For y<0, multiplying -1<=g by the nonpositive y reverses the inequality and gives yg<=-y=abs(y). Thus all interior slopes and both interval endpoints really satisfy the global relation.

At positive x, necessity tests y=0 and y=2x, uses abs(x)=x and abs(2x)=2x, and derives x*(g-1)=0. Strict positivity supplies x!=0, hence g=1. Sufficiency substitutes g=1 and proves the global supporting inequality for arbitrary y via y<=abs(y); it is not restricted to positive y.

At negative x, the same two test points use abs(x)=-x and abs(2x)=-2x, yielding x*(g+1)=0 and g=-1. Sufficiency substitutes -1 and uses -y<=abs(y) for arbitrary y. The two signs are not exchanged by the scalar inner-product representation, which appears as (y-x)*g in the coercion-normalized inequalities.

The terminal splits first on 0<x, then x=0; in the remaining branch it proves x<0 by total real order and invokes the actual negative leaf. All three branches call the proved exact characterizations. There is no assumed terminal, chosen-subgradient surrogate, missing reverse implication or local-support substitute.

The actual headers match the frozen source statements. The v2 blind reconstruction faithfully describes these statements and the actual reused definition. Real coercion preserves finite addition and order; all source function values and inner products are finite, so no infinity-convention delta arises here. The only representational change is use of the shared EReal-valued API.

## Canary and technical evidence

The public canary imports the actual public module. zero_boundary_canary checks both -1 and +1, the fractional slope 1/2, and exclusion of 2 at zero. zero_is_not_a_singleton derives a contradiction from the two distinct endpoint members. source_three_branches_canary invokes the all-x terminal at 2, -2 and 0 and checks its exact outputs. These are useful source-boundary consumers; they do not replace the body-level proof or claim that testing a few points establishes a universal theorem.

full-leaf02 reports all four declarations with only propext, Classical.choice and Quot.sound. full-canary02 reports those four plus the three canaries with the same standard axioms. public-focused01 ends with successful build of the public module and public canary (3289 jobs), with all three public canary axiom prints standard. public-frozen-check reports all four actual public statements equal to their original prebody fingerprints, with no findings. Compiler/fence observations are separate from this semantic judgment, and log bytes are not themselves immutable execution-to-source manifests.

full-leaf01 contains a failed terminal-order proof and sorryAx; full-canary01 contains a failed branch-canary simplification and sorryAx. Both failed runs are rejected as validation and must remain historical evidence. Their later repaired results do not retroactively make them successful. This reviewer did not rerun compilation.

## Limits and next acceptance stage

No repair is requested for these mathematical bytes. The reader, source inventory/status wording, public root/Tests integration, combined harness and site evidence, and final immutable binding remain for a separate final public-byte review. This report accepts neither subsequent normal-cone/max/OSD obligations nor completion of Chapter 2 or the book. It preserves the contract receipt's historical unproved stage rather than rewriting it.

## Independently measured raw SHA256

Current raw filesystem bytes, without newline normalization or reserialization. Paths relative to E:/ABRL/worktrees/research-online-book. Hashes of containing files do not expand the scoped read claim above.

| File | Raw SHA256 |
| --- | --- |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `Tests/OnlineSubgradientAbsoluteCanary.lean` | `5234ba8106382687d2b56396f205c257648d89daa8177a696c91ff404bea3b46` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `runs/online-subgradient-absolute-20261003/full-leaf01.log` | `b38eb4d6ca5aec28a5613eb61d61bfdd14e2d9c4cc4e98159e072fda898c0d82` |
| `runs/online-subgradient-absolute-20261003/full-leaf02.log` | `d875ebd3b6220816e92a0b1db40eddf5b33fa4463253efb36ce2fdc2955b7bc3` |
| `runs/online-subgradient-absolute-20261003/full-canary01.log` | `9f7fa495367a9ccf68146740d12de81364ff202299ef4b178b8c14b720658bf8` |
| `runs/online-subgradient-absolute-20261003/full-canary02.log` | `3505eb69592d5c84c1d051cde4f7f4d45f7b5092518229c14f919ae2c8b5cfe6` |
| `runs/online-subgradient-absolute-20261003/public-focused01.log` | `1d45ead248a4bb70a78bf503b1e1da6e6356a84c1500c8c2d4b370b7ada1095f` |
| `runs/online-subgradient-absolute-20261003/public-frozen-check.json` | `8036dae55a92e2cb2d3334e13bc4d8bc9db57ddb6c76a8b25802d3256adf7066` |
| `runs/online-subgradient-absolute-20261003/blind-packet-v2.txt` | `9d65343f308bb4bae9a569afb88c0f94240f8a35b523d71ae74afbf0fb1a1156` |
| `runs/online-subgradient-absolute-20261003/blind-reconstruction-v2.md` | `9845fd5ba702a59424dc40b21f028b9bba99e206cf8aabccf1d8b614312df9ca` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_negative-header.txt` | `f359b9dd5e7dd8e6009b5d0835565cbe368b6ccd1e625d234b25bd03e52b1108` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_negative.json` | `0e808e2f48a678e87afb260fc91df4d530c469304ac61a8c7a7d6a37379ca524` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_positive-header.txt` | `cfb2df66eda35e65a83318b5b59f570e56b9afa4f11d0dcdf372d6f9b1ad856d` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_positive.json` | `8c4370b9c55e3c88a6358029f63b0916211df587ffe66fb72567eefbcaa3f8fb` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_zero-header.txt` | `c5f9745262f576971cf7096bc268258885b391dd0bef85786e1c81dcc1d8b332` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_zero.json` | `bc325ee4fd9ef8cd7e6e34194c8782133c8e32fc069492c59d33e34ea56b5ca0` |
| `docs/contracts/online-subgradient-absolute-v1/context.txt` | `ecb3d1316f53b564bd8cd52a1af4b38c83c2b9f31d043595b0f1d87a851f8ba9` |
| `docs/contracts/online-subgradient-absolute-v1/contract-manifest.json` | `433327d2dc9af0b8463812ff249b50e6bcdca7793f6b3701463e9a4925704f27` |
| `docs/contracts/online-subgradient-absolute-v1/contract.md` | `6365f9c7eb76281e9b9eced733c802b60134a2670fc5e93c2c8fe6c87a1eb45d` |
| `docs/contracts/online-subgradient-absolute-v1/example_2_24-header.txt` | `b0322da57a4477f93638dd5845349c715b519a441bbafe15d28f785d7f66d118` |
| `docs/contracts/online-subgradient-absolute-v1/example_2_24.json` | `302d299be4bcc52eb3fc7c9fd8defb5d7e759281e66a329ba0220771a01deb30` |
