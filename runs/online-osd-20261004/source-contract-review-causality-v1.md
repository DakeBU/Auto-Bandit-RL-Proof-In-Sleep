# OSD causality v1 independent source-contract review

Verdict: **accepted-with-explicit-delta**, restricted to stabilization of eight exact headers and the proposed dependency DAG. No target proof body was supplied, reviewed or compiled. Actor `/root/source_reviewer`, requested GPT-6 Astra / medium; distinct automated source reviewer, external_human=false. Runtime model identity is not independently verified.

All 19 actual contract-directory files were read (context, contract, manifest, eight headers and eight native JSONs; the assignment's count18 was off by one). The new blind packet, reconstruction and receipt were read independently. Original PDF was rehashed and freshly extracted: Definition2.20 and subdifferentiability printed16-17/PDF28-29, Lemma2.31 printed19/PDF31, Algorithm2.2 printed20/PDF32. Raw digest is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Actual SourceProper, SourceSubdifferential, subgradient_point_finite, Domain, project and project_spec were inspected; whole dependency files are hashed but unrelated declarations are not certified.

## Seven semantic slots

1. **Objects and source hypotheses.** Finite-dimensional real inner-product E is a coordinate-free representation of source Euclidean space; no positive-dimension assumption is added. V is actual nonempty closed convex Domain. Properness inherited from Definition2.20 excludes bottom and supplies one finite witness. SubdifferentiableOn requires actual global supports at every feasible point, not merely inequalities restricted to V. Loss convexity, differentiability, boundedness and interior are not extra hypotheses.
2. **Selection and finite values.** currentSubgradient_mem asserts that the actual classical selected vector is a support at feasible x under SubdifferentiableOn. Its hx is appropriate here: unlike standalone Lemma2.31, this target supplies no independent hg at arbitrary x, and outside V the selector may use fallback0. finite_loss asserts EReal equality f(x)=coe(toReal(f(x))), which genuinely excludes infinities. Existing proper-support finiteness supplies a viable producer; toReal alone does not. The requested DAG does not assume these conclusions.
3. **Feasibility and strict prefix.** iterate_mem covers t=0 through feasible x1, and all successors by actual projection membership. It legitimately needs neither positive steps nor regular prior losses, since the total selector/projection still constructs feasible points. iterate_prefix holds for the same V and x1 under equality of both schedules and entire loss functions at all s<t. It does not demand current or future equality. At t=0 both antecedents are vacuous and predictions equal x1. This precisely specifies structural prefix invariance, not an observed-value-only oracle model. Future information encoded in externally supplied x1 or schedules is outside the guarantee.
4. **Current-round support and finiteness.** iterate_support and iterate_finite_loss require only current loss validity, plus feasible initialization (and feasible u for the latter). Prior invalid losses/steps can still yield feasible points because projection is total. Therefore no all-history validity premise is silently needed. The two finite equalities use the same current loss at the actual iterate and every feasible comparator. To apply them on a whole horizon later, validity must be supplied round by round.
5. **Same-trajectory single-step conclusions.** one_step_chain uses precisely the selected support at iterate(t), and its negative residual uses iterate(t+1) from the same V, schedule, loss sequence and x1. Both eta-scaled inequalities retain their original coefficients and eta-squared correction. one_step divides the complete squared-distance difference by 2*eta(t), with eta(t)/2 times support norm squared. Strict current positivity is explicit. No desired inequality is an input. These are valid algorithmic specializations of the arbitrary-x source lemma, not a replacement that narrows it.
6. **Information and representation deltas.** Source allows any support; this implementation fixes one noncomputable canonical allowed choice from current whole f,x. It does not model every possible adaptive tie-breaking rule or provide executable selection. The general arbitrary-g Lemma2.31 remains separate. Source output-before-loss order is represented by iterate0=x1 and the current loss updating only iterate(t+1). No comparator/horizon enters the selection/update. Prefix invariance is a newly explicit formal obligation extracted from that order. Singleton, lower-dimensional/unbounded domains and dimension0 remain allowed; no nonempty interior. Regret is merely defined here, including T0, not bounded.
7. **Blind correspondence and evidence.** Fresh blind reconstruction correctly decodes all eight headers, especially full-function strict prefixes, current-only loss regularity, actual finite witnesses and true next iterate. Tool comparison verifies every native statement text equals its whitespace-collapsed header, all eight manifest/native hashes agree, and the context raw digest matches the manifest. No body or compile evidence is supplied for these targets. The DAG is a proposed mathematically sufficient route, not a compiled proof-term graph: projection -> feasibility; support nonempty -> selection -> finite conversion; recursion -> prefix; these -> actual current support/finite loss; full lemma + recurrence -> chain -> positive division.

## Decision and remaining boundaries

No mathematical header repair is required. The eight targets are a faithful implementation obligation set for one permitted source support-selection rule, with explicit coordinate/EReal/indexing/selection deltas above. This acceptance does not assert proofs of causality, feasibility or one-step algorithm guarantees already exist.

Nonblocking historical metadata: manifest.fixed_performance says separate not-yet-frozen contract. It is not authoritative about the later separate performance package; that package was deliberately not inspected here. Preserve these frozen bytes and record any later workflow status in a new overlay. No scope for cumulative/fixed/variable/tuned source guarantees is accepted by this review.

All eight bodies, semantic body review, public integration and combined gates, reader/site, immutable bindings and PR acceptance remain pending. Performance contracts require their own independent review. Example2.32, Chapter2/book, persistent Goal, older migration and main/live completion remain open. No native trial or production/contract/old-receipt/frontier edits were performed.

## Raw SHA256 inventory

Exact raw bytes; no normalization or JSON reserialization. Scoped dependency reads are disclosed above.

| File | Raw SHA256 |
|---|---|
| `docs/contracts/online-osd-causality-v1/context.txt` | `b162f92f05924622d248b0673321078b35330dc3980f7b53c1adc4ba64087a5c` |
| `docs/contracts/online-osd-causality-v1/contract-manifest.json` | `b53c534562dab163e6675d13aafa57cdcf8dac6bdc688ed1c5e97523d11647e0` |
| `docs/contracts/online-osd-causality-v1/contract.md` | `cc0f92e6039ba7c91e9016b5d081c85a9a767f17c0eb724d5c8edf6592db8ac8` |
| `docs/contracts/online-osd-causality-v1/currentSubgradient_mem-header.txt` | `d2124e5873f09c451184cf0ce630c4d595ebc46b7d272a45f040130cbc8d8edf` |
| `docs/contracts/online-osd-causality-v1/currentSubgradient_mem.json` | `7dfe0d48d81131c73f5dfd3c8adb0c23ff51107502ed630f392506474e93a44b` |
| `docs/contracts/online-osd-causality-v1/finite_loss-header.txt` | `a92185b3142ca6cde24d3b26f50ea64e01605ac85afd036bff829226b1395911` |
| `docs/contracts/online-osd-causality-v1/finite_loss.json` | `7ec1c933965f9c1e06d4438ad24391d925072537c2589229e717582a385a6760` |
| `docs/contracts/online-osd-causality-v1/iterate_finite_loss-header.txt` | `6eb9e327784e0132bd1082043b8342dea0f822c9a0461eb179cbd6c6148df739` |
| `docs/contracts/online-osd-causality-v1/iterate_finite_loss.json` | `1e766d2997eb6c11a69ec5f67182c5c5089b264596c1f6ebd355e99c5bc2eab2` |
| `docs/contracts/online-osd-causality-v1/iterate_mem-header.txt` | `8d6c7da81d36ac5e1f2f3b632078422be1f2a15a9284b28dc29014102b605a44` |
| `docs/contracts/online-osd-causality-v1/iterate_mem.json` | `5d22ee9701aa8d52cad6555d9180902700dc6c7948d54e8bc6a3922b23ea7e81` |
| `docs/contracts/online-osd-causality-v1/iterate_prefix-header.txt` | `1bc568dd80566655cfe3cf939cb1566a128ed8fdec4ac6fc4c4c0de1737f9e70` |
| `docs/contracts/online-osd-causality-v1/iterate_prefix.json` | `db4f55a2d5aa6dcbc156665642aabdd00f3edee0cd6565e5033380570001d158` |
| `docs/contracts/online-osd-causality-v1/iterate_support-header.txt` | `d7ad089360795ff40b9e322781736fcbece1852ebe4e8f799d89127b9ee99d45` |
| `docs/contracts/online-osd-causality-v1/iterate_support.json` | `39ccd63efe480aa3bbf4737b8a1c72537b7f50db2a4347b77e5c3cde00f7bde4` |
| `docs/contracts/online-osd-causality-v1/one_step-header.txt` | `3a0c8aefdca96c1605dc1113666c9c46953a86e417eb3d9da95b54444338ef0a` |
| `docs/contracts/online-osd-causality-v1/one_step.json` | `4627dacd069960fde5ec06e087b9aec371e5d985abe246968b8e16b2a772b918` |
| `docs/contracts/online-osd-causality-v1/one_step_chain-header.txt` | `e5ad2f3469128ba4932959e9bf3dda8bd0fdfa7e0a04e736b7e334f93fc45c96` |
| `docs/contracts/online-osd-causality-v1/one_step_chain.json` | `823d4f5a1589286a8b6e53633e499f91cf082a5131b62bd4bdd6513e392824ca` |
| `runs/online-osd-20261004/blind-packet-causality-v1.txt` | `9b89a109bce588ab1d043f88827238acda08abfea92fd2bda9265956bab5c3f8` |
| `runs/online-osd-20261004/blind-reconstruction-causality-v1.md` | `a440c2821de3fc7baae6e21f688760acd3174307fe3d8354e79a5d800df9d82c` |
| `runs/online-osd-20261004/blind-receipt-causality-v1.json` | `b153c7f0fb1feb46dff1a14ae796e03909711318849268096e219c826567a5fc` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
