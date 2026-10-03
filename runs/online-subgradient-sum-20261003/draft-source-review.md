# Draft source review: Theorem 2.23 sum rule

Verdict: **accepted-with-explicit-delta for contract stabilization only**. Both inclusion and mixed-qualified equality remain mandatory proof obligations. No proof body, compilation, public acceptance, Theorem 2.23 closure, Chapter 2 completion, main acceptance or live deployment is certified.

Actor: `/root/source_reviewer`, separate automated anti-anchored reviewer; requested GPT-6 Astra / medium; date 2026-10-03. This is not external-human review. The source-blind reconstruction is by the distinct fresh actor `/root/sum_blind`; its own model-provenance disclosure is retained rather than replaced by an inferred model identifier.

## Independent source and file receipts

Worktree: `E:/ABRL/worktrees/research-online-book`. The original cached PDF `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf` was independently rehashed as `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the pinned Orabona arXiv:1912.13213v10. I freshly extracted physical pages 29–30 directly from that PDF with pdftotext, and read the supplied `tmp/next-subgradient-sums-source.txt`. Theorem 2.23 on printed17–18 gives inclusion for proper components and, additionally, equality under component convexity/closedness and the mixed common-domain/interior condition.

Contracts, manifest, endpoint JSON and new blind reconstruction were read completely. For the three imported production files, I reread the exact definitions and immediate scoped context of SourceClosed, SourceProper, SourceSubdifferential, effectiveDomain, realEpigraph and IsConvexExtended, plus the point-finiteness implication. Hashes below bind containing-file raw bytes; they are not a claim to have newly reviewed every unrelated declaration.

| File relative to worktree | Raw SHA256 |
| --- | --- |
| `docs/contracts/online-subgradient-sum-v1/context.txt` | `7c49b10c1e933dac2f41ebfb195151224156c14f6ef81fed82a5c4269d5ee1d8` |
| `docs/contracts/online-subgradient-sum-v1/inclusion-header.txt` | `9cd548022c463e6be3631685a7c687116b176f005341eecbb7f324f26273124b` |
| `docs/contracts/online-subgradient-sum-v1/equality-header.txt` | `04daea804ef2da692817458481240e079892c03383e83acd3b9f20f1f2ea32da` |
| `docs/contracts/online-subgradient-sum-v1/contract.md` | `5b09efee5962772ecadb5afc63a85d560c2c2483c4003b6ff61520c0bd7095ac` |
| `docs/contracts/online-subgradient-sum-v1/contract-manifest.json` | `1992bd69dba31dfca18b50640e7fb9f7708731658fc70d3bba86fd2be7578d8b` |
| `docs/contracts/online-subgradient-sum-v1/theorem_2_23_inclusion.json` | `e09198bb68b61320952decb46f359ef0633e49518b5ecf79dc12358052a16471` |
| `docs/contracts/online-subgradient-sum-v1/theorem_2_23_equality.json` | `a6b11235782600cdef78d90c4ebbe2fa7ca274bec7654530a510afa6a50f06ca` |
| `runs/online-subgradient-sum-20261003/blind-reconstruction-v2.md` | `80a186970ec70e5f6ffed7496b716d763eb9e1030e47682bf5472ceb8892e953` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `tmp/next-subgradient-sums-source.txt` | `ce46624c332bcc1684c18aae541d31bfdf3bcfd0d5a2abe040d24dbf970de31e` |

The context and two header hashes measured here match their manifest fingerprints. Endpoint JSON statement fields agree with the corresponding header statements in scope and quantifiers. Their empty `source_assumptions` arrays do not override the explicit hypotheses in those statements; they must not be presented as evidence that the endpoints have no source assumptions.

## Source correspondence and seven semantic slots

| Slot | Mismatch search and outcome |
| --- | --- |
| 1. Objects/spaces | Source Euclidean space is represented by a finite-dimensional real inner-product space. Component functions are EReal-valued; properness excludes bottom and gives each a finite witness. The sum-set is a witness-defined finite Minkowski sum of actual global subgradients, not a closure, convex hull, approximate support set or assumed decomposition. |
| 2. Quantifiers/order | Inclusion applies to every finite index type, every individually proper family and every ambient x. Equality uses Fin(n+1), hence a positive finite family. One common z belongs to the last component domain and all OTHER component ambient interiors; x is then arbitrary and need not equal z. No all-interiors condition or qualification at x is substituted. |
| 3. Assumptions | Inclusion adds no convexity, closedness, common finite point or finite-at-x hypothesis. Equality retains every component's properness, convexity and closedness as in the source. SourceClosed is exactly closed real sublevels, not a new epigraph/compactness/continuity assumption. No dual-attainment or decomposition premise appears. |
| 4. Conclusions | Inclusion is precisely Minkowski sum subset of subdifferential of pointwise sum. Equality is exact set equality for all x, including points where the sum is top. The hard reverse inclusion remains an explicit required endpoint and cannot be discharged merely by proving inclusion. |
| 5. Constants/normalization | Components and vectors are summed with coefficient one over the entire finite family. Fin.last n represents source m, with the other n indices corresponding to 1 through m-1. No averaging, weighting, convexification or limiting approximation is introduced. |
| 6. Probability/feedback | Pure deterministic convex analysis. No probability, information access, online algorithm, filtration, or measurable-selection hypothesis is present. |
| 7. Boundaries | Empty components make the Minkowski witness impossible; the resulting inclusion is vacuous. Empty generic inclusion index types are deliberately admitted, yielding zero sums. Equality is nonempty-family only; n=0 is the single-function case. Infinite component values away from domain are preserved. Ambient interior, not relative interior, appears exactly as in the printed qualification. |

## Boundary and arithmetic audit

For a witness family G at a query x, each G(i) is an actual global support of a proper component. The finite witness in properness therefore forces f_i(x) to be finite; this is a derived fact for inclusion, not an extra premise. At a test point y, each f_i(y) is either real or positive infinity. Thus the ordinary EReal finite sum never encounters mixed positive/negative infinity under component properness. The intended inclusion proof may sum the actual inequalities without introducing an alternative infinity arithmetic or assuming finiteness of all f_i(y).

If a component subdifferential at x is empty, the existential G in SourceSubgradientSum is impossible, matching the source's explicitly vacuous right-hand side. No nonempty-support assumption is needed at the inclusion terminal.

An additional definitional boundary needs to remain disclosed: component properness alone does not imply that the sum is proper, because the component domains may have empty intersection. With the existing unguarded global inequality definition, the identically-top sum has every vector as a subgradient. Under the conventional domain-guarded extension it would have none. In the no-common-point case, however, the Minkowski side is empty at every x, so the inclusion is vacuous under either convention. This is a totalized-definition scope clarification, not a nonvacuous strengthening of the source's proper-function support claim. Do not advertise meaningful support existence for an improper sum on the basis of this inclusion.

Equality's common z belongs to every component domain, since interior membership implies membership. Properness excludes bottom there, so every component is finite at z and the sum is proper. At a query x where the sum is top, at least one component is top; its subdifferential is empty, making the Minkowski side empty. The proper sum also has empty subdifferential there. The all-x equality contract correctly retains this branch instead of silently restricting to finite-at-x queries.

For the inclusion's empty index type, SourceSubgradientSum is {0} and the sum function is zero; its support set is {0} in an inner-product space. This is a valid explicitly declared empty-family extension beyond the printed positive list f1,...,fm. For equality with n=0, the last index is the only index, the other-interiors quantifier is vacuous, and qualification reduces to existence of a domain point, already supplied by properness. The conclusion is the one-component identity; it must not accidentally require the single component's interior to be nonempty.

## Blind reconstruction comparison

The v2 decoder reconstructs the actual supplied definitions, including real sublevels, properness's two conjuncts, real-height epigraph convexity, global supporting inequalities and the witness-defined vector sum. It correctly identifies the distinction between a common qualification z and the arbitrary query x, the special status of the last component, and the empty/singleton cases. Its observation about the unguarded subdifferential of an identically-top sum is correct and is explicitly scoped above. I found no mismatch between that reconstruction and the current headers/imported definitions.

## Required treatment and stabilization verdict

No mathematical header repair is required. Stabilize the two endpoints together, retaining these explicit deltas: finite-dimensional coordinate-free Euclidean presentation; arbitrary finite indexing and the empty-family extension for inclusion; witness-defined Minkowski sums; and the unguarded support convention for a potentially improper sum, where inclusion is vacuous.

The manifest correctly lists both endpoints as required and keeps draft/uncompiled status. Its dependency-search narrative is not a proof of equality and is not an impossibility claim. Inclusion work must not strengthen the terminal to convex components, add finite-at-x, or add common-domain assumptions to simplify arithmetic. Equality work must construct the decomposition from the exact mixed qualification, not assume it, strengthen it to all interiors, move it to x, or replace exact equality by a closure.

This is acceptance of the source-facing **contract**, not a successful theorem implementation. Both endpoint proofs, their actual contextual binding, independent semantic review of resulting bodies, compiler/canary evidence and later integration gates remain outstanding.

