# Inclusion candidate source review: Theorem 2.23

Verdict: **accepted-with-explicit-delta for the scratch inclusion candidate only**. No mathematical repair is required for this body. Equality remains frozen, unproved and mandatory. This receipt does not accept full Theorem 2.23, public integration, combined root/Tests, website, main, deployment or the book Goal.

Actor: `/root/source_reviewer`, distinct automated source reviewer, requested GPT-6 Astra / medium, 2026-10-03. This is not external-human review. The distinct source-blind actor is `/root/sum_blind`; its own model-provenance disclosure is preserved. The preceding contract review is contextual history, not authority substituting for inspection of this body.

## Scope and source comparison

I read the complete current scratch inclusion and canary files, all three compiler logs, frozen-statement check, all seven v1 contract files, fresh v2 blind reconstruction, preceding draft receipt, and the extracted printed17–18/PDF29–30 source. I rehashed the original PDF independently; it matches the pinned SHA256 below. I reread the exact imported SourceSubdifferential, SourceProper and effectiveDomain definitions and immediate contexts. Containing-file hashes do not imply a fresh review of unrelated declarations or the entire transitive import closure. I did not rerun compilation in this review.

The source proves inclusion by choosing one global support per component at a common query point, adding their inequalities at an arbitrary test point, and identifying the resulting support vector with their sum. The actual body follows this construction directly. `rintro g ⟨G, hG, rfl⟩ y` consumes an actual decomposition and actual support witnesses; `Finset.sum_le_sum` sums `hG i y`. `sum_add_distrib`, the real-to-EReal additive homomorphism and `map_sum`, and `sum_inner` establish precisely the sum-function support inequality for every y. There is no consumer assuming the desired aggregate support, no imported sum-rule oracle, and no local-domain restriction in the conclusion.

## Seven semantic slots

| Slot | Audit result |
| --- | --- |
| 1. Objects/spaces | EReal component functions and actual vector-family Minkowski sum in a real inner-product space. The written finite-dimensional context is retained; its unused-section-variable warning reflects proof generality, not a missing source hypothesis. Source Euclidean space is covered. |
| 2. Quantifiers/order | Arbitrary finite index type, proper family, arbitrary query x, arbitrary decomposition G, then every test y. The same x is used for every component. No hidden common finite point or x qualification is introduced. |
| 3. Assumptions | The original hp properness parameter remains in the terminal. No convexity, closedness, finite-at-x, nonempty support, or shared-domain input is added. hp is unused by the algebraic proof, as disclosed by the compiler; removing it is not part of this reviewed contract. |
| 4. Conclusion | Exactly SourceSubgradientSum f x subset of SourceSubdifferential of the pointwise sum at x. This constructs a global support from each input decomposition. It does not construct decompositions from aggregate supports and does not prove equality. |
| 5. Constants/normalization | Unweighted ordinary finite sums, coefficient one, real inner product coerced into EReal. No averaging, approximation, closure or convex hull. |
| 6. Probability/information | Deterministic statement and proof; no probability, causality, filtration or measurable-selection premise. Classical choice is a standard Lean axiom reported by compilation, not an extra mathematical support-existence premise. |
| 7. Boundaries | Empty-family inclusion is a declared extension beyond the source's positive list. Empty component supports make the input sum-set empty. Properness prevents negative infinity, but the aggregate can be identically top when domains are disjoint; inclusion is then vacuous on its Minkowski side. The all-x conclusion remains intact. |

## Arithmetic and totalized-definition boundary

The body genuinely uses Mathlib EReal ordered addition to sum the inequalities; it does not silently replace EReal arithmetic with real arithmetic. Under properness no component takes bottom, so source-facing applications do not encounter mixed infinities. At a nonvacuous input witness, properness also implies finiteness of each component at x; the proof need not introduce that derived fact as an input or use it explicitly.

Individual properness does not imply properness of the sum. For disjoint component domains, the aggregate is identically top. The existing unguarded global inequality definition gives every vector as a support of that improper aggregate, unlike a domain-guarded convention. At every x some proper component has no support, hence the Minkowski side is empty. The present inclusion therefore stays vacuous and faithful to the source's explicit empty-side clause. Do not present this as meaningful support existence for an improper aggregate. This convention disclosure, arbitrary finite indexing/empty-family extension, and coordinate-free Euclidean presentation remain the explicit deltas.

## Canary and compiler evidence

The current canary text repeats the same inclusion body and includes three meaningful boundary probes. The quadratic plus interval-indicator probe obtains a genuine nonzero support 2 at x=1 by feeding component witnesses 2 and 0 into the inclusion theorem; it is not a zero-only arithmetic check. The concave negative quadratic has no support at zero, proved by incompatible support inequalities at 1 and -1. Its one-component Minkowski probe confirms empty-witness semantics without assuming convexity; it does not itself invoke the inclusion theorem and does not prove a nonvacuous nonconvex application. The Fin 0 probe does invoke inclusion and produces the zero support of the empty sum.

`inclusion-leaf01.log` reports the inclusion with only propext, Classical.choice and Quot.sound. `inclusion-canary01.log` contains actual mod_cast failures and sorryAx in the concave and downstream vacuity probes: this failed run is rejected as validation and must remain historical evidence. The repaired current text explicitly rewrites real coercion addition and converts the two scalar inequalities before nlinarith. `inclusion-canary02.log` reports all five displayed declarations with only propext, Classical.choice and Quot.sound, and no error. This is observed focused compiler evidence, not a newly rerun build or public combined-gate claim. The logs alone are not immutable execution-to-source manifests; this receipt binds the actual inspected current text and log bytes separately.

`inclusion-frozen01.json` reports matching expected/actual statement hash ec65f9d2980a6c42c0425751ef7b2a82df2b380b87835357544edb284e9b7fcd and no findings. Independent reading of the header and candidate confirms the same parameters and conclusion. The endpoint JSON's empty source_assumptions array must not be interpreted as absence of the explicit properness parameter.

## Equality and completion boundary

The unchanged equality header still requires a positive Fin(n+1) family, each component proper/convex/closed, and one z in the last component's domain and every OTHER ambient interior; its query x is arbitrary. No all-interiors replacement or at-x qualification is accepted. This exact reverse-decomposition endpoint remains unproved and mandatory. The frozen draft manifest's historical statement that neither endpoint was compiled is contract-time metadata, not current inclusion status. This scratch review updates only inclusion evidence and preserves the earlier receipt unchanged.

## Independently measured raw receipts

All SHA256 values below were computed from current raw filesystem bytes during this review, with no JSON reserialization or line-ending normalization. Paths are relative to E:/ABRL/worktrees/research-online-book.

| File | Raw SHA256 |
| --- | --- |
| tmp/online-subgradient-sum-inclusion.lean | 4ea465098e119a2f772080468fd256b165dbfe3a878e1e763c1c8bd34285d1b2 |
| tmp/online-subgradient-sum-inclusion-canary.lean | 05a229fd8ff31f40e912d3f13b5ca888125c3086f6b822e01e8a6df2e69336e3 |
| runs/online-subgradient-sum-20261003/inclusion-leaf01.log | 44938950c73ef7ddbf7d743668235a2c7c8ec409bd7c94aaffdc7685dc63e1ef |
| runs/online-subgradient-sum-20261003/inclusion-canary01.log | fc71eb155c5058a3ae5b0df6fef43ee0419576502537ee011afdd9eb0713bd78 |
| runs/online-subgradient-sum-20261003/inclusion-canary02.log | 4303f389df597a7fbd9067e495494d03d5c168119c948cfdfc69f7dfce11a458 |
| runs/online-subgradient-sum-20261003/inclusion-frozen01.json | 7258638f4007d584ea266cf7d2442310dcf38bf9e3286f47f0ebc9d3a56f6b2c |
| docs/contracts/online-subgradient-sum-v1/context.txt | 7c49b10c1e933dac2f41ebfb195151224156c14f6ef81fed82a5c4269d5ee1d8 |
| docs/contracts/online-subgradient-sum-v1/inclusion-header.txt | 9cd548022c463e6be3631685a7c687116b176f005341eecbb7f324f26273124b |
| docs/contracts/online-subgradient-sum-v1/equality-header.txt | 04daea804ef2da692817458481240e079892c03383e83acd3b9f20f1f2ea32da |
| docs/contracts/online-subgradient-sum-v1/contract.md | 5b09efee5962772ecadb5afc63a85d560c2c2483c4003b6ff61520c0bd7095ac |
| docs/contracts/online-subgradient-sum-v1/contract-manifest.json | 1992bd69dba31dfca18b50640e7fb9f7708731658fc70d3bba86fd2be7578d8b |
| docs/contracts/online-subgradient-sum-v1/theorem_2_23_inclusion.json | e09198bb68b61320952decb46f359ef0633e49518b5ecf79dc12358052a16471 |
| docs/contracts/online-subgradient-sum-v1/theorem_2_23_equality.json | a6b11235782600cdef78d90c4ebbe2fa7ca274bec7654530a510afa6a50f06ca |
| runs/online-subgradient-sum-20261003/blind-reconstruction-v2.md | 80a186970ec70e5f6ffed7496b716d763eb9e1030e47682bf5472ceb8892e953 |
| runs/online-subgradient-sum-20261003/draft-source-review.md | 603a04b49f6c9822b02d330841231678f5b761ea728c66be21f5e3482dfe07c9 |
| tmp/next-subgradient-sums-source.txt | ce46624c332bcc1684c18aae541d31bfdf3bcfd0d5a2abe040d24dbf970de31e |
| BanditRLProof/OnlineSubgradientBasic.lean | 4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962 |
| BanditRLProof/OnlineClosedProper.lean | 9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6 |
| BanditRLProof/OnlineConvexExtended.lean | fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f |
| ../research-online-ogd/tmp/pdfs/orabona-v10.pdf | cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 |
