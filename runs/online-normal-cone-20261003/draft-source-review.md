# Example 2.25 draft source review

Verdict: **accepted-with-explicit-delta for contract stabilization only**. All three source claims are faithfully frozen. The delta is coordinate-free finite-dimensional real inner-product presentation of Euclidean space, using the existing zero/top indicator and EReal support API. No header correction is required. No proof, target compilation, public acceptance, chapter/book completion or later source result is certified.

Actor: `/root/source_reviewer`, distinct automated anti-anchored reviewer, requested GPT-6 Astra / medium, 2026-10-03. This is not external-human review. The decoder is the distinct source-blind normal_blind actor; its report is reconstruction evidence, not proof or source authority.

## Source and inspection scope

I freshly extracted physical page30/printed18 from the original pinned Orabona arXiv:1912.13213v10 PDF and independently rehashed it as cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Example 2.25 treats a nonempty convex V, identifies indicator subgradients with the normal cone, states the cone is {0} at an ambient interior point, and gives the full nonnegative radial ray for norm-one points of the closed unit ball.

I read context, contract, manifest, all three headers/native JSONs, the complete neutral packet and reconstruction, api-probe01 and the intentionally unproved target scaffold. I inspected actual SourceSubdifferential and immediate scoped context, extendedIndicator, effectiveDomain, effectiveDomain_indicator, SourceProper and sourceProper_indicator_iff interfaces in their containing production modules. Hashes bind containing files; this is not a new review of every unrelated declaration in those modules. No proof body for the new claims is present and no target compilation was attempted by this reviewer.

## Seven semantic slots

| Slot | Mismatch search and result |
| --- | --- |
| 1. Objects/spaces | Each terminal explicitly binds FiniteDimensional over a real inner-product space. The first two use arbitrary nonempty convex V; the third uses the actual closed norm unit ball. This covers source Euclidean geometry, not an unannounced infinite-dimensional extension. |
| 2. Quantifiers/order | Indicator equality holds for every query x, including outside V, and every candidate g. Cone inequalities test all y in V; the subgradient definition tests every ambient y. Interior statement quantifies each x satisfying ambient interior membership. Ray membership existentially selects alpha for each g, not one alpha shared by all normals. |
| 3. Assumptions | First two retain source nonemptiness and convexity plus explicit finite-dimensionality. Interior premise is on x; there is no extra closedness, boundedness, full-dimensionality or nonempty-interior assumption. Unit-ball statement assumes only norm(x)=1 beyond ambient structure. No decomposition, unit-normal or cone-existence premise. |
| 4. Conclusions | Three full set equalities: indicator support=normal cone; interior cone={0}; boundary cone=all nonnegative multiples of x. Both directions are mandatory. Merely producing alpha*x as a normal is insufficient for the last equality. |
| 5. Constants/signs | Indicator is 0 inside, top outside. Normal inequality is inner(g,y-x)<=0, yielding the outward ray. Ball uses norm<=1; query norm exactly1; alpha>=0 includes zero. No reversed normal direction, open ball, sphere-only test set or strictly positive ray. |
| 6. Probability/information | Pure deterministic geometry. No probability, algorithm, regret, causality or information-access claim. |
| 7. Boundaries | SourceNormalCone includes x in V, so it is empty outside V. Nonempty V makes indicator supports empty there too. Ambient interior is not relative interior. Thin domains may have no qualifying interior point. Zero normal is included; in zero-dimensional space the norm-one conditional has no instance. |

## Definition and source fidelity checks

The membership guard x in V is necessary for the all-x indicator equality and agrees with the source paragraph's implication that a subgradient must lie at a domain point. For outside x, nonemptiness supplies a y in V; top plus a finite inner product cannot be <=0, so the left set is empty as is the guarded cone. For inside x, all outside-y inequalities are automatic and the inside-y inequalities reduce exactly to the displayed real normal inequality. No mixed-infinity convention occurs because the indicator never equals bottom.

Empty V is deliberately excluded. Under the shared unguarded subdifferential, its identically-top indicator has all vectors as supports, whereas the guarded normal cone is empty. Keeping the source nonemptiness premise prevents this genuine mismatch. Convexity and finite-dimensionality might be unnecessary for some individual elementary implications, but the source terminals retain them exactly rather than silently generalizing during proof repair.

The interior claim uses ordinary ambient interior: a small displacement x+epsilon*g may be tested in V. It does not assert a zero cone at arbitrary relative-interior points of thin convex sets. No assumption of closed V is imported. The ball claim fixes center0, radius1 and boundary norm1. It characterizes the entire outward nonnegative ray, including its origin; it neither chooses one direction with unknown coverage nor assumes collinearity of a candidate normal.

The neutral decoder reconstructs all these quantifiers, exclusions, signs and exact sets correctly, including the outside-domain guard and finite-dimensional binders. Its copied shared interfaces agree with the inspected production interfaces. The native JSON statements agree with the actual headers; manifest fingerprints are native statement hashes, not raw file digests, and should not be confused with the raw hashes below. The empty source_assumptions arrays do not remove the explicit nonempty/convex/sign hypotheses of the statements.

## Evidence and stabilization boundary

api-probe01 displays the actual shared definitions and scalar-coercion, metric-neighborhood, inner-product/norm and order APIs. It is retrieval evidence only, not a compiled proof of these three claims. The target scaffold has empty := by slots with comments; these are parser metadata, intentionally incomplete and not proof bodies. Absence of a literal sorry does not turn them into successful proofs.

All three source endpoints remain mandatory. Stabilize these exact statements; future proof repairs must preserve outside-point equality, ambient interior, inclusive zero coefficient and the reverse ray characterization. A mathematical header change requires a new version and source review, not a silent weakening. No repair is requested for this version. Later max/hinge/affine/Lipschitz/OSD/linearization, older26path migration and the remaining book remain separate required work, not approved by this contract-only verdict.

## Independently measured raw SHA256

Current raw bytes, without normalization or JSON reserialization. Paths relative to E:/ABRL/worktrees/research-online-book.

| File | Raw SHA256 |
| --- | --- |
| `docs/contracts/online-normal-cone-v1/context.txt` | `068e3271455ee2598a947fc435ae78be3fcc49ed465cde68bdded7bf9c4df8ea` |
| `docs/contracts/online-normal-cone-v1/contract-manifest.json` | `d4b497e5826568219537d53d6151af1fc4929d6da67d839afa1ee2e9e6795500` |
| `docs/contracts/online-normal-cone-v1/contract.md` | `b571970881b07ffab41ccae79b52fb6e204c57c285a2f3f29ca13979869a69f2` |
| `docs/contracts/online-normal-cone-v1/indicator_subdifferential_eq_normalCone-header.txt` | `91c76b33e4552368f14ab3f59f2ef31dd3cef7415f89973508ce7ecd2cac0b5c` |
| `docs/contracts/online-normal-cone-v1/indicator_subdifferential_eq_normalCone.json` | `055435f3b6c3566ae6c2b92ab02cdf403565729d05d97a530fa18545c0a83a49` |
| `docs/contracts/online-normal-cone-v1/normalCone_interior_eq_zero-header.txt` | `db5028f1286da0c04191937a156d37acb9532c58d0732127b90179cf70fee50c` |
| `docs/contracts/online-normal-cone-v1/normalCone_interior_eq_zero.json` | `e5cb693a137886ea057180d0e4f27d33e0cb72a235e2accb72823634fd5745a4` |
| `docs/contracts/online-normal-cone-v1/normalCone_unitBall_boundary-header.txt` | `b64fb6f90981f9585ccfaa2f85168cf66383e179abbdb4472457c5ae97134779` |
| `docs/contracts/online-normal-cone-v1/normalCone_unitBall_boundary.json` | `a3ab600507e3c1499a4219204a5f23d2c62ca5c4a5eae3d5c9c5b68bcf8b1ae2` |
| `runs/online-normal-cone-20261003/blind-packet.txt` | `0136781723e141c14e87ef5b545c9b0eccea3e8051f636693e49088101e83aca` |
| `runs/online-normal-cone-20261003/blind-reconstruction.md` | `e5b917f3c71c0978f903b70b2e77971a7ffcd26b0c6ff7a6551305ffc2d45b3a` |
| `runs/online-normal-cone-20261003/api-probe01.log` | `ec6f444da31702f3bc50adecb380df9d56c13ca15e295e4508e3608f104b89d6` |
| `tmp/online-normal-cone-target.lean` | `a49f6c4de197175e56cee70029acc018812b2f6cc6a823eb4d642efdfeefaef5` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
