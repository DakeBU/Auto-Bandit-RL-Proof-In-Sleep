# Theorem 2.28 source contract review

Verdict: **accepted-with-explicit-delta**, for contract stabilization only. No mathematical header repair identified. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium; distinct automated reviewer, not external-human.

Read scope: all five v1 contract files, source-pages, fresh distinct blind packet/reconstruction/receipt, actual SourceSubdifferential and SourceProper definitions, pinned adjoint interface locations and type-probe output. Whole files are hashed below, but unrelated imported theorems are not newly audited. Original PDF independently hashed to `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; physical30 was freshly extracted. Printed18 Theorem2.28 assumes f proper, defines h(x)=f(Ax+b), and concludes A-transpose image of its source subdifferential is included in the composed subdifferential.

## Seven semantic slots

1. **Objects/model.** Two finite-dimensional real inner-product spaces represent possibly different Euclidean dimensions. An actual continuous linear map A:E->F represents every finite matrix in orthonormal coordinates; its actual Hilbert adjoint represents the transpose. Finite-dimensional linear maps are automatically continuous, so bundling continuity excludes no source matrix. Finite-dimensional completeness is inherited, not an extra terminal input.
2. **Hypotheses.** Exactly SourceProper f is retained: no bottom value and a finite witness somewhere. No convexity, closedness, differentiability, continuity of f, Lipschitz assumption or query finiteness is introduced. No rank, injectivity, surjectivity or nonzero-map restriction. Properness of h and nonemptiness of either support set are not assumed.
3. **Construction.** The target uses actual inline h(y)=f(Ay+b), not an abstract h with a missing identity. The left side uses the actual adjoint, not an assumed pullback oracle. The planned proof transports the source global inequality at Ay+b through translation cancellation, A(y-x)=Ay-Ax and the adjoint inner identity. No proof body is reviewed yet.
4. **Quantifiers.** Every proper f, A,b,x and every vector in the actual adjoint set image are covered. The source support inequality ranges over all F; the conclusion tests all ambient E. The finite properness witness need not lie in A(E)+b. Neither domain restriction nor local support replaces the global definition.
5. **Guarantee.** Inclusion only, in the correct direction: A.adjoint image of subdiff f(Ax+b) is a subset of subdiff(f composed with the affine map)(x). No equality, reverse lifting, uniqueness or nonempty output is asserted. The original matrix expression is correctly realized as a set image.
6. **Degeneracies/convention.** Zero-dimensional spaces and zero/rank-deficient maps are admitted. Empty source subdifferentials make the inclusion vacuous. Properness of f forces source emptiness at infinite query values, but the composition may be identically top if the affine image misses every finite point. Under the literal shared global-inequality convention such a target has all vectors as supports; the source inclusion remains vacuous, and no meaningful subgradient existence for an improper loss is claimed. This convention deserves explicit reader disclosure when discussing improper compositions. A proper nonconvex example such as f(t)=-t^2 at0 has empty source supports; A=0,b=0 makes h=0 with support{0}, illustrating strict inclusion and why convexity/equality must not be added.
7. **Source/reconstruction/status.** The blind decoder reconstructs the exact image direction, properness, all-y quantifiers and empty/improper cases correctly. Source anchor is printed18/PDF30. Manifest is draft, compiled=false and chapter/book false. The native source_assumptions array is empty but the actual statement explicitly retains hp and both finite-dimensional binders; metadata is not permission to erase them.

## Explicit deltas and remaining evidence

Accepted deltas: coordinate-free finite-dimensional Euclidean spaces, continuous-linear-map packaging with automatic finite-dimensional continuity, actual adjoint as transpose, and EReal with SourceProper excluding bottom. The shared global-support convention for potentially improper h is explicit above and causes no nonvacuous strengthening of the original inclusion. No zero-dimension exception is necessary.

The API probe is **not a passing compilation**: its exit record is1 because guessed adjoint_smul/adjoint_zero identifiers are absent. It nevertheless reports actual adjoint_inner_left and successful completeness synthesis (`complete_of_proper`) for both spaces. Preserve this failed retrieval evidence; a repaired body/compilation must use the actual APIs. This is an evidence boundary, not a header mismatch.

Mandatory later work: actual transported-inequality proof, unchanged-fence/axiom checks, nonzero map and translation canary, zero/rank-deficient and proper nonconvex strict-inclusion canaries, then public/root/Tests/harness/reader/site/immutable/PR gates. Proposed canaries are not yet proved by this review. No body, public acceptance, global trial, source edit, main/live or chapter/book completion is certified. Later source Lipschitz/OSD/linearization and older migration remain required.

## Raw SHA256 inventory

Exact raw bytes; no normalization or JSON reserialization.

| File | Raw SHA256 |
|---|---|
| `docs/contracts/online-affine-subgradient-v1/context.txt` | `a342da47300bae3633d237c96013bd9edcdef874d8d52d3b3e1bc9b5179dc4b9` |
| `docs/contracts/online-affine-subgradient-v1/contract-manifest.json` | `c0540d686c86f11a9bca48bb2376a7c300cf07a085aa858743744f0bef57ace4` |
| `docs/contracts/online-affine-subgradient-v1/contract.md` | `bb647512bf5dcd2bdacf4da11132e257fb57d0f8beed912fccb0b38cf86ae6b2` |
| `docs/contracts/online-affine-subgradient-v1/theorem_2_28-header.txt` | `1c7fff1f7dbd471b029a7aed7d47d3d0b5d3f8ae828429774bb11ccc8e4849fb` |
| `docs/contracts/online-affine-subgradient-v1/theorem_2_28.json` | `2ee307d726ce4619233cfc972b596f5505e547b26e252e1994b7d7de0d1cb67d` |
| `runs/online-affine-subgradient-20261003/source-pages.txt` | `9e93fc254cfc06e8a62823cddffef15342a66b894950eb1e6c663b573018138f` |
| `runs/online-affine-subgradient-20261003/blind-packet.txt` | `15f8efe0e055c0a7a31d98797820e2ee2f16c76fe2b2fee68b6416e5898109d1` |
| `runs/online-affine-subgradient-20261003/blind-reconstruction.md` | `d0c5bc057fe415437c69a6967161c819bf36103891b0834339666398dde6b42b` |
| `runs/online-affine-subgradient-20261003/blind-receipt.json` | `0e23cab3d8f1fab90d14db62d3b45c564527ff76bf464946c727154a9614b7fe` |
| `runs/online-affine-subgradient-20261003/api-probe-01.log` | `9d76b077a82c1110269c729221d8a9b13c2c158a8733cb3988d1a59f272f2bea` |
| `runs/online-affine-subgradient-20261003/api-probe-01-exit.json` | `da2ebddd3f12621d330c409c87f0fc1c01fc2a5f464671bdbddddb03b85b9988` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean` | `ffa28bc6ab970495e53c01337b42aee7b047644eb954a253b491a5104e409735` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
