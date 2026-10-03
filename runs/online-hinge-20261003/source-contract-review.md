# Example 2.27 source contract review

Verdict: **accepted-with-explicit-delta**, for contract stabilization only. No required header repair identified. No proof body, compilation, public integration, reader or package acceptance is certified.

Actor `/root/source_reviewer`; requested GPT-6 Astra / medium; distinct automated anti-anchored source reviewer, not external-human review. Read scope: all seven v1 contract files, the fresh blind packet/reconstruction/receipt, source-pages extract, and the actual shared SourceSubdifferential definition in OnlineSubgradientBasic. The latter file is hashed whole but its other theorems are not newly audited. The original pinned PDF was independently hashed and physical page 30 freshly extracted; Example 2.27 is on printed page 18. Digest: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`.

## Seven semantic slots

1. **Objects/model.** The source hinge is exactly max(1-inner(z,x),0). `sourceHinge` uses this real maximum and embeds its finite value into EReal; neither branch ordering nor offset changes. The source Euclidean space is expressed as a finite-dimensional real inner-product space. No stochastic or sequential object is introduced.
2. **Hypotheses.** The source terminal has the explicit finite-dimensional binder and arbitrary z,x. There is no nonzero/normalized z, interior, closedness, domain restriction or auxiliary support-existence assumption. Properness, convexity and continuity needed for the proposed maximum-rule application are proof obligations to derive for these concrete functions, not hidden terminal inputs.
3. **Construction.** The affine foundation characterizes all global supports of inner(a,y)+b as the singleton a, on an arbitrary real inner-product space. This is reusable stronger-scope infrastructure, not a substitute for Example 2.27 or the later affine-composition theorem. The proposed Bool maximum, active-index classification and segment-hull route is semantically suitable, but no body has been reviewed or certified.
4. **Quantifiers.** Every z and evaluation x are included. Membership uses the actual shared definition with every ambient y and the finite EReal embedding of inner(g,y-x). The packet's displayed definition matches that shared definition. The terminal is set equality, hence includes every candidate support and both necessity and sufficiency; it is not merely existence or one chosen subgradient.
5. **Conclusion/branches.** Negative margin gives {0}; zero margin gives exactly {g | exists alpha in [0,1], g=-(alpha smul z)}; the remaining real case is positive margin and gives {-z}. This agrees with the original negative/equality/otherwise ordering. Both segment endpoints are included and no hull closure or normalization changes the set.
6. **Degeneracies.** For z=0, margin is always 1 and the last branch gives {0}, as required for the constant-one function; the boundary and negative-margin cases are then impossible. For x=0 the margin is 1 and the answer is {-z}. A zero-dimensional ambient space is allowed. At a realizable zero-margin query, alpha=0 and alpha=1 yield 0 and -z. Full all-y support still compares across different margin branches; the contract does not restrict testing to the current branch.
7. **Source/reconstruction/status.** The independent blind reconstruction correctly recovers all branches, inclusive endpoints, global quantification and z=0 behavior. The manifest marks draft and compiled=false and keeps chapter/book false. Native source_assumptions arrays are empty, but the actual statement/context retain their displayed typeclass assumptions; those arrays must not be read as erasing finite dimensionality. The foundation and terminal have distinct names and fingerprints. The source anchor printed18/PDF30 is correct.

## Explicit deltas and mandatory next evidence

The source terminal uses a coordinate-free finite-dimensional real inner-product space and a finite-valued EReal embedding; these are faithful representations of the stated Euclidean hinge. The affine foundation has wider, possibly infinite-dimensional scope and is separately labeled reusable infrastructure. It does not claim the source terminal has been generalized to infinite dimension.

No semantic mismatch requiring a new contract version was found. Subsequent proof review must inspect actual global affine necessity/sufficiency, the actual concrete max identity and active cases, and both directions of the closed segment characterization without a nonzero-z premise. Nondegenerate canaries should exercise the strict branches and a true boundary mixture plus both endpoints/rejected vectors, with z=0 checked separately. Actual compilation/axiom/frozen-header checks, public root/Tests/harness, reader/source mapping, graph/registry/site and immutable bindings remain pending. Later affine, Lipschitz, OSD/linearization and the whole book remain required. No native trial, global frontier mutation, or production edit was performed by this review.

## Raw SHA256 inventory

Actual bytes, without line-ending normalization or JSON reserialization. Whole-file hashes bind the explicitly stated read scope.

| File | Raw SHA256 |
|---|---|
| `docs/contracts/online-hinge-v1/affine_subdifferential-header.txt` | `1e9df27a0e3c0a264e4dc19f3d893c0ecf70f07e500a2a8f9dc20d8ef8104ac4` |
| `docs/contracts/online-hinge-v1/affine_subdifferential.json` | `495c59906a45310b9c5ad90de892d482e67c145e38a2781ce323d439fb74106e` |
| `docs/contracts/online-hinge-v1/context.txt` | `a13cb0edaf48d138456149fcb92c11d0fad1581283ff71798a87a79106bfed51` |
| `docs/contracts/online-hinge-v1/contract-manifest.json` | `4f83d22b824fab4468aa36967cfd462a0773adb4e925f5165212e5c287dc04d2` |
| `docs/contracts/online-hinge-v1/contract.md` | `082ffaf14393cc0dca02d779d8a67027b5a0e0214b2870f2f95b4bc1b94364e7` |
| `docs/contracts/online-hinge-v1/example_2_27-header.txt` | `a136d38294d5d1efc4dfbf2781a46b196067e99027585fcca840502d35e6c83a` |
| `docs/contracts/online-hinge-v1/example_2_27.json` | `2353f433582c2f700ed50803c6008f4335dbe435e61e1bc59c7ff47a03b56816` |
| `runs/online-hinge-20261003/blind-packet.txt` | `5c5002a689017ca2cbb61547e3c8d509b7797777390bc3a94b5b48fe3b28626a` |
| `runs/online-hinge-20261003/blind-reconstruction.md` | `f25cbf558807696b9be99f7e51b045a9c318ce6847133f8e4572813750869cef` |
| `runs/online-hinge-20261003/blind-receipt.json` | `46df8e53c7bfbe1bbe32c287cc1103965f0758f71851d6ac49b6afccf7378150` |
| `runs/online-hinge-20261003/source-pages.txt` | `9e93fc254cfc06e8a62823cddffef15342a66b894950eb1e6c663b573018138f` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
