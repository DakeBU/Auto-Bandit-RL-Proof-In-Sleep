# Example 2.27 actual candidate body review

Verdict: **accepted-with-explicit-delta** for hinge-full-02 and five hinge-canary-03 canaries. No required mathematical repair. Actor `/root/source_reviewer`, requested GPT-6 Astra / medium, distinct automated reviewer, not external-human.

Read scope: every declaration/body in the full candidate and complete canary file; unchanged frozen contract, blind packet/reconstruction and original source from this actor's stabilization review; successful logs/exits and safe-verify reports. The canary's candidate prefix matches full02 after removing diagnostic axiom printing and whitespace. All files in the earlier contract receipt were freshly rehashed and unchanged, including pinned original PDF `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, Example2.27 printed18/PDF30.

Imported interface inspection covers actual SourceProper/effectiveDomain, convexExtended_iff_toReal, theorem_2_26 and its terminal body, and mathlib convexHull_pair/segment_eq_image statements and bodies. The previously reviewed full max producer is reused; this is not a new audit of every transitive mathlib proof. Whole-file hashes bind this stated scoped inspection.

## Seven semantic slots

1. **Objects/model.** sourceHinge is exactly the real max of 1-inner(z,x) and zero embedded in EReal. Bool false is constant zero; true is inner(-z,y)+1. The finite-dimensional real inner-product model faithfully represents source Euclidean space.
2. **Hypotheses.** The terminal has exactly the frozen finite-dimensional binder and arbitrary z,x. Concrete affine properness excludes bottom and supplies value b at zero. Concrete convexity proves effectiveDomain=univ and the affine weighted equality. Ambient continuity composes inner-product/addition continuity with the real-to-EReal embedding. Finite values discharge every queried-domain obligation. No properness, continuity, closedness, nonzero-z or support oracle is added as a source-terminal premise.
3. **Affine support producer.** Necessity tests an arbitrary global support g at y=x+(g-a), converts the finite EReal inequality to reals and derives inner(g-a,g-a)<=0. Nonnegativity and definiteness give g=a. Sufficiency checks every ambient y using inner subtraction. This proves actual uniqueness and full support, even in an arbitrary real inner-product space, without completeness or finite dimension.
4. **Maximum/quantifiers.** hinge_max_identity proves both inequalities for the actual Finset maximum: each component is bounded by the real max, and an actual Bool member attains the needed branch. The full existing maximum equality is applied after deriving all its qualifications. All z,x, candidates g and ambient test points y are retained, including tests across hinge branches. No selected-subgradient substitute occurs.
5. **Active cases/full guarantee.** The active-union proofs enumerate both Bool values and actual singleton component supports. Negative margin excludes the true component and leaves {0}; positive margin excludes false and leaves {-z}; equality retains {0,-z}. The terminal uses convexHull_singleton in strict branches and convexHull_pair plus segment_eq_image at equality. Both witness directions are explicit, giving precisely g=-(alpha smul z) for alpha in closed [0,1]. The final branch derives positive margin from not-negative and not-zero. No closure/open segment/normalization changes the source formula.
6. **Degeneracies/canaries.** No z=0 exclusion occurs; its margin is 1 and the formula returns {0}. The five actual canaries prove: strict-zero at scalar z=1,x=2; strict slope {-1} at x=0; the full boundary interval [-1,0] at x=1; -1/2 membership together with its absence from the active union and rejection of +1; and arbitrary scalar x with z=0. The interval equality includes both endpoints, although endpoint membership is not separately named. These test genuine mixing and necessity, not just one support's existence.
7. **Source/evidence/status.** Actual terminal and blind reconstruction agree with all three source branches. Safe-verify preserves both original native fingerprints and hypotheses. Full02 and canary03 recorded exits are zero; the terminal and each of five canaries list only propext, Classical.choice and Quot.sound. These are recorded scratch compilation evidence, separate from semantic judgment and later public acceptance.

## Deltas and limits

Accepted deltas are the coordinate-free finite-dimensional Euclidean presentation and finite EReal embedding. The affine foundation additionally has wider arbitrary-inner-product scope and is clearly infrastructure, not the later affine-composition theorem.

The inspected full01 failure log contains sorryAx and is rejected recovery evidence, not accepted proof. The repair note records rejected canary01/02 scalar-inner normalization failures. Successful03 derives the real-inner equality definitionally; its statements are not weakened. Failed logs remain preserved.

Candidate-body acceptance does not certify public integration, root/Tests/full harness, final reader, site/graph/registry, immutable binding or PR delivery. Later affine/Lipschitz/OSD/linearization, older migration and whole-book work remain required. This review edited only its two reports, with no native/global trial or production mutation.

## Raw SHA256 inventory

Actual bytes, no normalization or JSON reserialization. Whole-file hashes do not expand the declared semantic read scope.

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
| `runs/online-hinge-20261003/source-contract-review.md` | `a186bdee86c9584665a16f9f3498e8c72aa98b5b0d081861f87ba173325133d0` |
| `runs/online-hinge-20261003/source-contract-receipt.json` | `c40e165f5d4cabda929cd23b03455cb487a323e116e9c54e59521576cad0b7b6` |
| `runs/online-hinge-20261003/stabilization.json` | `0a3829976f25ad1842b7045e057a6dfebeca6bac14558ec2b6aa4a3ac228d30e` |
| `runs/online-hinge-20261003/hinge-safe-verify.json` | `e8f5f6e930b48108f08ae23d18fbaed89adcfff36863cc655458e69dbe16f9ac` |
| `runs/online-hinge-20261003/affine-safe-verify.json` | `07cc206ac887c412cb508adda2482dbe38132aa9a2c15cbe4b623322305140c5` |
| `runs/online-hinge-20261003/canary-repair.md` | `87788cbe4e59cbeb62f08ea56d255a998781231267a20d19dea0a982ee8a09d7` |
| `runs/online-hinge-20261003/attempts/hinge-full-02.lean` | `afeaf88f0ca2bfec142007ed8d092bd7e031af41660b16a844402c46a9fd3a3c` |
| `runs/online-hinge-20261003/attempts/hinge-full-02.log` | `c69abf1ed0fb81708896f792c2b240c2c5a5bdb24236561185c6539aaf13dfab` |
| `runs/online-hinge-20261003/attempts/hinge-full-02-exit.json` | `c6cdf417c883cb199cbb06f9b1d1cd74f571ac1ff53c794f086b1990327f4f9c` |
| `runs/online-hinge-20261003/attempts/hinge-canary-03.lean` | `b273cf7ad6a80ec471303f82029b165961a79664136e0abf9f2cc9a7c848a5b1` |
| `runs/online-hinge-20261003/attempts/hinge-canary-03.log` | `6ae222d9a5241cf865a2b5c6df25f007f81d789f08c23786fb673141aa3589fd` |
| `runs/online-hinge-20261003/attempts/hinge-canary-03-exit.json` | `dc670fe34e5c2348fee3c215cd7d985250ddb92b33fc0c8a07a8ee1f6a33f16c` |
| `runs/online-hinge-20261003/attempts/hinge-full-01.log` | `3f6133b6b06d29d9033a1d0f22bf6ea1469277394a719f6d1c718c52fb550ddf` |
| `BanditRLProof/OnlineSubgradientMax.lean` | `c1224494d910035fb482971885a5a4c617da9b3d9a618cb71ec91e5b15dd018c` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Hull.lean` | `892e7ab6e315b15a8bc6af60c4603597a78733fff8bbc2fe37b6bd36f23a7f32` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Segment.lean` | `e0e6ba0bf8db11909dcb9e38ccb855787b220389a18ecf5c17d9335402ecfadf` |
