# Full Theorem 2.22: independent source review

Verdict: **accepted-with-explicit-delta for the inspected full equivalence, exact reverse gradient producer, and generic representative gradient identity**. No semantic repair is required for these bound mathematical files. This verdict is separate from compiler validation, public canaries, combined-project acceptance, reader/site publication and review-binding checks, which this receipt does not certify.

Actor: `/root/source_reviewer`; model configuration requested GPT-6 Astra, reasoning medium; date 2026-10-03. This is a distinct automated semantic-review actor, not external-human review. I independently inspected the new reverse proof chain and terminal, rather than treating earlier forward/contract verdicts as evidence that the reverse was established.

## Source and current-file inventory

Canonical research source repository is `E:/ABRL/research`; reviewed worktree is `E:/ABRL/worktrees/research-online-book`, branch `codex/research-online-subgradient-differentiability`, inspected HEAD `e5a3e6adc7bbfc90562aef845637e30e8d6e25fd`. The reviewed production files include current working-tree content; HEAD alone is not the receipt binding.

The pinned Orabona arXiv:1912.13213v10 PDF at `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf` was freshly hashed as `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the expected source. Physical page 29 was freshly extracted directly with `pdftotext`. On printed page 17, Theorem 2.22 assumes a convex extended-real function finite at x, concludes differentiability at x iff a singleton subdifferential, and identifies the singleton element as the gradient.

Files below were read completely in this review; raw SHA256 bindings are:

| File relative to worktree | SHA256 |
| --- | --- |
| `BanditRLProof/OnlineSubgradientDifferentiability.lean` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `BanditRLProof/OnlineConvexMinorant.lean` | `33fc76b3f18e2686963ca59a895f320b21f8b437b0d27ff2d16bba37e7b08ea7` |
| `BanditRLProof/OnlineSubgradientInterior.lean` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `tmp/online-subgradient-full.lean` | `342c6c9430b22f5dc09b584a75389c0bac6f3df5f9daad88c507fcd58afe4dcc` |
| `runs/online-subgradient-differentiability-20261003/full-theorem02.log` | `d7c17e501a0d3f86c5af7b2c67e59f801cb05cd381f76cb451e9e4f51c268d1c` |
| `runs/online-subgradient-differentiability-20261003/reverse-gradient03.log` | `ced04583ef52a5e19cc6f6f2c2bdd19b250f866bf6ad0d44c37ac17420fa516c` |
| `docs/contracts/online-subgradient-differentiability-v2/contract.md` | `9a44687bb43edd524ec3dcbca227410d507295681d19ca731463ffb03a9d64fe` |
| `runs/online-subgradient-differentiability-20261003/blind-reconstruction-v2.md` | `89e90ba9abad3c07c3c7150f50fff62cef83b97a56ed4c22dc408285ca3d56a9` |

The actual `SourceProper` and first-order interfaces had been inspected in prior stages of this actor's session. Their meaning is not inferred from source-theorem names: properness excludes bottom globally and supplies a finite witness; the shared first-order result supplies the global supporting inequality. The new reverse uses the actual current producer and global support definition read above.

## Seven semantic slots

| Slot | Independent comparison |
| --- | --- |
| 1. Objects and spaces | Finite-dimensional real inner-product space is the coordinate-free representation of source Euclidean space. f remains EReal-valued globally. Extended convexity is convexity of the real-height epigraph; no global finite-valued replacement of f occurs. The refactored affine core uses finite-dimensional real normed geometry and continuous linear functionals internally. |
| 2. Quantifiers/order | For every convex f and finite point x, differentiability is equivalent to existence of exactly one global supporting vector. The reverse derivative is proved for the same specified singleton g. The companion identifies the support set with the gradient of every admissible differentiable local real representative h. All support inequalities quantify over every ambient y, not only a neighborhood or domain. |
| 3. Assumptions/regularity | The full terminal assumes only convexity and finite f(x), besides finite-dimensional geometry. Properness, interior membership, local Lipschitzness, continuity, support selection and local uniform bounds are derived in the chain. No source-facing input adds closedness, boundedness, lower semicontinuity, smoothness or an interior hypothesis. |
| 4. Conclusions | Actual bidirectional differentiability/singleton equivalence is present. `singleton_subdifferential_hasGradientAt` preserves the stronger exact endpoint: the finite part has gradient equal to the supplied singleton g, not merely some derivative. `theorem_2_22_gradient` supplies the source gradient identification for every local representative. |
| 5. Constants/normalization | Local Lipschitz bound K controls all nearby supporting-vector norms; shrinking a radius by 2 leaves room for the test displacement. The derivative residual is bounded by `norm(G(y)-g)*norm(y-x)` with coefficient one, yielding a Frechet little-o estimate, not merely fixed-direction derivatives. Support signs and y-x orientation are preserved. |
| 6. Probability/feedback | The arbitrary-index filters and classical choice are deterministic topological proof devices. No probability, stochastic independence, causal feedback, measurability of selection or stopping semantics are assumed or claimed. Nontrivial-filter hypotheses occur only in auxiliary limit results and are instantiated by the ordinary neighborhood filter. |
| 7. Boundaries/exclusions | Differentiability uses full ambient neighborhoods, including x, not a punctured or relative-domain notion. At a finite noninterior domain point, singleton support is ruled out by proof, not excluded by a terminal premise. Positive-infinite exterior values remain allowed. Bottom values elsewhere are ruled out under either side's substantive hypotheses. Zero dimension is allowed; no infinite-dimensional equivalence is asserted. |

## Reverse construction: producer audit

**Singleton forces interior.** The actual theorem first obtains g as a global support at the finite point. That inequality excludes bottom at every y. If x were not in the ambient interior of the convex effective domain, the supporting-functional result at x produces a nonzero normal. Its representing vector d satisfies an inequality allowing g+d to support f globally. Positive-infinite exterior values are handled separately; finite-domain points satisfy the normal inequality. Singleton equality forces d=0, a contradiction. No nonzero normal is assumed at an interior point and no interior premise is smuggled into the full endpoint.

**Actual local support selection.** The reverse gradient theorem builds properness from the support inequality and the given finite value. It defines G(y) by choosing a vector from `subgradient_exists_of_domain_interior` at each interior y, and uses zero elsewhere. The accompanying `hGmem` proves membership for that exact function G. Interior openness ensures only the valid branch matters near x. Thus the chain does not assume an arbitrary selector already has the desired support property or convergence.

**A uniform bound on nearby supports.** `subgradient_norm_le_lipschitz_ball` tests a support g at `x+t*g`, with t=r/(2 norm(g)) when g is nonzero. The point is inside the actual finite Lipschitz ball. Comparing the support lower inequality to the Lipschitz upper inequality bounds norm(g) by K. The zero case is separate. `subgradients_locally_bounded` obtains local Lipschitzness from the finite real part's convexity on the effective domain, then shrinks the neighborhood so every nearby center has a test ball inside the original finite Lipschitz region. The same K controls every support at every point in the smaller ball; this is not a pointwise bound allowed to vary without control.

**Closed graph and compactness produce the limit.** `subgradient_limit_of_continuousAt` passes each global supporting inequality to the limit. It uses actual finite-part continuity at x and eventual finiteness near x; at an arbitrary test y it separately handles positive infinity or converts the finite value. It does not assume global closedness of the epigraph. `singleton_subgradient_tendsto` traps the support stream in the closed ball of radius K, compact in the finite-dimensional space. For each map-cluster point it constructs a nontrivial refining filter on which the supports converge, keeps the base points converging to x, applies the closed-graph lemma, and uses singleton membership to identify the cluster point with g. The compact unique-cluster-point principle therefore proves convergence of the actual support stream. Continuity and compactness are derived from genuine finite-dimensional hypotheses, not postulated as a support-limit premise.

**Frechet residual, not directional substitution.** The reverse applies that result to xs=id and the actual G along the entire neighborhood filter. Hence norm(G(y)-g) tends to zero as y tends to x. The support at x gives a nonnegative remainder. The support at y, tested at x, bounds that remainder above by `<G(y)-g,y-x>`. Cauchy-Schwarz gives the norm product. For every positive epsilon this controls the remainder by epsilon times norm(y-x) throughout a neighborhood. The code uses the little-o characterization of `HasFDerivAt` to obtain `HasGradientAt` with exactly g. It has not settled for Gateaux/directional differentiability or an unspecified derivative.

**Genuine local real representative.** The full reverse then chooses the finite part as h but also proves its EReal coercion equals f on a neighborhood via derived nowhere-bottom and interior membership. This equality is indispensable: it prevents the totalized toReal map from spuriously declaring an infinite-valued boundary differentiable. The full `SourceDifferentiableAt` conclusion includes this genuine local agreement, not just differentiability of toReal in isolation.

## Forward, gradient identity, and refactored shared geometry

The production forward/gradient route remains source-faithful: local representative agreement gives actual neighborhood finiteness. The shared affine core derives nowhere-bottom and a touching global support without global properness or closedness inputs. This supplies the regularity required by the shared first-order result, which produces the actual gradient as a global support. A local-minimum derivative argument makes every support equal that gradient. Eventual equality transfers gradient identity to every admissible h. The companion's finite-x argument is redundant given local equality but preserves the source contract and does not weaken it.

`OnlineConvexMinorant.lean` now contains one finite-neighborhood geometric core. `affine_support_of_domain_interior` obtains neighborhood finiteness from its old assumptions and reuses that core. `affine_minorant_of_domain_interior` still discards contact, and `convex_affine_minorant` retains its global minorant conclusion and existing affine-span route. The old mathematical consumer headers are preserved in the inspected file. The scratch full file contains a self-contained copy of the core; the production file uses the shared module instead, so this scratch provenance is not evidence of duplicated public geometry.

## Source reconstruction and compilation evidence are distinct

The version 2 blind reconstruction accurately states the full terminal and companion semantics, including absent properness/interior inputs and representative independence. It contains statement-level reconstruction only; it did not review this reverse proof body. The v2 contract's historical prose saying bodies remain open is a frozen draft-stage record, not authority for the current code's status. The new current-file inspection finds actual bodies for both directions and the exact gradient endpoints.

The inspected scratch logs show warnings for redundant variables/section assumptions and axiom reports listing only `propext`, `Classical.choice`, and `Quot.sound` for the displayed reverse/full/gradient declarations. They contain no displayed proof error. This is evidence of what those supplied logs report, not an independent compiler rerun or cryptographic binding of each log to current production bytes. The scratch and production modules differ through shared-core extraction, comments and diagnostic commands; the old scratch log alone must not be labelled a fresh production/full-project build.

## Acceptance boundary

No source-semantic repair was found. **Accepted-with-explicit-delta** means the exact source assumptions, iff conclusion and gradient identity are preserved under the explicit coordinate-free finite-dimensional representation and local-real-representative encoding. The construction supplies its required support existence, uniform boundedness, closed-graph passage and compactness argument rather than assuming them.

This receipt newly covers the full reverse and equivalence at the recorded bytes; earlier forward-only receipts remain historical scoped evidence, not retroactive proofs of the reverse. Pending public canaries, site/readers, generated graph, review binding, combined Lean/Tests/harness gates, merge and deployment are not certified here. Completing this single source theorem is not Chapter 2 or full-book completion. No external-human-review claim is made.
