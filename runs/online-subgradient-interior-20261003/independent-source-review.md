# Independent source review: interior subgradient existence

Verdict: **accepted-with-explicit-delta**.

Actor: `/root/source_reviewer`, distinct from the formalizer and `/root/closed_blind`; requested configuration GPT-6 Astra / medium. Date: 2026-10-03. This is an anti-anchored mathematical source review, not an external-human review. No previous acceptance verdict was used as evidence. No compilation, full-project acceptance, integration, or publication claim is made here.

## Read inventory and binding

Repository: `E:/ABRL/worktrees/research-online-book`; inspected branch `codex/research-online-subgradient-interior`; HEAD `6571dcea0670463f12ad24edd067b7483a16ac98`. The minorant change is a working-tree diff, so this receipt binds actual file bytes rather than treating HEAD as containing all reviewed work.

The following files were read in full unless otherwise stated. SHA256 values are raw-file hashes:

| File | SHA256 |
| --- | --- |
| `BanditRLProof/OnlineConvexMinorant.lean` | `136b6b2845b133f641a7c8569763f2d4f904409dd6cb3a8f2a0a7da707b5223f` |
| `BanditRLProof/OnlineSubgradientInterior.lean` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `Tests/OnlineSubgradientInteriorCanary.lean` | `6f80f819bb7a6f9632b80596af7eeb2b84808929fef4dd41195a046ef826b085` |
| `runs/online-subgradient-interior-20261003/blind-packet.txt` | `b202cf04d82a8db3129609375ff234df7e9d0e8ec07edd918edc9fe98283690d` |
| `runs/online-subgradient-interior-20261003/blind-reconstruction.md` | `004c5b473cf6fd9dbd0aaa5d3cdf53e6e8b458907cdee528b1fbf0a6a9bdb54d` |
| `website/content/readings.json` (only `online-subgradient-interior` entry inspected) | `2beebc34af05a53fd3a37e50b2f8a365f0ceed62a47bd933698df01df7ba0bef` |

I also inspected the Git diff of `OnlineConvexMinorant.lean` against HEAD to compare the old terminal and adapter. The repository README and semantic-roundtrip skill had already been read in this actor's current session; they establish procedure, not evidence for this mathematical verdict.

Source: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, Orabona arXiv:1912.13213v10. A fresh SHA256 calculation gives `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the pinned source. Physical page 29 was freshly extracted directly from that PDF with `pdftotext`. The relevant unnumbered assertion is on printed page 17, Section 2.2.1: proper convex functions are subdifferentiable on the ambient interior of their effective domain. The footnote separately mentions a stronger relative-interior version. The neighboring Theorem 2.22 and sum rule identify subsequent scope, not outcomes of this packet.

## Direct mathematical comparison

The source-facing `subgradient_exists_of_domain_interior` retains properness, extended convexity, finite-dimensional real geometry, and a selected point in the ordinary interior of the effective domain. Its conclusion is nonemptiness of the same global supporting-vector set used by the existing Definition 2.20 interface. Unfolded, one vector g supports f at x against every y in the entire ambient space, including points outside the effective domain. It does not assume the desired supporting vector.

The new `affine_support_of_domain_interior` is a genuine contact result. It simultaneously gives a continuous linear functional a and real b with `a(x)+b=f(x)` and `a(y)+b<=f(y)` for every y. The equality is indispensable: a generic affine minorant lying strictly below f at x would not establish a subgradient there. The actual proof retains the equality after normalizing an epigraph support; the producer uses that equality in its rewrite to the global subgradient inequality. This is not an opaque consumer of an assumed contact hypothesis.

The helper's explicitly named function premise is only nowhere negative infinity, whereas the source-facing producer names properness. This is a difference in assumption packaging, not permission to apply the helper to an improper function with the same interior-point premise: interior membership implies domain membership, and with nowhere-bottom it supplies a finite value at x. Thus the helper's complete premises already imply properness. Its more general finite-dimensional real normed-space formulation returns a functional; the producer uses a finite-dimensional real inner-product space to obtain a representing vector. No assertion about a general infinite-dimensional space follows.

## Seven semantic slots

| Slot | Mismatch search and result |
| --- | --- |
| 1. Objects and spaces | Source Euclidean space is represented by a finite-dimensional real inner-product space for the producer. The helper is more generally formulated on a finite-dimensional real normed space and returns a continuous linear functional, not an arbitrary vector in a non-inner-product space. EReal allows positive infinity outside the domain; properness excludes negative infinity. |
| 2. Quantifiers and order | For every admissible f and every selected interior x, there exists one support vector g working for all ambient y. The helper likewise chooses one a,b satisfying contact at that x and the inequality for all y. Supports may depend on x; no single vector is asserted to support at every x, and no y-dependent choice replaces the global support. |
| 3. Assumptions/regularity | Proper convex f and interior membership match the source producer. There is no added closedness, lower semicontinuity, differentiability, bounded domain, bounded function, or bounded-support assumption. Convexity is the shared real-height-epigraph definition. The helper's lack of a separate finite witness is legitimate because x supplies one. |
| 4. Conclusion | The exact source conclusion is a nonempty global subdifferential, not merely a nonempty local or domain-restricted support set. Contact is proved, then converted to a vector using the inner-product dual representation. There is no uniqueness, differentiability, quantitative bound, or continuous selection conclusion. |
| 5. Constants/normalization | The epigraph support is decomposed as A(y)+ct. Upward closure gives c<=0; interior membership rules out c=0. Normalizing by negative c gives a=-A/c and b=f(x)+A(x)/c, which preserves both contact and inequality direction. The final displacement is y-x with coefficient one and the correct sign. |
| 6. Probability/feedback | Entirely deterministic convex analysis. There is no probability, filtration, measurability, stopping, online trajectory, or regret claim. Removal of an old surrounding measurable/Borel context is not a replacement of mathematical assumptions by probabilistic ones. |
| 7. Boundary and exclusions | Interior is ambient topological interior, not relative/intrinsic interior. If a lower-dimensional domain has empty ambient interior, this producer has no applicable x. The source footnote's stronger relative-interior assertion is not established here. Arbitrary boundary points and general infinite-dimensional spaces are not covered. Positive infinity away from x is allowed; negative infinity anywhere is excluded. Dimension zero is not excluded. |

## Proof route, old terminal, and canary

The actual helper constructs support at `(x,f(x))` without assuming that the epigraph is closed. The point belongs to the epigraph and is not its interior point; a supporting-functional theorem is used at its closure. If the height coefficient vanished, the spatial functional would attain a local maximum at the interior-domain point and hence vanish, contradicting the nonzero functional. The normalization therefore has a strictly negative denominator. Positive-infinite values away from x are handled by a separate branch, preserving full global support.

The old `affine_minorant_of_domain_interior` name, mathematical hypotheses, and existential global-minorant conclusion remain present as an adapter which discards the new contact component. The old `convex_affine_minorant` terminal remains with its former mathematical assumptions and conclusion; its intrinsic-interior/affine-span proof still consumes the adapter. The inspected diff adds contact and the adapter, and removes an unused surrounding measurable/Borel context; it does not replace the old global minorant result by an interior-only terminal. This is a statement/source inspection, not an independently run regression or compiled-interface check.

The canary uses the real indicator of [0,2] at 1. Shared lemmas prove actual properness, actual extended convexity and exact interior membership, then invoke the producer. It does not assume a support exists or switch to an unrelated real-valued loss. It demonstrates a constrained effective domain with infinite exterior values; it does not by itself test a nonclosed domain, lower-dimensional domain, boundary existence, or the full theorem's generality. Those cases must be assessed from the statement rather than inferred from one canary.

## Blind reconstruction and reader

The reconstruction faithfully distinguishes the normed-space functional helper from the inner-product vector producer, verifies quantifier order and contact, and explicitly recognizes the finite witness recovered from interior membership. It correctly distinguishes ambient from relative interior and retains finite-dimensionality. Its disclosed prior exposure to related definitions is acceptable for the stated source-blind role; it did not claim ignorance of all earlier mathematical context. The packet was read as declaration/context text, not executed as a compilable module.

The inspected `online-subgradient-interior` reader accurately cites the unnumbered assertion rather than inventing a theorem number, keeps ambient interior explicit, names finite-dimensionality, and states global support. Its proof bridge preserves the contact equality and negative normalization. The reader's phrase that the helper uses a weaker nowhere-bottom assumption is correct when comparing that individual premise to properness; the full helper assumptions nevertheless recover properness through x, as clarified above. No weakening to a closed or bounded feasible set is hidden. The interval example matches the actual canary, and the reader leaves differentiability and subsequent rules separate. The compiled-status label is not certified by this semantic review.

## Verdict and required treatment

**Accepted-with-explicit-delta.** No Lean or reader repair is required for the inspected bytes. Preserve these explicit representation/implementation deltas: coordinate-free finite-dimensional inner-product presentation of the source Euclidean producer; a normed-space contact helper returning a functional; a separately derived contact construction rather than a purported verbatim source proof; and the helper's recovered finite witness instead of an explicit properness argument. There is no loss of the source producer's assumptions or conclusion.

This receipt covers the ambient-interior assertion only. It does not certify the stronger relative-interior footnote, arbitrary boundary existence, Theorem 2.22, later sum/max rules, or Chapter 2 completion. All compiler, integration, and live-publication evidence remains separate.
