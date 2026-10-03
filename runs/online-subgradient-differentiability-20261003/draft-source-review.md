# Draft source review: Theorem 2.22 contract

This is a **draft-contract review only**, by the separate automated actor `/root/source_reviewer`, requested GPT-6 Astra / medium, dated 2026-10-03. It is not external-human review and does not accept a proof, compilation, or completed source theorem.

Verdict for the displayed equivalence and prerequisite contracts: **accepted-with-explicit-delta** in representation. Verdict for treating the current headers as a complete contract covering every conclusion of source Theorem 2.22: **rejected pending a formal gradient-identity companion endpoint**. The contract prose already identifies this obligation, but no corresponding header is present in the reviewed packet. The full equivalence itself remains unproved; the scratch interior prerequisite does not complete it.

## Source and read inventory

Repository `E:/ABRL/worktrees/research-online-book`; inspected branch `codex/research-online-subgradient-differentiability`, HEAD `51fdc04770d9b2064c229d4f344ac781c88ce829`. All entries below are raw SHA256 bindings of the files actually read in full.

| File | SHA256 |
| --- | --- |
| `docs/contracts/online-subgradient-differentiability-v1/context.txt` | `0638affef80952cde5777ece5cdcf2fa8ec46efd2c3ada2c670de2b0df8f5348` |
| `docs/contracts/online-subgradient-differentiability-v1/full-header.txt` | `7029e22ec2d7e84879a3c97109e5d17709372628fa516b309c2d5391ef5e94b9` |
| `docs/contracts/online-subgradient-differentiability-v1/interior-header.txt` | `051a7e1df02b4405a9dcebc5a48a586aee4a9f909ff862e28fb5ea4deb66f9dd` |
| `docs/contracts/online-subgradient-differentiability-v1/contract.md` | `240f6b40af4b55d4c66ccb0056809515968b315e191355fbcc76545850c15e44` |
| `runs/online-subgradient-differentiability-20261003/blind-packet.txt` | `07beb3091aa31913521dd605f6aa519fbc8029077b5d2715b2bf3d940f455e64` |
| `runs/online-subgradient-differentiability-20261003/blind-reconstruction.md` | `3176c723aadf7f20ad634192e5806a02f3b4496e3091fe506f1c9aa049d52187` |
| `runs/online-subgradient-differentiability-20261003/interior-candidate.lean.txt` | `5683e637a951e8992833357180379adc52b07fc5253f41ef458e36e8defac9a9` |

Source `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`: SHA256 freshly computed as `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the pinned Orabona arXiv:1912.13213v10 file. Physical PDF page 29 was freshly extracted directly from the original PDF with `pdftotext`. Theorem 2.22, printed page 17, assumes convex extended-real f finite at x; it states differentiability at x iff the subdifferential is a singleton and identifies its element as the gradient. The surrounding paragraph confirms that gradient identification is an intended mathematical conclusion, not merely notation for a singleton witness.

No historical source-review verdict or compilation log was used to establish this verdict. Related definitions were available in the new blind packet and had previously been inspected by this actor; the review here uses the displayed current contracts. No website mapping was requested or reviewed.

## Seven semantic slots

| Slot | Adversarial finding |
| --- | --- |
| 1. Objects and spaces | Source Euclidean space is represented by finite-dimensional real inner-product space E. f remains EReal-valued globally, including both infinities before hypotheses/consequences rule them out. This is a coordinate-free representation of the source finite-dimensional geometry, not an infinite-dimensional extension. |
| 2. Quantifiers and order | For each convex f and finite-valued x, the header equates an existential differentiable representative with an existential exact singleton support set. The singleton requires existence and uniqueness, not just at-most-one. Support remains one g working for every ambient y. The missing gradient conclusion must be tied to the same f,x and representative, rather than introducing an unrelated selected vector. |
| 3. Assumptions/regularity | The full header assumes only extended convexity and finiteness at x in the finite-dimensional geometry. It does not add properness, ambient interior, lower semicontinuity, closedness, or boundedness. Interior is the prerequisite theorem's conclusion. Global properness may be derived when needed; it must not be silently promoted into a new full-terminal premise. |
| 4. Conclusion/metric | The equivalence faithfully captures differentiability versus singleton support. It does not itself state that the singleton element is the gradient. The prose promises a companion but a machine-readable statement is absent. This is an actual source-coverage gap at contract level, independent of proof progress. |
| 5. Constants/normalization | The support inequality retains f(x)+<g,y-x><=f(y) with coefficient one and the correct displacement sign. Differentiability is the ordinary real Frechet notion of a local real representative, not directional differentiability, one-dimensional slopes, or a normalized alternative. No rates or asymptotics enter. |
| 6. Probability/feedback | Deterministic convex analysis only; no probability, feedback, stopping, regret, or measurable-selection claim is present. |
| 7. Boundaries/exclusions | f(x) must be finite; the theorem is not stated at either infinity. Ambient neighborhoods and ambient interior are used, not relative or punctured neighborhoods. Zero-dimensional E is allowed. Positive infinity away from a finite neighborhood is permitted. Boundary-domain points are not excluded by a full-terminal hypothesis; their failure of differentiability or singleton support must follow from the theorem's reasoning. |

## Differentiability representation

`SourceDifferentiableAt f x` means there exists a globally defined real h such that its EReal coercion agrees with f eventually in the ordinary neighborhood filter of x and h is differentiable at x. The eventual equality includes x and all points of some ambient neighborhood. Consequently it entails local finiteness and ambient interior membership; it is not merely differentiability of `f.toReal` at a point where infinite values have been converted artificially to reals.

This is an appropriate explicit formal interpretation of ordinary differentiability of an extended-real convex function at a finite point. Global real-valuedness is required only of the auxiliary extension h, whose values outside the neighborhood are irrelevant; f is not restricted to be finite everywhere. Any two such h agree near x and therefore have the same derivative at x. A gradient endpoint should reflect this representative independence rather than choose a particular off-neighborhood extension with unexplained mathematical significance.

There is no source properness premise to add. On the singleton side, even one global support at finite x rules out bottom at every y, and x is the finite witness. On the differentiability side, f is finite near x; combined with convexity this precludes negative infinity elsewhere by propagation along segments into that neighborhood. These are proof obligations or consequences, not added assumptions in the current header.

## Interior prerequisite and scratch scope

The scratch `singleton_subdifferential_interior` header agrees with the draft prerequisite. Its proof body takes a singleton support and, if x were not interior, obtains a nonzero supporting normal for the convex effective domain. It represents that normal by a nonzero vector d and constructs a second support g+d; the sign of the normal inequality makes this perturbation a lower support. Positive-infinite exterior values are handled separately, and global nowhere-bottom is derived from the existing support at finite x. Singleton equality then forces d=0, contradicting the construction.

This route derives ambient interior rather than assuming it. It is distinct from the earlier interior-existence producer, whose direction is interior implies a nonempty support set. The scratch file contains the prerequisite proof and a `SourceDifferentiableAt` definition but no proof of the full equivalence or gradient companion. Inspecting that source does not establish compilation, and even successful compilation of this leaf would not complete Theorem 2.22.

## Required contract repair

Add an explicit public companion header tying the same global subdifferential to the gradient of a genuine differentiable local real representative. A sufficient mathematical endpoint is:

For the same convex f and finite x, for every real-valued h agreeing with f on a neighborhood of x, if h is differentiable at x, then

`SourceSubdifferential f x = {gradient h x}`.

Alternatively, define a representative-independent source gradient and prove the singleton equals it; that choice requires its own well-definedness connection to actual derivatives. An arbitrary singleton witness renamed as a gradient without derivative identification would not repair the gap. No additional properness or interior premise may be added to obtain apparent source completeness. The endpoint may keep the full header's finite-x premise even though neighborhood equality already entails it.

After adding the companion contract, update the source-blind packet and obtain a reconstruction/review of that added endpoint. Keep the current receipt as a record of the initial omission rather than silently treating its absence as having been reviewed away.

## Blind reconstruction and final status

The new blind reconstruction correctly identifies the local representative semantics, exact singleton quantifier, lack of extra properness/interior assumptions, finite-point restrictions, and the missing derivative/gradient identity. Its disclosure of prior related mathematical-context exposure is clear; it remains source-blind for this assignment. No mismatch was found between its reconstruction and the displayed headers.

The equivalence/prerequisite **draft contracts** are semantically acceptable with the explicit finite-dimensional coordinate-free and local-representative interpretations. The packet is **not yet a complete full-source contract** until the gradient companion is formally stated. All proof acceptance remains pending; no full Theorem 2.22 result, external-human review, public integration, or Chapter 2 completion is claimed.
