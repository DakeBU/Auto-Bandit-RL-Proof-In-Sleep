# Next B4 dependency proposal: coordinate-vector support under an arbitrary chosen norm

Status: PROPOSAL ONLY. No statement seal, blind decoding, independent source approval, elaboration, proof body, Lean build, publication, or acceptance is claimed. The header is deliberately a `.txt` document without a body. This formalizer does not fill either independent reviewer role.

## Snapshot and ownership

Canonical source is `E:/ABRL/research`; inspected isolated checkout is `E:/ABRL/worktrees/research-online-book`, branch `codex/research-online-ch2-strong-convex-support`, HEAD `ceef2d303da1398bd543d144930e3ec7e1b58263`, tracked working tree clean at inspection. Origin is `https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep.git`. No fetch/pull, Git mutation, production modification, build or browser activity was performed because the parent owns concurrent combined gates and restricted this assignment to create-only planning. The checkout stays in place. Every new artifact is under this proposal directory.

Read-first contracts and the repository substantive-advance, semantic-roundtrip, and Lean-formalization skills were consulted. Curated process-memory rule `ABRL-PM-ATOMIC-SOURCE-ASSUMPTIONS` applies. Historical personal memory was used only to identify the source-faithfulness workflow, not to assert current acceptance.

## Sole proposed mathematical leaf

Module candidate: `BanditRLProof/OnlineStrongConvexSourceSubgradient.lean`.
Sole public declaration: `BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth`.
Exact proposed imports/context/header: `proposed-header-v1.txt`.
Outcome class: reusable-interface, `adapt_existing`.

Let E be a real normed space with specified algebraic coordinates e : E ≃ R^d. If f is proper, V is convex and contained in dom f, and f obeys Definition 4.1 with modulus lambda >= 0 in the norm on E, then every source vector subgradient g of the coordinate function f o e^{-1} at e(p) gives

    f(q) >= f(p) + <g, e(q-p)> + (lambda/2) ||q-p||_E^2

for p,q in V. There is no isometry condition on e. The Euclidean inner product supplies only the source coordinate pairing, and never replaces the norm in the quadratic term. Finite dimensionality and continuity of the resulting functional are derived inside the proof, not public premises. This is a forward-only dependency of Lemma 4.2, not its full iff.

This interface expresses the missing bridge between the existing Euclidean source-subgradient library and the existing norm-generic support-growth result. It has a real mathematical use: nonzero loss/difference-loss source subgradients can now feed the source's strong-convexity stability calculation without an implicit Euclidean-norm restriction. It is not a zero-support wrapper or an easy surrogate consumer.

## Pinned source and scope

Source: Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10. PDF `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, verified this turn. `source-extracted-v1.txt` is a fresh `pdftotext -layout` extraction of these exact bytes; textual inspection is not a new pixel audit.

Anchors: Definition 2.20 (printed 16-17/PDF 28-29), Definition 4.1 and Lemma 4.2 (printed 34-35/PDF 46-47), Lemma 7.5 (printed 101-102/PDF 113-114), Theorem 7.47 (printed 129-130/PDF 141-142), Algorithm 15.9/Theorem 15.31 (printed 266-267/PDF 278-279).

The parent support contract is `docs/contracts/online-ch2-b4-strong-convex-support-v1/source-contract-v1.json`. Its previously unfinished vector/chosen-norm interface is exactly this proposal's scope. The effective target freeze `docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json` remains untouched. The proposed leaf has no horizon or terminal binder and cannot discharge the separately recorded terminal corrections.

## Atomic binder ledger

| Binder | Classification | Expanded meaning / source relation |
|---|---|---|
| E, NormedAddCommGroup E, NormedSpace real E | TYPING | Real vector carrier with one chosen genuine norm; its norm is used in both strong interpolation and conclusion. No InnerProductSpace instance on E. |
| d, e | TYPING | Finite coordinate representation of the source R^d; e is a linear bijection with inverse, not an isometry. All finite-dimensional normed R^d choices fit. Derive FiniteDimensional real E from e.symm. |
| f | TYPING | Extended-real objective on E. The source coordinate objective is u ↦ f(e^{-1}u). |
| V | TYPING | Literal feasible subset of E, source feasible set e(V). No shrink/intersection of V. |
| lam | TYPING | Real strong-convexity modulus. |
| hf | SOURCE | SourceProper f = (forall x, f x != bottom) AND exists x r:real, f x = coe r. Finite witness is not assumed inside V. |
| hV | SOURCE | Convex real V, as in Definition 4.1. |
| hdom | SOURCE | For every x in V, f x < top. Together with hf, all evaluations on V are real finite. |
| hlam | SOURCE | 0 <= lam; no strengthening to strictly positive lambda. |
| hstrong | SOURCE | Exact Definition 4.1 interior interpolation a in (0,1), with coefficient (lam/2)*a*(1-a) and the chosen norm on E. |
| p,hp,q,hq | SOURCE | Evaluation/support points p,q in the unchanged V. They imply V nonempty for this invocation; no extra nonemptiness binder. |
| g | TYPING | Ordinary coordinate vector in EuclideanSpace real (Fin d). |
| hg | SOURCE | Exact supplied source subgradient: forall u in R^d, f(e^{-1}(e p)) + coe <g,u-e p> <= f(e^{-1}u). Global quantifier; not just on V. |

Definition audit: reuse literal SourceSubdifferential, SourceProper, effectiveDomain. No new choice-defined object. SourceSubdifferential itself permits improper functions, but hf rules out those regimes here. The global coordinate function is proper by bijectivity (derive if needed, never add a binder). `toReal` is justified by hf/hdom on p and q, not by its fallback values.

Explicit scope delta from full Lemma 4.2: the leaf proves only the forward implication for one supplied g at p. It assumes V subset dom f from Definition 4.1, not V subset dom partial f. Existence of a subgradient at every V point is unnecessary for this implication and remains unproved. The source equivalence/converse and equality-to-inequality typo in the converse proof stay OPEN. No closedness, differentiability, global convexity, attainment, hmin, norm-equivalence bound, continuity premise, or nonzero-g condition is added.

## Source proof spine and genuine consumers

Author's source route: Definition 2.20 supplies affine support based at p, evaluated at the interior segment point p+a(q-p); Definition 4.1 gives the upper interpolation bound; divide by positive a; let a decrease to zero to obtain the quadratic support lower bound. This is the forward proof of Lemma 4.2. The converse's two supports at the interpolated point, their weighted sum, and its printed erroneous equality are excluded from this leaf with explicit OPEN status.

Implementation alternative: derive the continuous functional L(z)=<g,e z>; restrict the exact global support to z in V; invoke stronglyConvex_support_growth with the original f,V,lam,p,q and L; simplify L(q-p). Existing support-growth internally tilts f by an affine functional and reuses stronglyConvex_minimum_growth. That different Lean proof topology must remain separate from the author's alpha-to-zero source proof. The functional adapter is the new representation work; quadratic growth is genuinely supplied by the existing theorem.

Lemma 7.5 consumer: source first produces gt in partial(Ft+ell_t+indicator(V))(xt) using zero optimality support of Ft+indicator(V) and Theorem 2.23 inclusion. Feed that actual global vector support into this leaf for the inclusive objective at xt and xt+1, then rearrange the FTRL stability difference and apply Holder/Young for the second inequality. Attainment/uniqueness from Theorem 6.9, support assembly/properness, indicators, and dual-norm Young are still separate obligations. In particular, source-subgradient sum inclusion's proper-component premises must be discharged from actual consumer assumptions, not silently added to Lemma 7.5.

Theorem 7.47 consumer: the support is the actual difference-loss vector ghat_t in partial(ell_t-hint_t)(xt), transported through zero support of the hinted minimization objective and sum inclusion into partial(Ft+ell_t+indicator(V))(xt). This leaf supplies the nonzero affine term plus the negative stability penalty after rearrangement. Do not assume the difference loss is convex globally merely for sum-equality API convenience; use the actual support inclusion. Do not replace the source's cumulative strong-convexity hypothesis with new componentwise hypotheses.

Theorem 15.31 remains downstream of the audited 7.47 specialization hint_t=ell_t, with zero difference support. Its proper/closed/strong inclusive objective assumptions do not justify pretending arbitrary component functions are already proper or subdifferentiable. Attainment and the approved terminal policy remain independent open obligations. A zero-support canary alone would not validate the proposed vector adapter.

## Reuse search and API readiness

Inspected current local declarations: stronglyConvex_support_growth, stronglyConvex_minimum_growth; SourceSubdifferential and subgradient_point_finite in OnlineSubgradientBasic; SourceProper/SourceClosed and sourceClosed_iff_lowerSemicontinuous; theorem_2_23_inclusion and theorem_2_23_equality in OnlineSubgradientSum; indicator_subdifferential_eq_normalCone in OnlineNormalCone. No existing Online module supplied a separately chosen norm with the existing source vector support. Sum-equality imposes extra qualification and is not needed here.

Inspected pinned Mathlib:

- LinearEquiv.finiteDimensional in LinearAlgebra/FiniteDimensional/Defs.lean: e.symm transports finite dimension of EuclideanSpace back to E.
- innerₗ in Analysis/InnerProductSpace/Basic.lean: real algebraic pairing; compose `(innerₗ _ g)` with e.toLinearMap.
- LinearMap.toContinuousLinearMap and its coe simp lemmas in Topology/Algebra/Module/FiniteDimension.lean: every such map on finite-dimensional E is continuous. This avoids an explicit norm-equivalence constant.
- innerSL in Analysis/InnerProductSpace/LinearMap.lean is another possible implementation, but using an inner product on E would collapse the chosen norm and is forbidden.
- WithLp.linearEquiv and EuclideanSpace.equiv supply concrete finite-coordinate canary equivalences.
- NormedSpace.Core/ofCore APIs exist for alternative re-norming representations, but this header avoids local competing norm instances entirely.

No new library/toolchain/dependency is requested. There was no external-library web search because the pinned local Mathlib provides the needed bridge and the assignment prohibits browser activity. Readiness: mathematically dependency-ready; named APIs located; proposed header has NOT been elaborated, and API/instance issues would be API_BLOCKED rather than mathematical refutations. A neutral typing-only check can follow independent header review and parent authorization without adding theorem-body placeholders.

## Failure boundaries and public canary proposals

Reject any successor header introducing InnerProductSpace E, an isometry e, a supplied continuity or finite-dimensionality witness that is derivable from e, hmin, quadratic support as a premise, strict lambda positivity, global finite f, or a narrower V. Reject a proof that replaces ||q-p||_E with the Euclidean norm of e(q-p), even if the chosen canary happens to make them equal.

Public positive canary 1 (non-Euclidean, nonzero support): E = Fin 2 -> real with its standard sup norm, e = (WithLp.linearEquiv 2 real (Fin 2 -> real)).symm, V=[-1,1]^2, f(x)=(x0^2+x1^2)/2+x0 on V and top outside, lambda=1, p=(0,0), g=(1,0), q=(1,1). f is proper and finite exactly on V, its interpolation gap dominates (a(1-a)/2)||x-y||_infinity^2, and g globally supports the coordinate extended objective. The output is 3/2 <= 2. Separately assert ||q-p||_E^2=1 while the coordinate Euclidean squared norm is 2. Whole canary must directly depend on the proposed public declaration, whose compiled term must in turn depend on stronglyConvex_support_growth. The explicit norm comparison checks the intended norm distinction. This first numerical inequality alone does not reject the erroneous Euclidean penalty: replacing the squared sup norm 1 by the coordinate Euclidean squared norm 2 still gives the true inequality 2 <= 2. The dependency and coefficient checks do not turn that numerical canary into a discriminating counterexample.

Positive canary 2 (coordinate scaling): use e'(x)=2e(x) and g'=(1/2,0) for the same f,p,q,V. The linear term remains 1 and the quadratic term remains 1/2; scaling coordinates must not scale the chosen-norm penalty. Explicitly check that ||q-p||_E^2=1 while ||e'(q-p)||_2^2=8. The correct conclusion is still 3/2 <= 2; replacing the chosen-norm penalty by the scaled coordinate Euclidean penalty would instead give 5 <= 2, which is false. Thus this second canary discriminates against that norm substitution and exercises coordinates that are not isometric. These checks remain proposed obligations; no canary proof or execution is claimed. It is a separate canary, not an extra production theorem.

Boundary canary 3: lambda=0 with affine objective and genuine nonzero coordinate support, equality conclusion. Optional d=0 canary confirms no hidden Nontrivial E/d>0 condition. Negative/source review guards: bottom-improper objective cannot exploit toReal; q outside V does not satisfy hq; no assertion of support existence or minimizer attainment. All are proposals; no canary body or compile is present.

## Publication and hard-target preservation

If later approved/proved, publish the coordinate-pairing versus chosen-norm distinction next to the forward support inequality, exact Lean and real dependency links. Lean Graph: planned new adapter node with planned edge to support growth; not yet a solid proof edge. Overview: B4 dependency advances only after gates; full Lemma 7.5, Theorem 7.47, Theorem 15.31 remain open. Functor: none-found-with-reason; changing a coordinate representation is an explicit interface, not evidence of a certified new functor. Root imports/tests, declaration registry, reader page and ordinary combined project/harness/site gates remain parent-owned future work. No progress credit or graph metadata was edited in this planning pass.

Hard targets retained unchanged: full Lemma 4.2 iff and converse, source equality typo treatment, support existence, source-qualified closed/proper strong-convex attainment and uniqueness, full stability/dual-norm bounds, 7.47 and 15.31 terminal repair obligations, all B4 effective targets, Chapter 2, and the entire Chapters 1-16 main-text goal. Suggested next process: independent blind reconstruction of header/context, anti-anchored source review and topology audit, then an authorized exact statement seal and sequential proof work after the current leaf's acceptance gates.
