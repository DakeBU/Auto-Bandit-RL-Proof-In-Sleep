# Next required closure targets: draft source/API audit

Printed p10/PDF22 four bullets remain required. The whole-source text search for convention/infinity/undefined found no mixed-infinity addition convention near the convexity statements; this negative search is not proof of an intended convention. The prior packet records an explicit counterexample to bottom-dominant EReal addition. Do not silently freeze the unrestricted source combination as that false target.

Dependency-ready general targets independent of that ambiguity:
- Affine precomposition preserves real-height epigraph convexity for every extended-real f, including both infinities. Lift the affine map A:E->F to A.prodMap(identity real) on epigraph coordinates, and use the locally inspected Convex.affine_preimage.
- Arbitrary pointwise supremum preserves epigraph convexity: its real epigraph equals the intersection of all real epigraphs. Use iSup_le_iff and convex_iInter. Include empty index (constant bottom) and genuine positive infinity. No nonempty index or bounded-family premise should be silently added.
- The monotone convex composition bullet explicitly uses real-valued f and g. Use the existing finite embedding bridge and locally inspected ConvexOn.comp, preserving global nondecreasing g.

Pinned local APIs inspected: Mathlib/Analysis/Convex/Basic.lean convex_iInter and Convex.affine_preimage; LinearAlgebra/AffineSpace/AffineMap.lean AffineMap.prodMap/prodMap_apply; Analysis/Convex/Function.lean ConvexOn.comp. Exact headers and tests still require a new contract before proof work. General nonnegative combination remains semantic-repair, not excluded or counted complete.

Draft closure headers explicitly elaborated: exactly three intentional unproved-body errors and no additional type/parser errors. This is feasibility evidence only; new contract fingerprints and stabilization are still required before proof.

## Primary-source convention evidence

Rockafellar, Conjugate Duality and Optimization, printed p6/PDF17, author-hosted https://sites.math.washington.edu/~rtr/papers/rtr054-ConjugateDuality.pdf, accessed2026-09-14. The paragraph on convex sums explicitly makes positive infinity dominate mixed-infinity addition, and distinguishes the opposite concave convention. This supports a separate named upper-addition operation for the full convex closure result. Applying it to Orabona's unstated convention is an explicit interpretation, not a claim that Orabona printed that rule. The next contract must record that attribution, preserve the counterexample for ordinary EReal addition, audit zero coefficients separately and verify the complete endpoint without a silent noBot restriction. No closure proof or acceptance follows from this citation alone.

## Proposed full-sum proof route (not frozen or implemented)

A named upperAdd(a,b) may be defined by negating the sum of negatives, so top dominates mixed infinities while finite addition agrees with real addition. The useful exact helper is: upperAdd(a,b) <= real(h) iff there exist real r,s with a<=real(r), b<=real(s), and r+s<=h. Prove all top/bottom/finite cases explicitly. Then the epigraph of a pointwise upper sum is convex by combining witnesses from both input epigraphs at two points. Positive scaling can use real height rescaling; zero weights need a separate zero-function case. This would preserve both infinities and all nonnegative coefficients rather than introducing a noBot premise. It remains a proposed route requiring exact contracts, type checks, actual proofs and nondegenerate mixed-infinity canaries.
