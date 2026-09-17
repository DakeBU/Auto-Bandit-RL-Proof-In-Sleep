# Lipschitz full endpoint contract: HOO, explicit source repair

Frozen before HOO implementation, 2026-09-17. This is one mandatory representative line within the all-ten program, not a reduction of that program. No theorem in this contract is accepted merely because a producer compiles.

## Sources and classification

Primary: Bubeck, Munos, Stoltz and Szepesvari, X-Armed Bandits, JMLR 12 (2011), pp.1655-1695. Frozen PDF SHA256 DCBBC42AE1DDC5A21153594A542D593D85B4F18913D9776A16221E2E31BE68EF. Locators: Section 2 model; Section 3 / Algorithm 1 and equation (3); A1/A2 and Lemma 3; Definitions 4-5; Theorem 6; complete Appendix A.1, Lemmas 14-17 and its four-step proof.

Read all these source sections and the entire endpoint proof. Visually checked pp.1661-1662 for the algorithm/covering corrections. The source's other algorithms (truncated/local HOO) and minimax lower bounds are not this selected line. Their exclusion does not waive any obligation of Theorem 6's line.

Recent primary comparison: ICLR 2025, Lipschitz Bandits in Optimal Space, frozen SHA256 16F77EBDF6734A93323B60726AAE8921D4D9C37EC9FD08CE0CD61FC90DCDBEA8. Read model, Algorithms 1-2, Lemmas 1-5, Corollary 1 and proofs of Theorems 1-2. This comparison motivates explicit memory/causal semantics but its claims are not imported: bounded real magnitudes do not imply exact logarithmic bit representations; its printed geometric sum inequality fails at a=2,B=3 (22>16, visually confirmed p.7); later-round shallow revisits need a bound beyond the comparison arm's gap. These are separate proof gaps, not a blanket refutation of its asymptotic rate. The lower-bound proof also needs its dimension-dependent factor in log K and the nearest-center loss comparison checked before reuse. Other 2026 candidates are screened only, not accepted sources for this endpoint.

Repairs/adaptations, explicitly distinct from unchanged source reconstruction:
- Equation (2), p.1661, has P_(h,2i) on the right: use the intended right child P_(h+1,2i), as specified by the surrounding tree definition and subsequent formulas.
- Algorithm 1 initialization prints B_(1,2)=B_(2,2)=infinity: initialize both children of the root to infinity via the general unexpanded-node rule.
- Theorem 6 prints all n>=1 with log(n), which is zero at n=1. Use log(max(n,2)) in the algorithm's confidence and terminal bound; record the first rounds explicitly.
- Retain post-round n statistics and use them only to select round n+1. The proof's use of same-index statistics for selection must be repaired, never hidden by an off-by-one alias.
- Choose the left child deterministically on a tie and a fixed representative in each nonempty region; Section 3 explicitly permits these choices.
- Implement node labels as finite binary words. Prove correspondence to binary children/depth, rather than creating a finite-arm replacement or a horizon grid.

## Model and exact algorithm

A nonempty measurable arm space with measurable mean f in [0,1], and stationary reward laws supported on [0,1]. An actual sequential reward construction must produce the conditional law at the selected arm. It is sufficient to construct kernels on the countably many fixed region representatives, without adding global continuity or compactness assumptions.

The covering tree has root X and each region equals the union of its two children's regions. Regions are measurable and nonempty. A nonnegative, possibly asymmetric dissimilarity ell has ell(x,x)=0; no triangle inequality is assumed. A1 supplies geometric diameter bounds nu1*rho^h and pairwise disjoint contained open balls of radius nu2*rho^h at each depth; nu1,nu2>0 and 0<rho<1. A2 is exactly

    f* - f(y) <= f* - f(x) + max(f* - f(x), ell(x,y)),

where f*=sup f, not an assumed attained maximizer.

Initially only the root is expanded and it has no sample. Every round starts at the root, follows the child with largest B (left on ties), stops at an unexpanded node, plays its representative and expands it. Update counts and reward sums for every prefix of the selected word. Unvisited U and unexpanded B are positive infinity; for visited nodes U is the empirical mean plus sqrt(2 log(max(n,2))/count) plus nu1*rho^depth. For expanded nodes B=min(U,max(B_left,B_right)). All B values are recomputed consistently after the round. A finite recursion fuel may implement this only with a proof that it exceeds the expanded depth; no fuel cutoff changes the selected node.

## Mandatory performance endpoints

1. Actual measurable causal HOO action/reward process, fresh selected nodes and exact path statistics/backward B semantics.
2. Geometry Lemma 3 for approximate region suprema, optimal branches without assuming attainment, disjoint packing bounds and the near-optimality limsup definition. Derive a uniform packing constant for every d'>d, including coarse scales; do not assume the desired node-count bound as an ultimate premise.
3. Moment-generating / martingale deviation producers for predictably selected regions under the actual reward law, including never-visited-again cases. No region-IID assumption or supplied confidence-event oracle.
4. Source Lemmas 14-17 with explicitly repaired time indices and all constants/initial rounds accounted for: actual poor-node selection and expected visitation bounds.
5. The actual three-way tree regret partition, shallow-node one-play contribution, poor-branch contribution, geometric summation and integer depth optimization.
6. For finite near-optimality dimension d, each d'>d admits gamma>0, depending on the environment and source parameters but not the horizon, such that for every n>=1 the actual expected pseudo-regret is at most

    gamma * n^((d'+1)/(d'+2)) * log(max(n,2))^(1/(d'+2)).

7. Equality of expected cumulative regret and pseudo-regret under the constructed reward law, with integrability proved. Fixed policy and compatible law across horizons.

## Acceptance

Joint public root, Tests and full harness; genuine infinite-arm/noisy/nonconstant-mean canary or an explicitly delimited nondegenerate finite-depth instance plus an infinite-arm model witness; axiom audit; independent semantic review; source repair ledger; shared registry/site mapping; compiled reference/transfer evidence and ICLR evaluation package. All remain required. Efficiency experiments must use a separately frozen valid protocol; this development is descriptive evidence only.
