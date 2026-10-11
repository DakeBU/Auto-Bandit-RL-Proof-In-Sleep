# Next B4 edge: actual cumulative optimistic stability

Proposal only. No header elaboration, BODY, Lean execution, or production mutation. This chooses ONE derived finite-branch stability theorem, with its neutral unelaborated header separated from these source notes. It is mathematically valid and structurally dependency-ready; it still requires independent source/blind review and freeze. The finite/common-domain and continuous-dual local-support deltas are explicit review decisions, not hidden source equivalences.

## Exact mathematical role

For n prior losses, define A=psi+sum_(i<n)loss_i and G=psi+sum_(i<n+1)loss_i+indicator(V). Let p be an actual minimizer on V of A+hint, and let g support loss_n-hint at p on V. Assume the actual G has lambda-strong curvature, not that psi supplies all curvature. Then for every feasible q,
G(p)-G(q) <= g(p-q)-(lambda/2)||p-q||^2.
All displayed values are finite under the declared branch. The new content is the construction of support for G from the actual prediction and difference-loss support. The existing supplied-support theorem alone does not establish this missing algorithmic premise.

This exact difference is the stability summand G_t(x_t)-G_t(x_(t+1)) in the existing finite_regret_identity. Unlike a new minimum-growth wrapper, this statement permits nonzero g and p that does NOT minimize G. The hprediction binder is transparently the source Algorithm7.8 minimizer of prior losses plus hint; it cannot be changed to IsMinOn G. No performance bound or curvature of a different objective is smuggled into the inputs.

## Pinned source anchors and proof spine

Orabona v10 SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Lemma7.5 printed101-102/PDF113-114 constructs loss support at the prior-loss minimizer and then applies Lemma4.2. Algorithm7.8 and Theorem7.47 printed129-130/PDF141-142 replace prior loss objective by A+hint and use a subgradient of loss-hint. The source uses Theorem6.27 zero support plus Theorem2.23 sum inclusion. The proposed implementation proves the resulting support directly by adding the actual minimum inequality and the loss-minus-hint support inequality. These are the same source algebraic dependencies, without introducing a public artificial zero-support helper. Existing stronglyConvex_support_growth then supplies the exact quadratic improvement.

No claim that this proves the source's existence/uniqueness paragraph: Theorem6.9 and its closedness/coercivity/domain qualifications remain unproved by this edge. Source closedness and subdifferentiability hypotheses needed for those later parent conclusions are not demanded by this conditional inequality. The source hypotheses are preserved in the full parent; this extracted local implication is stronger where those unused existence hypotheses are dropped.

## Internal construction, no proof search performed

Use no-bottom plus below-top for included losses to obtain actual finite real identities. Finite sum preserves no-bottom; on V the actual G is a finite coercion and outside V its indicator gives top. The feasible p witnesses nonempty V, so existing sourceProper_of_domain gives SourceProper G. Derive G's feasible domain inclusion; do not assume properness/domain of a returned objective.

For z in V, hprediction gives A(p)+hint(p)<=A(z)+hint(z). hdifference gives loss_n(p)-hint(p)+g(z-p)<=loss_n(z)-hint(z). Add them and use the range(n+1) decomposition, obtaining G(p)+g(z-p)<=G(z). Call stronglyConvex_support_growth on actual G,V,lambda,p,q with this produced local support and the original hstrong. Rearrange via g(p-q)=-g(q-p) and norm symmetry. No use of the proposed conclusion or a fake minimum of G.

The pending cumulative regularizer producer is a sufficient way to supply hstrong for some downstream components, but imposing its regularizer-curvature assumptions here would improperly narrow the more general total-objective source branch. Its properness construction can be reused internally conceptually; the current public theorem bundles it with regularizer curvature, so direct reuse would require an unjustified hypothesis. Do not split out a new properness wrapper merely to manufacture a dependency: the existing sourceProper_of_domain plus explicit finite sum is sufficient.

The accepted full iff does not produce support existence, so it cannot discharge hdifference. The installed vector adapter converts source coordinates when needed, but the natural proof here consumes a continuous dual directly. A future source-vector caller must derive the coordinate functional internally as already reviewed in the adapter, retaining the original norm. Do not add an isometry or replace the penalty with coordinate Euclidean norm.

## Source/interface deltas requiring explicit review

Algorithm7.8 permits extended losses and only requires its played point in the current loss domain. This header intentionally selects the common finite-on-V branch, so full infinite-comparator/undefined-difference cases remain separate. It must not be labelled the full theorem. Algorithm15.9 already has V subset dom loss_t; this condition is not a newly discovered omission there. Below-top alone includes bottom, so hbot is independent.

Algorithm7.8's hint is printed as V->R and psi on X. Here real ambient extensions are harmless because hprediction and hdifference use only V. Crucially the header asks only LOCAL support on V, so its truth does not depend on an arbitrary off-V extension of the hint. Global coordinate source support implies this local hypothesis; the converse is not asserted. The conditional arbitrary normed-space version generalizes the finite-dimensional source and makes no finite-dimensional attainment claim.

## Real consumers and nonredundancy

For Theorem7.47, substitute n=t-1,psi=psi_t,hint=hint_t,p=x_t,q=x_(t+1). This produces each G_t stability summand before finite_regret_identity adds regularizer differences and the terminal gap. Lemma7.5 is hint=0. The positive-lambda dual-norm Young bound remains a separate missing scalar/operator-norm edge; lambda0 here is legal and never divided by.

For BTRL15.31 the analogous negative-stability case is already available directly from existing minimum growth at the actual current-objective minimizer. Do not create another BTRL minimum-growth wrapper merely to reuse this theorem. What BTRL still needs is real trajectory/attainment, sum assembly and the approved terminal correction.

## Frozen terminal obstructions remain operative

The exact frozen repaired optimistic target retains G_T(z)-G_T(u) in the finite identity. A repeated final hint can leave this terminal gap POSITIVE; the leaf above cannot delete it. The approved route uses an unhinted ghost h_(T+1)=0,psi_(T+1)=psi_T and an attained minimizer z of G_T, separately proving all conditions. Repeating the hint instead requires its explicit correction h_(T+1)(u)-h_(T+1)(z), not cancellation. Truncating the final stability summand alone does not repair optimistic regret: the frozen positive terminal-gap obstruction remains.

For repaired BTRL, choose ghost x_(T+1)=x_T and sum negative movement only through t<T; the optional stronger terminal term is -lambda_T||u-x_T||^2/2. Repeating the final loss is refuted by the frozen0<=-1/36 example and is not an accepted completion. This proposal chooses no ghost and asserts no terminal inequality.

## Review/failure gates

Reject replacement of actual hprediction by a minimizer of G; a pre-assumed support of G or stability bound; an added norm-estimate premise standing in for the dual bound; a new hstrong on the regularizer instead of the actual total; or cancellation of any terminal gap without the exact approved ghost/minimizer argument. Reject a source-vector caller that assumes an isometry, treats local support as global, or ignores finite-value transport.

A later discriminating consumer should use n=0,psi(x)=x^2/2,hint=0,p=0,current loss=x on V=[-1,1]. G's minimizer is -1, so p is not a minimizer of G. The produced nonzero support g(z)=z gives tight G(0)-G(-1)=1/2 at lambda1; no growth conclusion is supplied as premise. This is a suggested canary only, without frozen header/BODY. Terminal negative examples remain separate tests of the parent assembly.

All broader B4 obligations remain OPEN: general cumulative production, actual global support existence, qualified attainment/uniqueness, full Lemma7.5 including dual bound, 7.47 and15.31 repaired performance theorems. C2 seven open-forward containers plus six future claims, null mandatory denominator and accepted=false remain unchanged; no C1-16 endpoint shipping claim.
