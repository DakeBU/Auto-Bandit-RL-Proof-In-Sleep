# Research roots and exact unresolved suppliers

This ledger is a research specification, not a Lean theorem or a claim of novelty.
The compiled analytic and process leaves are listed in README.md and the proof-term
graph. The following missing suppliers cannot be replaced by assumptions in a theorem
claiming to implement either full project.

| Root | Present status | Next exact obligation |
|---|---|---|
| Born effect stability and aligned circuit bias | compiled | physical loading, finite-bit synthesis and alignment acquisition remain separate |
| Fresh computational-basis PMFs and fixed-n classical adaptation | compiled | allowed general measurement, stopping and interruption semantics |
| Bias/statistical-radius recommendation failure transport | conditional | produce the actual estimates and conditional tails from reset queries |
| A depth-dependent estimation cost | external theorem; not locally ported | instantiate projector reflections, literal word counts, fresh shots and integer caps |
| A gap-dependent and gap-free regret upper bounds | speculative | concrete policy, all-history coverage, horizon truncation and expectation calculation |
| A matching minimax lower bound | speculative | hard oracle family, adaptive transcript information and testing reduction |
| Adaptive reset transcript information, basis-only fixed-n refinement | compiled local increment | actual finite trace PMF and injective list/historyLaw bridge; H² bounded by D times the average of both environments' expected arm-weighted query costs; stopping, arbitrary measurements, testing and K-arm reduction remain open |
| B cost envelope and adaptive epsilon-BAI complexity | speculative | feasible fidelity selector, real cost certificate and stopping/termination |
| Horizon-independent uniform O(K) weak-oracle regret | refuted by pinned external lower bound | the requested soft-O expression must retain horizon logarithms |
| Uniform fine-accuracy BAI with irreducible identical biased oracles | refuted mathematical example below; not a local Lean lower bound | finer identifiable fidelity or a different stated target |

## A: intended policy and accounting interface

The next proposed policy has dyadic target radii, active-arm sets and a summable
stage/arm failure schedule. An estimate must return its actual list of reset plans,
classical outcomes and interval; its cost is the sum of each plan's forward plus inverse
count. The interval producer must be valid conditional on every supported previous
classical history. Only then can the compiled interval elimination lemmas be applied.

A stage may run only if its literal integer query cap fits the remaining horizon.
Stopping before an incomplete block and selecting the remaining exploitation arm need
an explicit rule. Every exploitation query is charged too. In particular, a policy
that simply completes an estimation stage after exhausting T violates the contract.
For ties the active optimum set is nonempty; no positive gap is assigned to a tied
optimal arm. K>T does not permit one free initial query per arm. D=1 must use an actual
one-query fresh-sample estimator, rather than an empty Grover schedule.
The displayed cost interpolation requires D>=1. The more general compiled Plan type
also allows D=0, where all words have zero unknown-oracle calls; no information or
performance claim is made for that case. T=0 has zero charged regret and permits no
oracle call.

The candidate gap sum is over positive gaps. The candidate gap-free split must add
the small-gap contribution T*r and optimize r only after accounting for integer caps,
logs and incomplete exploration. The trivial regret bound T uses rewards in [0,1].
Failure contributes at most T times its probability, so the all-history schedule must
make that term explicit. None of these policy/performance roots is currently proved.

The compiled Hellinger bound is for one basis-measurement block. Converting actual
`blockPMF` masses into that bound, proving the adaptive classical-history recurrence,
and supplying hard Bernoulli-unitary environments are distinct next leaves. A fixed
pair of unitary points can be perfectly distinguishable, so a two-point calculation
alone does not imply the horizon-logarithmic lower bound in the pinned prior work.

Local continuation update: `AdaptiveTranscript.lean` in this private adapter project
now closes fixed-n adaptive information accumulation. Its actual kernel masses are
derived from the existing evaluated words; no per-block information assumption is
added. Its finite PMF pushes forward injectively to the existing `historyLaw`, and
uniform weighted cost is proved equal to existing `historyQueryCost * eta^2`.
With a natural all-trace budget T, H² <= D*T*eta². This is not a literal
infinite-List tsum theorem and does not construct horizon clipping or stopping.
The first paragraph above describes the prior milestone, now superseded only
for this explicitly named fixed-n basis refinement.

The arm-local bound retains BOTH environments' expected weighted query costs.
It cannot directly replace those by baseline-environment counts to obtain the
K-arm minimax rate. A one-sided/stopped comparison or another verified hard-family
reduction is a new exact open leaf. No sqrt(KT/D) theorem follows automatically.

## B: an implementable finite selector must precede the envelope

For each actual finite fidelity list, store the fixed implemented circuit, matching
dagger, target-bias alignment certificate, coherent query cap and real primitive-cost
certificate. The existing expansion theorem counts `knownGates + q*oracle.length`.
Replacing this by g*q requires a proved bound on the known gates; preparation/readout
per shot and any certification cost must be added if the advertised cost includes them.
The present theorem does not supply these costs for an amplitude estimator.

At target radius r, only entries with b<r are feasible. A finite argmin can choose an
entry only when this set is nonempty. An empty set means an explicit infeasibility
outcome, or an infinite extended-real envelope; it cannot mean zero cost. Statistical
radius s=r-b is positive. The continuous expression
g*[1/s+1/(D*s^2)] omits confidence logs and integer caps. A final envelope must minimize
the estimator's certified integer query/shot/gate bound at failure level alpha, plus
its other stated costs. Optimizing this expression is currently a proposed design,
not the actual local proof of a resource bound.

A conservative first algorithm can require b<=epsilon/4 for every arm, estimate the
implemented mean to epsilon/4 at per-arm failure delta/K, and use the existing actual
finite-enumeration recommendation. This has the compiled correctness transport once
the statistical producer exists. Adaptive elimination can improve allocation, but its
termination and comparison to per-arm Phi require separate proofs. Any claim of new
multi-fidelity optimality also requires more than this known radius-composition rule.

An identifiability obstruction: suppose every available implemented arm/fidelity is
the same mean-1/2 unitary, with fixed bias bound b>0. Two ideal instances can have means
(1/2+b,1/2-b) and the swapped pair, for b<=1/2. They induce identical complete query
transcripts under every policy. For epsilon<2b their unique epsilon-optimal arms are
opposite. If the common output probability of arm 1 is p, uniform success would require
both p>=1-delta and p<=delta, impossible for delta<1/2. This is an exact fixed-bias
obstruction, not a drifting-noise model or a formal quantum minimax theorem.

## Admission and implementation boundaries

Noncomputable exact-real PMFs and argmax have mathematical semantics; they are not
finite-bit samplers or free computations of unknown means. The whole estimator and
policy must supply their own computational and confidence evidence. External quantum
papers/resources remain candidate dependencies until a compatible local adapter
compiles. Prior-art absence in the inspected set is not a global novelty proof.

Publication remains draft because the earlier concrete gate-cost adapter lacks full
pre-proof exact-signature coverage. The later reset increment has contemporaneous
signature evidence and an independent review; that does not retrospectively repair
the earlier gap. No accepted registry or atlas complexity node is fabricated.
