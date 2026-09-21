# Static Musical Chairs: representative contract

2026-09-20. This is the selected mathematical target and explicit source repair,
not a compiled algorithm-to-regret result. All ten topic obligations remain.
The source and separate repair review receipts are recorded in
`runs/extended-topics-20260920/multi-agent-source-review.json`.

## Pinned source and endpoint

Jonathan Rosenski, Ohad Shamir and Liran Szlak, *Multi-Player Bandits -- a
Musical Chairs Approach*, ICML 2016, PMLR 48:155--163.
Official record: https://proceedings.mlr.press/v48/rosenski16.html.
Main physical p3: Algorithms 1/2, Definition 1, Theorem 1 and its explanation
of conditioning. Supplement physical pp1--7: concentration statements and the
complete static A.1 chain, Lemmas 2--4. Main and supplement SHA256:

- `c56474f0c3e689c1819b11e2bca4d3e5dcaef6eddfd0173bb55ff6a84f11d99d`
- `4ffd4d0c3fc975ae04b3d5e96911bd58d66bc2206e9d9584e18fcbf0c5b305ad`

The representative endpoint is the actual static, unknown-player-count MC
algorithm's global pseudo-regret, including exploration, estimation failure
and random coordination. Known-N coordination alone is not this endpoint.
Dynamic entry/exit, asynchronous clocks, no collision sensing, heterogeneous
player rewards, capacity-sharing arms and MEGA comparison theorems are distinct
models. They are not silently included or used as assumptions here. A recent
primary-source comparison remains mandatory; the classic audit does not close
the literature obligation.

## Primitive model and local information

There are K arms and N players, with 1 <= N < K, synchronized rounds and a
common start. Each arm has an arbitrary stationary probability law supported
on [0,1], with mean mu_a. Construct fresh independent arm rewards over rounds
and private independent uniform action coins, independent of the rewards.
The model must admit continuous reward laws, not only finite PMFs or Bernoulli
instances. One latent reward per arm/round suffices: at most one player can
observe it without a collision.

All players choosing the same arm in a round receive zero if their number is
greater than one. Each player observes its own action, a separate collision
indicator, and its reward when collision-free. Reward zero is not a collision
test. The learner knows K, the common exploration duration, and a number
epsilon with 0 < epsilon < Delta, where Delta = mu_(N) - mu_(N+1) > 0.
The actual N, means, other players' histories and the proof's good event are
not learner inputs. A fixed public arm order resolves ties. Means within the
top N may tie; only the boundary gap is required.

## Exact algorithm and totality conventions

For 0 < delta < 1 use exactly S exploration rounds, with

    S = ceil max{ (16 K / epsilon^2) log(4 K^2 / delta),
                  50 K^2 log(4 K / delta) }.

This explicitly changes the second logarithm from the printed log(4/delta).
It preserves the first coefficient and logarithm using a different, verified
mathematical proof. No claim is made that the increased second term is necessary
or that the printed final theorem has been disproved.

At each exploration round every player draws a fresh uniform arm, ignoring
past rewards. Player i stores collision count C_i and, for every arm, the count
and sum of its collision-free rewards. Empirical mean is sum/count; define it
as zero if the count is zero. At the end of exploration compute

    Nhat_i = min(K, round(1 + log((S-C_i)/S) / log(1-1/K))).

If C_i = S, use Nhat_i = K. For valid counts in the regular branch the real
inverse is at least one; implement a total natural-valued rounded/clamped
version and prove agreement on valid states. Specify ties in rounding even
though the good event stays strictly away from half-integers. Sort empirical
means using the fixed arm tie rule and retain the first Nhat_i arms.

Initially every player is unfixed. Each unfixed player independently samples
uniformly among its own retained arms. After its first collision-free pull it
fixes permanently on that arm. A fixed player stays there even if another
player later collides with it. No arm is returned only after a successful loop;
the policy is a total causal trajectory at every finite horizon.

The source's inclusive `t=0 to T0` is reconciled with its T0 denominator by
using rounds 0,...,S-1. If T<S, run only T exploration rounds and use the
deterministic short-horizon bound. A proof may construct an infinite causal
extension, but the finite learner must not inspect post-horizon feedback.

## Required performance statements

Let A_star be the unique top-N set, and define, on the actual joint trajectory,

    R_T = sum_(t<T) [sum_(a in A_star) mu_a
                    - sum_i mu_(A_it) 1{player i does not collide at t}].

Always 0 <= R_T <= NT. For T>=S construct the exploration-measurable event G
that every local top-Nhat set is A_star and every Nhat equals N. Prove
P(G)>=1-delta, and from the fresh continuation after every G-history derive

    E[R_T | G] <= NS + 8N^2 <= NS + 2 exp(2) N^2.

The last inequality recovers the printed, weaker static coordination residual.
It is conditional expected pseudo-regret, not a pathwise high-probability
constant bound. Since delta<1, P(G)>0 and conditioning is meaningful. For every
finite T, including T=0 and T<S, the mandatory unconditional endpoint is

    E[R_T] <= min{NT, NS + 8N^2 + delta NT}.

Also expose the version with 2 exp(2) N^2 for source comparison. For T>=2,
delta=1/T gives the corresponding horizon-dependent logarithmic exploration
bound and failure residual N. At fixed delta, the unconditional residual is
linear in T and must not be erased. Equality with expected realized regret is
an unconditional fresh-reward statement; it cannot be transferred to a
reward-dependent exploration event without a separate proof.

## Mandatory producers and acceptance

1. A total local policy, observable local state, actual joint action/reward
   process, and prefix causality. The global model may index N players; the
   per-player decision function cannot receive N.
2. The exact exploration observation and collision laws and their temporal
   independence. Produce conditional reward laws from the joint construction.
3. Random-count concentration, all-player estimation, constructed ranking,
   and an actual exploration-good event of probability at least 1-delta.
4. The fixed-arm distinctness invariant, conditional fixation hazard, finite
   survival sum and global regret charging bound for the actual continuation.
5. The same process's full conditional and unconditional endpoints, short
   horizons, and the delta=1/T corollary.
6. A full-learner nondegenerate public-root canary with N=2, K=3, Bernoulli means
   3/4,1/2,1/4 and epsilon=1/8. Check observation probability 2/9 and collision
   probability 1/3, nonzero collision/transient regret, zero-reward sensing,
   and local ranking order invariance. A coordination-only example is useful
   but does not replace this canary.
7. Blind reconstruction, anti-anchored source comparison, separate source-repair
   review, axiom/dependency audit, shared library root, Tests, full harness,
   registry/reader/site synchronization and contribution manifest.
8. A bounded classic/recent source disposition and actual compiled reuse,
   failure and descriptive ICLR case evidence. Controlled all-topic evaluation
   remains a separate unexecuted program obligation.

No tail bound, correct N estimate, common ranking, successful settlement, or
coordination cost may be supplied as a premise of the final theorem. Intermediate
conditional interfaces are allowed only with actual producers and consumers.

## Status and graph boundary

The accompanying `MULTI-AGENT-PROOF-ROUTE.md` contains the mathematical repair
and concentration ledger. No production declarations or public-root result
are claimed by this contract. The route ledger records the selected contract;
topic completion remains false. Lean Graph: no new certified edge yet.
Functor Hypergraph: no new certified transport; random-count averaging is a
candidate mechanism only, and fails without reward-independent selection.
Teaching/book routes, results, registry and public site remain unchanged until
an independently reviewed implementation packet is ready. No main integration,
deployment, controlled experiment or efficiency improvement is certified.
