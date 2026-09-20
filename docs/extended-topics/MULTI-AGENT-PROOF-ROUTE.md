# Static MC: proof route and explicit repair

Read `MULTI-AGENT-CONTRACT.md` for the pinned source, algorithm and quantifiers.
This is mathematical derivation, not a claim that its Lean chain is complete.

## Source versus repair

Supplement Theorem 5 has its lower-tail inequality direction reversed.
The count-threshold inversion in A.1.1 also prints 1/(8q) where 8/q is needed.
The proof mixes conditioning on different count events, and its final assembly
does not pay for all players' N estimates. These are defects of the displayed
proof, not a counterexample to the final bound. The PDF's absolute values in
Lemma 3 are present; a text-extraction omission is not a mathematical defect.

The route below avoids the count-threshold step altogether and uses a global
failure split delta/2 for rankings and delta/2 for population estimates. Only
the second logarithm in the sample budget changes. The static coordination
proof is sharpened without changing the policy. Separate reviewers inspect
the source and this repair; neither review alone is a Lean semantic round trip.

## Exploration law and direct random-count averaging

Write b=1-1/K. For a fixed player i and arm a, let V_t indicate that i chooses
a and every other player chooses a different arm. Independent uniform private
coins give q=P(V_t=1)=b^(N-1)/K. For fixed i,a, these indicators are independent
over time, so D=sum_(t<S) V_t has Binomial(S,q) law. Different players' counts
need not be independent. The elementary bound b^(N-1)>=1/4 gives q>=1/(4K).

Condition on the entire finite exploration action schedule h. Its law is
independent of the reward array because exploration ignores rewards. The
D(h) selected reward coordinates therefore remain independent arm-a draws
with support [0,1] and mean mu_a. Hoeffding gives

    P(|muhat_ia-mu_a| > epsilon/2 | h)
        <= 2 exp(-D(h) epsilon^2/2).

For D(h)=0 the right side is 2, so the same bound holds trivially with the
zero empirical-mean convention. No separate positive-count event is needed.
Finite mixture over the complete schedules yields

    P(|muhat_ia-mu_a| > epsilon/2)
      <= 2 E exp(-D epsilon^2/2)
       = 2 (1-q+q exp(-epsilon^2/2))^S
      <= 2 exp(-S q (1-exp(-epsilon^2/2)))
      <= 2 exp(-S epsilon^2/(16K)).

For the last step, x=epsilon^2/2 is in (0,1/2];
exp(-x)<=1-x+x^2/2<=1-x/2. Thus 1-exp(-epsilon^2/2)>=epsilon^2/4.
The preceding step is 1-y<=exp(-y) for y=q(1-exp(-x)). Union over NK<=K^2
pairs bounds ranking failure by delta/2 at the contract's first budget term.
On the complementary event, for a in A_star and c outside A_star,

    muhat_ia - muhat_ic >= mu_a-mu_c-epsilon >= Delta-epsilon > 0.

Hence each player's sorted first N set is exactly A_star, independent of ties
or different orders inside it. Combine with Nhat=N, not before.

## Population inverse and all-player union

For player i, let B_it indicate any collision. These are iid over exploration
time with mean p=1-b^(N-1). Put p_hat=C_i/S and q0=1-p. Hoeffding yields

    P(|p_hat-p| > 1/(10K)) <= 2 exp(-S/(50K^2)).

To prove estimator correctness without relying on the source's informal Taylor
margin, choose gamma=2/5<1/2. Since q0>=1/4, concavity of z^gamma and convexity
of z^(-gamma) at z=1 give

    q0(1-b^gamma) >= q0 gamma/K >= 1/(10K),
    q0(b^(-gamma)-1) >= q0 gamma/K >= 1/(10K).

Thus |p_hat-p|<=1/(10K) implies

    q0 b^gamma <= 1-p_hat <= q0 b^(-gamma).

All quantities are positive; in particular p_hat<1. Dividing logarithms by
log b<0 reverses inequalities and places
1+log(1-p_hat)/log b in [N-gamma,N+gamma]. Rounding gives N, and the cap at K
does not change it. Handle N=1 directly or through the same inequalities.
The all-collisions fallback cannot occur on this event. Union over N<=K yields
failure <=2K exp(-S/(50K^2))<=delta/2 at the second budget term. No independence
across players is asserted. The intersection with the ranking event defines G.

## Actual random coordination

Fix any exploration history in G. All local candidate sets equal A_star,
although their enumerations may differ. Every subsequent unfixed player draws
fresh uniform coins on its own enumeration, hence uniformly on that same set.

Induction proves that fixed players occupy distinct arms. Old fixed players
stay fixed; a new fixed player had no other player on its arm that round, so
it cannot share with an old or simultaneous new fixed player. This statement
holds deterministically, for every draw sequence.

Suppose u>=1 players remain unfixed at a coordination round. There is a top
arm unoccupied by fixed players. For a tagged unfixed player, the event that it
chooses that arm and the other u-1 unfixed players avoid it has conditional
probability

    (1/N)(1-1/N)^(u-1) >= 1/(4N).

For N=1 this probability is one; do not divide a logarithm by zero. For N>=2
use u<=N and (1-1/N)^(N-1)>=1/4. The event implies fixation at this round.
The bound holds after every admissible current history, not only on average.

Let U_r be the number unfixed before round r of coordination. Repeated tower
conditioning gives, for each tagged player,

    P(still unfixed before r | exploration history) <= (1-1/(4N))^r.

The waiting times of different players need not be independent. Summing over
players and a finite number L of remaining rounds gives

    E[sum_(r<L) U_r | exploration history]
      <= N sum_(r<L) (1-1/(4N))^r <= 4N^2.

For a pathwise regret charge, let c be the number of fixed players hit by an
unfixed player in the round. Distinct fixed arms allow each such collision to
be charged to a different unfixed player, so c<=u. At least N-u-c distinct top
arms give their means to collision-free fixed players. The top-N comparator
therefore loses at most u+c<=2u; other successful players can only reduce the
loss because all means are nonnegative. This yields round pseudo-regret<=2U_r,
and total expected coordination pseudo-regret<=8N^2. Averaging over G-histories
preserves the bound. Exploration contributes at most NS deterministically.

The source residual follows from exp(2)>=4. Splitting expectation over G and
its complement gives the delta NT residual. The trivial NT bound and the
short-horizon case complete the endpoint for every finite T.

## Concentration and regularity ledger

| Object | Produced law / conditioning | Range and mean | Tail or use |
|---|---|---|---|
| V_t for fixed i,a | Independent uniform joint actions, iid over t | {0,1}, q=b^(N-1)/K | Exact Binomial Laplace transform |
| Selected arm-a rewards | Conditional on complete reward-independent action schedule | [0,1], mu_a | Two-sided fixed-count Hoeffding at epsilon/2, then finite mixture |
| B_it for fixed i | Same exploration coins, iid over t | {0,1}, p=1-b^(N-1) | Two-sided Hoeffding at 1/(10K), union over players |
| Fixation indicator | Fresh joint coins conditional on complete past | {0,1}, conditional success >=1/(4N) while unfixed | Iterated conditional survival, not iid geometric trials |
| R_T | Actual local-policy joint law | [0,NT] | Integrate good and bad events; retain delta NT |

Counts, rank selection and collision events are measurable finite combinatorial
functions. Reward sums, logs on their explicit positive domains, rounding and
piecewise fallbacks require measurable policy producers. Bounded reward sums,
finite-horizon regret and exponential transforms used above are integrable.
No infinite expectation or stopping-time interchange is needed for the finite
geometric sum. For arbitrary reward measures, use finite product measures and
explicit finite action-schedule mixtures; PMF-only feedback is insufficient.

## Retrieval, owning modules and next Lean boundary

Searched `tools/bandit.py search-memory collision` and `list-lean-decls collision`:
no existing collision declarations. Inspected the shared Mathlib retrieval cards
for finite sums, finite types, measure/integral and probability independence.
Mathlib's `PMF.uniformOfFintype`, `PMF.map`, `PMF.bind` can construct finite
joint action and coordination kernels. `Causal.nodeJoint` is a dependent finite
PMF history constructor, but importing a causal-specific wrapper is not needed
for a uniform finite joint draw. Existing `HeavyTail.independent_sum_mgf` is a
candidate genuine concentration reuse; its current bounded-second-moment MGF
does not by itself give the exact Hoeffding coefficient above. Search the pinned
Hoeffding/sub-Gaussian APIs before deciding to add any shared leaf. The pinned
`Mathlib/Probability/Moments/SubGaussian.lean` supplies
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` (line 860) and
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` (line 780).
The former centers an a.e. measurable [a,b]-valued variable with proxy
((b-a)/2)^2; the latter gives exp(-r^2/(2 sum proxies)). For [0,1] and r=D
epsilon/2, applying it to both signs gives exactly 2 exp(-D epsilon^2/2)
when D>0. These are inspected compatible upstream producers, not yet consumed
by the prototype or an actual schedule-conditioned law adapter.

Initial owner: planned `BanditRLProof/Algorithms/MusicalChairs.lean` and subsequent
law/concentration/regret modules in the existing project. First bounded proof
is the actual coordination transition and fixed-arm distinctness invariant;
it is infrastructure for the required chain, not the endpoint. A scratch
prototype must stay labelled as such until public-root integration, independent
semantic decoding, source comparison and common gates are completed. New
general-purpose probability lemmas require targeted shared declaration search
and actual downstream consumers before promotion.
