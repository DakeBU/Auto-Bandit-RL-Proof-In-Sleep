# Fresh reward process and unconditional realized-regret transport

Source: pinned Rosenski--Shamir--Szlak static Algorithm1/2 and Theorem1,
within the frozen repaired contract. Target: extend the actual action process
with fresh continuation reward arrays, complete chronological feedback, and
unconditional expected realized=pseudo regret. Never infer conditional equality
on the exploration reward-dependent good event.

Owner: runs/extended-topics-20260920/MusicalChairsRealizedPrototype.lean.
Semantic fingerprint: fixed arbitrary [0,1]-supported arm probability laws,
separate collision bit, reward zero on collision, exact phase/horizon indexing,
private candidate draws from learned local feedback and no future observation
access. Realized regret may be negative on an individual sample.

Reuse: rewardLaw and coordinate preserving/mean/bounded theorems; existing
explorationFeedback and learnerAction; probability kernel first marginal;
finite schedule measurability, product integrability/Fubini and integral-map
transport. Reuse a single schedule/reward expectation interface for exploration
prefixes and continuation instead of duplicate mean arguments.

Reader/review: exact folded scratch, source/metric/conditioning limits,
distinct blind and source actors plus axiom audit. Adds actual reward/feedback
producer and expectation transport edges; public graph changes wait for shared
extraction/root/Tests/harness/site gates. Full stochastic learner canary and
recent-source/all-topic evidence remain separate mandatory obligations.

## Implemented and focused verification

The actual complete latent law is the learned exploration/continuation law
times an independent continuation reward array. Complete feedback is measurable,
its action/collision fields agree with the prior learner, local candidates are
recovered from completed exploration feedback, and local state updates use the
visible action/collision bit. The observed reward-sum identity holds at every
finite horizon, including empty and truncated phases. Its pushforward law is a
probability measure. Signed integrability and unconditional realized=pseudo
expectation transport now supply the primitive-source visible-regret bound.

Failed elaboration attempts were resolved without changing the statement or
raising maxHeartbeats: explicit integral sample types prevent expanding the
entire coordination recursion during unification. Dependent finite sums use
finCongr/Fintype.sum_equiv; feedback record constructors carry explicit reward
array types. The final focused file compiles with no errors or warnings. The
diagnostic trace commands were removed before freezing.

There are 54 new scanned declarations (43 theorems, 11 definitions) and three
named measurable/probability instances. All 57 were checked with #print axioms;
only propext, Classical.choice and Quot.sound occur. The original Comparator
prefix is byte-identical. Exact new-layer folded code in the reader is verified.
Three metric/feedback fixtures compile; none is labelled the full noisy learner.

The next mandatory canary must instantiate the actual source learner with
n=2, k=3 and Bernoulli means 3/4,1/2,1/4, epsilon=1/8. It must connect the
actual explorationLength and learned kernel to the all-horizon endpoint, prove
the exact 2/9 effective observation and 1/3 collision probabilities, and
demonstrate positive-mass transient coordination under the learned law. Existing
arbitrary supplied-candidate fixtures are insufficient. The numeric source
duration is large, so symbolic law identities and positive-mass event proofs
are appropriate; exhaustive path enumeration is not required by the contract.

Graph/publication disposition: new scratch theorem and observation-law edges;
Overview updates only the multi-agent partial progress. Production Lean Graph,
teaching routes, result registry, contributor credit and generated site are
unchanged because public extraction and combined gates have not run for this
layer. Functor Hypergraph: none-found-with-reason; the shared schedule first-
moment interface is reused inside this topic, with no new certified cross-topic
transport claimed. Main, anonymous snapshots and live deployment are untouched.
