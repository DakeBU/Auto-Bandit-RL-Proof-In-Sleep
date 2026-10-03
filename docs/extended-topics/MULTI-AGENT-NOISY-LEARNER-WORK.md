# Frozen stochastic full-learner canary

Source/target: the existing MULTI-AGENT-CONTRACT.md static repaired algorithm,
mandatory canary n=2,k=3, independent Bernoulli arm means 3/4,1/2,1/4,
epsilon=1/8. Fix delta=1/4; retain actual source explorationLength and all
finite horizons. Do not replace the learned candidate kernel with a supplied
correct set. Owner: MusicalChairsNoisyLearnerPrototype.lean scratch extension.

Reuse: actual reward/visible law and primitive-source expected regret; proved
source good-event probability; exact good-event rectangle factorization;
existing allowed two-player draw mass and two-round transient path. Two-point
real measures adapt the existing HeavyTailRegretCanary measure interface.

Mathematical target: prove the arm means and genuine noise from the actual
reward integrals; derive true top set {0,1} and numeric gap 1/4. The actual
learned exploration good event has mass at least 3/4. On this event each player's
candidate set is {0,1}; a two-round private draw path that first collides and
then separates has conditional mass 1/16. Thus its intersection with successful
actual exploration has unconditional mass at least 3/64. Its coordination
pseudo-regret is exactly 5/4. Carry this event into the complete reward law,
retaining actual noisy future coordinates rather than substituting means.

Instantiate the complete visible-law bound for every H, with the exact duration
S, yielding min(2H,2S+32+H/2). Check actual effective observation probability
2/9, collision probability 1/3, zero-reward sensing and local ranking order
invariance using the same law/interfaces. Limited earlier fixtures are parents,
not substitutes for the full learned-law event and endpoint.

Validation/review: focused compilation, all new declaration/instance axiom
audit, distinct blind reconstruction and source review; reader with exact code
and explicit scope. Public-root canary acceptance still requires extraction
and combined root/Tests/harness/site gates. Scratch success alone does not close
the topic. No new source repair or controlled-efficiency result is intended.

Graph disposition: new scratch consumer and positive-probability witness edges;
partial Overview update after review; no public graph/registry mutation before
production. Functor Hypergraph none-found-with-reason: no new cross-topic
transport, only the existing first-moment interface and kernel factorization.
