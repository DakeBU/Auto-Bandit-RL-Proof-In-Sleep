# Musical Chairs coordination occupation checkpoint

Code snapshot: `4e79ff440beafd3e3e08e93416706044e34a2f3e` on
`codex/research-extended-topics`. Canonical project remains the shared
BanditRLProof/Lake library. Source/canary review is accepted with explicit
component scope; common harness/site gates are recorded separately in
`runs/extended-topics-20260920/multi-agent-occupation-validation.json`.

Promoted the previously reviewed scratch transition and exact joint law into
`BanditRLProof/Algorithms/MusicalChairsCoordination.lean`. The new
`MusicalChairsCoordinationTime.lean` proves the numerical1/(4n) hazard,
probability-zero return of fixed players, actual bind-recursive survival,
finite playerwise sum<=4n and total expected unfixed occupation<=4n^2.
The endpoint is a finite sum of expectations under actual state marginals;
it does not claim a full-history conditional path law or pseudo-regret.

Both modules are reachable from BanditRLProof.lean. Tests.lean imports six
public-root component canaries: actual collision and successful-draw paths,
exact isolated-event probability1/4, a fixation lower bound, all-horizon
occupation<=16 for two players/three arms, and the one-player boundary.

There are54 production declarations, including38 proved propositions, plus
six canary theorems. The all60-declaration axiom audit found only standard
Lean axioms. Independent neutral reconstruction and source comparison bind
the exact files and all three folded blocks in the reader:
`research-wiki/papers/extended-topics-musical-chairs-coordination.md`.
The reviewed source/axiom receipt is
`runs/extended-topics-20260920/multi-agent-occupation-review.json`.

The next mathematical edge is the global2U pseudo-regret charge with fixed
arms distinct and in the true top set, followed by integration under the same
coordination law. The unknown-N exploration law, arbitrary bounded rewards,
local collision-count estimator, ranking concentration, good-event producer,
full conditional/unconditional regret and mandatory full-learner canary all
remain required. Recent full-proof source comparison and all-topic ICLR
controlled evidence remain open. No topic is marked complete; no main merge
or deployment is claimed. Historical scratch artifacts remain as immutable
review evidence; they are not additional production libraries.
