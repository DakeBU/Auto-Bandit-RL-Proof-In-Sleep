# Attained covered causal design

`CausalOptimalAllocation.lean` proves the existence of an actual PMF allocation
minimizing the source objective over **all covered allocations**, with objective
value at most the number of actions. `optimalAllocation` chooses this proved
witness; it does not take an optimizer or its performance as an assumption.
This is a noncomputable mathematical choice, not a numeric solver implementation
or an optimization-runtime bound.

The proof constructs a real coordinate representation of the finite probability
simplex and a PMF from every simplex point, proving the exact mass correspondence.
It intersects the compact simplex with the finitely many closed constraints
Q(z)>=P_a(z)^2/K, K=|A|. Uniform allocation lies in this set. Every point in it
covers the union support: a positive action mass makes its squared lower bound
strictly positive. Zero allocation weights remain allowed.

The coordinate objective equals the existing PMF maximum second moment. Each
term with zero action mass is identically zero; each nonzero numerator has a
strictly positive denominator on the constructed set. This yields continuity
there, and the extreme-value theorem gives a minimum. Every covered allocation
whose cost is <=K belongs to that set by the previous sublevel theorem. Any
other covered allocation has cost >K and cannot improve the chosen minimum.
Thus minimizing the compact set proves global optimality on the required
covered domain, without optimizing the misleading totalized-division formula
on uncovered simplex faces.

The public interfaces prove coverage, the K upper bound and comparison with
every covered allocation. Structural canaries check coincident action laws:
the optimal cost is exactly one, and a boundary allocation with a zero action
weight remains covered and optimal. These are allocation checks, not substitutes
for the frozen noisy algorithm-to-regret canary.

Still required for the frozen source line: parallel-model allocation bridge,
actual repeated sampling and recommendation, source-level Bernstein/tuning and
full simple regret, noisy full-chain canary, independent semantic review,
shared topic mapping and all-topic ICLR evidence. Topic acceptance remains open.
