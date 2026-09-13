# Conversion Window: Orabona v10 projected OGD

Task id: `ONLINE-OGD-CH2-FIXED`
Contract: `docs/contracts/online-ogd-v1/contract.md`.
Exact frozen headers: original JSON captures in that directory; corrected native
validation metadata in its `fences/` subdirectory. The statement hashes agree.

| Source symbol | Lean meaning |
|---|---|
| finite-dimensional real Euclidean space | E with real inner product and completeness; EuclideanSpace instantiation in public canary |
| nonempty closed convex V | Domain.carrier with nonempty/closed/convex proofs |
| Euclidean projection | project, constructed by mathlib minimizer existence; uniqueness via variational inequality |
| convex differentiable loss on a neighborhood | RegularLoss V f |
| x1 | initial x₁; iterate ... 0 |
| xt and gt | iterate ... (t-1), gradient (loss (t-1)) at that iterate |
| xt+1 | step on current loss; iterate ... t |
| sum t=1,...,T | Finset sum over range T |
| comparator regret | regret V eta loss x₁ u T |
| source gradient bound L | G, evaluated on the same tuned trajectory |
| diameter D | positive uniform pairwise distance upper bound |

## Frozen assumptions and information

The fixed-step theorem requires eta>0, x₁ in V, regular losses for t<T,
and u in V. It has no finite diameter or gradient bound. For T=0 the proof
reduces to exact zero regret and cancellation of the initial/terminal potential.
Eq. (2.1) additionally requires T>0, D>0, G>0, and the specified uniform bounds.
No division by zero cases are hidden in the tuned theorem. Projection construction
is classical exact-real mathematics, not an executable floating-point solver.

The recurrence only reads loss t in constructing point t+1. `iterate_prefix`
proves equality of points for equal strict loss prefixes. The algorithm is fixed
before quantification over comparators, and the tuned step uses a priori bounds.
This is deterministic pathwise regret; no probability or distribution premise occurs.

## Ready-leaf route and conversion limits

Projection existence/characterization -> distance contraction; convex affine-line
secant derivative -> first_order; both -> lemma_2_12; actual iterate plus feasibility
-> scaled finite telescope -> theorem_2_13_fixed -> positive tuning -> equation_2_1.
Source formula has the initial norm reversed; norm symmetry gives the same square.
Both parts of the source Lemma 2.12 are retained as a conjunction.

Allowed edits after freezing: theorem bodies, local proof helpers, canary,
source evidence, imports of the new module, and the shared Book mapping. A changed
terminal needs a new reviewed contract version. Failed proof bodies do not license
changing assumptions. See the run's failure table and fence-metadata-repair.md.
