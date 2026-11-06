# Weighted potential in the proof of Theorem 2.13

The first equality on printed page 14 of Orabona’s *Online Learning: A Modern Introduction Using Convex Optimization* carries the same gradient-energy sum on both sides. Cancelling it gives an exact identity for the weighted change in squared distance. The last squared distance has a minus sign and uses the final played step size. The interior coefficients use successive differences of reciprocal step sizes.

The library proves the corresponding summation identity for real sequences and specializes it to squared distances in a normed additive commutative group. Five test theorems cover signed weights, a one-round free terminal value, constant and zero weights, and actual projected gradient and subgradient trajectories.

[Source page](https://arxiv.org/pdf/1912.13213v10#page=26) · [Statement, constants and checked proof uses](statement-and-proof.json) · [Current file bindings](evidence-map.json)

## Historical scope

The Chapter 2 freeze records 172 overlapping targets. It tracks the scope of the chapter, including later statement branches. Chapter-wide proof coverage remains partial. The two declarations above address the weighted potential equality.

[Freeze decisions and current scope](freeze-reconciliation.json) · [Coverage ledger](shared-book-coverage.json) · [Original PR219 paths and their continuations](original-path-continuations.json) · [Historical delivery](historical-delivery.json)
