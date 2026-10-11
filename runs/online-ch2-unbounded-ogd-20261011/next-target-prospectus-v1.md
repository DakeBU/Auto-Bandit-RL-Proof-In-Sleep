# Proposed next target: actual variable-step OGD failure

Choose `forward:unbounded-variable-OGD-failure`, owned by `forward:chapter5-unbounded-variable-OGD-failure`. Chapter2 PDF26/printed14 names OGD; Theorem5.4 PDF64–65/printed52–53 states the unprojected OSD lower bound.

The full local `OnlineUnboundedOSD.theorem_5_4` already proves the existential convex 1-Lipschitz lower bound with the exact alpha/T threshold and phi constant. Its actual printed public type and standard-axiom evidence are preserved in the JSON. The explicit affine switching witness, scalar/vector lower bounds, phi range and limit already exist; do not reprove them.

The remaining concrete reconciliation is the algorithm name: the terminal public theorem uses actual subgradient-selector regret, while the Chapter2 pointer says gradient descent. On these finite affine losses the gradient and subgradient coincide. First ask a distinct source reviewer whether the existing APIs already discharge this bridge; if an explicit terminal interface is needed, prove one actual `iterateVariable`/`regretVariable` integration theorem by transferring the existing witness lower bound. Avoid a new family of tiny wrappers. Preserve horizon-dependent adversarial witnesses and nontrivial-dimensional scope.

This is more dependency-ready than unrestricted ambient differentiability, whose B1 semantics remain open. It is a proposal only: exact leaf freeze and authorization follow current package acceptance. No proof or source-progress count, no container closure, and no change to B1–B7, the eight open containers, six future claims, or null denominator.
