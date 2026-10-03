# Candidate semantic review

Same-model sequential review, GPT-6 Astra/medium; not independent external review. The join theorem uses differentiability of its input functions with matching value and derivative at the seam. These are discharged by actual polynomial/affine derivative proofs when instantiated for Huber, not left as assumptions of huber_hasDerivAt.

The Huber target quantifies every real delta>=0 and every real residual. Inner joining at delta is quadratic/affine; outer joining at -delta is affine/inner. The proof uses -delta<=delta, not strict positivity, and therefore retains delta0. The final function is identified with the exact frozen absolute-value Huber definition through the proved three-piece identity. Five successful canaries cover both nonzero seams, quadratic interior, affine exterior and zero threshold. Failed canary01 is not accepted evidence.

Decision: scratch candidate only. Both exact terminals and complete context pass native fences; actual Lean compilation/axiom evidence is canary02. No public registry, root/Tests, full harness, site or graph acceptance is claimed for these scratch declarations. Remaining source obligations are sign-form derivative, convexity, vector gradient/feature bound and the actual unconstrained OGD guarantee. This is dependency-frontier progress toward Example2.15, not Chapter2 or whole-book completion.
