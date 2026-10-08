# Frozen contract validation plan

These are planned validation cases, not compiled theorem proofs.

- Instantiate the generic nonpositive-limit bridge and convergence-premise iff on the same actual shared regret definition. A real negative ordinary limit remains legal; the API must not force zero or nonnegative regret.
- Instantiate the actual source meanPredict upper no-regret endpoint on all-zero observations. Its first prediction is 1/2, subsequent predictions are zero, and comparator 1 gives normalized regret -7/8 at T=2. This prevents treating NoRegret as a nonnegative-regret or zero-limit property. Revalidation covers the unchanged Asymptotic module, not a new algorithm.
- The obstruction learner is constant0 and belongs to [0,1] at every round; its output is independent of all observations and comparator. The feasible comparator set contains both 0 and1.
- Verify the actual first three affine losses at comparator1: -2, +2, -4. Both signs occur; time-uniform bounded loss is outside this example. The learner's losses are zero and the same prefix telescopes to F(T), not a supplied certificate.
- T=0 actual cumulative regret is0; T=2 comparator1 normalized regret is-1; T=3 it is0. The two infinite subsequences are positive, cofinal and distinct, not two isolated finite values.
- Use the public strict_separation endpoint to obtain the upper condition and the negation of the literal limit property on the same nonempty interval and actual loss/prediction process. Do not discharge through an empty domain or imported target-shaped assumption.

Public ROOT/Test integration, actual named lookup, axiom audit and full harness remain separate later gates. The exact nine header hashes, source fingerprint and six neutral contextual definitions stay frozen.
