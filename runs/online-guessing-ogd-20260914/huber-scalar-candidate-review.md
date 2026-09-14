# Huber scalar representation candidate

Source Example2.15's exact absolute-value loss is represented by three affine/quadratic pieces, with both threshold equalities preserved under delta>=0. A separate theorem proves the zero-threshold loss is identically zero. The proof splits the three real intervals and treats the lower seam equality explicitly; it does not assume differentiability or convexity.

V1 header probe and leaf01 failed because the real-comparison definition lacked `noncomputable`. V2 explicitly records that context-only repair with the same two statement hashes; its header probe fails only the two intentional bodies. Leaf02 and canary01 genuinely compile. Canaries evaluate both nonzero outer branches, both seams and delta0. Both theorem axiom prints contain standard axioms only. Native checks and exact-prefix/hash evidence are in huber-scalar-frozen-check.json; candidate and canary sources are retained as .lean.txt.

Same-model GPT-6 Astra/medium review accepts this scratch prerequisite. It is not a public declaration, and no combined root gate is claimed for scratch code. The later derivative/convexity/vector-gradient/unconstrained-OGD source endpoint remains required. Seam candidate and scalar representation are reusable foundation growth, not Example2.15 closure.
