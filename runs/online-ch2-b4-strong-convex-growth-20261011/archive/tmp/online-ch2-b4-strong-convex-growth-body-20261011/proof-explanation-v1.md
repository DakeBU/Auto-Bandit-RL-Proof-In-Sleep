# Conditional quadratic minimum growth candidate

This is the direct segment alternative, not a reconstruction of the printed support/subgradient proof. The exact frozen theorem is unchanged.

Write P = toReal(f p), Q = toReal(f q), and c = (lam/2)||q-p||^2. Properness excludes bottom globally and V subset effectiveDomain excludes top on V; hence both endpoint values equal the casts of P and Q. The supplied minimum gives P <= Q. The nonnegative modulus gives c >= 0.

If the desired P+c <= Q failed, let g=Q-P. Then 0 <= g < c, so c>0 and a=(g+c)/(2c) lies strictly between zero and one. Convexity of the literal V puts a p+(1-a)q in V. Combining the minimum inequality at this point with the supplied strong-convexity inequality, then transporting finite endpoint arithmetic from EReal to real arithmetic, yields

P <= a P+(1-a)Q-c a(1-a),

or equivalently (1-a)(c a-g) <= 0. But c a=(g+c)/2>g and 1-a>0, a contradiction. This covers lam=0 and coincident points automatically: in those cases the contradictory c>0 branch cannot arise.

The proof never casts the segment value to real; it composes the EReal minimum and interpolation inequalities before casting the finite endpoint expression. Thus it does not identify infinite segment values with zero or need an extra finite-part/closed-weight premise. No public helper or selector is introduced. The source existence/support/sum-rule/cumulative/terminal obligations, full B4, all 7+6 containers and claims remain open.

Validation so far: Candidate-v1 focused compile exited0 on clean cb7ea30f3f74db0bc459e9629be092665023718f. Independent proof review, dependency/axiom probe, canaries, integration and full post-BODY gates are separate pending stages.
