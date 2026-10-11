# Next bounded B4 producer: actual cumulative dual-norm stability

Proposal only: no Lean execution, BODY, elaboration, source acceptance or freeze. Select one theorem, `cumulative_optimistic_stability_dual_bound`, deriving the numerical bound for the actual cumulative objective from the newly accepted sharp stability producer. The separate neutral header contains no proof or source narration. Its canonical import is a future dependency: the reviewed stability module has not been assumed installed by this proposal.

## Exact source role and semantic delta

Orabona v10 PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Lemma 7.5 printed101–102/PDF113–114 gives the second, dual-norm inequality after the sharp stability estimate. Its proof on printed102 explicitly uses the elementary scalar bound with positive denominator parameter. Theorem 7.47 printed130/PDF142 repeats precisely this operator-dual-norm/Young step in its final displayed formula. This proposal supplies that actual finite-cumulative numerical summand. It does not prove either complete numbered result.

Relative to the accepted sharp stability header, every objective, domain, no-bottom, prediction-minimum and local-support premise remains unchanged. The only mathematical input change is explicit `0 < lam` instead of `0 ≤ lam`; the conclusion becomes `(G p).toReal - (G q).toReal ≤ ‖g‖²/(2*lam)`. This is a positive-curvature branch, required for the divided conclusion. No nonzero condition on g is needed: g=0 gives a useful nonpositive bound. Neither lambda0 nor negative lambda is silently assigned a divided source meaning. Lean's real division by zero is total, so the unqualified lambda0 version would be false.

The dual norm is exactly the operator norm of the actual continuous functional on the original normed E. It is not the Euclidean norm of source coordinates. In finite dimensions, a source vector covector is interpreted by pairing through arbitrary algebraic coordinates and endowed with the dual of the chosen original norm. A later coordinate consumer must establish that representation and norm identification; this proposal does not equate arbitrary coordinate Euclidean norm with the dual norm or assert an isometry. No norm-estimate premise is added.

## Intended proof dependencies and mathematical route (no BODY)

Genuinely invoke `cumulative_optimistic_stability` on the identical psi,hint,loss,n,V,lambda,p,g,q and actual internally supplied premises, using positivity to supply the parent's nonnegativity. This establishes the actual objective difference at most `g(p-q)-(lambda/2)*‖p-q‖²`.

Use the existing `ContinuousLinearMap.le_opNorm` at the actual displacement, together with the elementary real `g(v) ≤ |g(v)|`, to replace pairing by `‖g‖*‖v‖`. The remaining scalar inequality follows from the nonnegative square `(lambda*‖v‖-‖g‖)²` and positive `2*lambda`; equivalently it is completion of the square. This works also at g=0 and v=0 and uses no norm-attaining vector. The scalar argument stays local, avoiding an extra public wrapper. The resulting theorem produces a different numerical bound, rather than republishing the sharp parent unchanged.

Actual downstream use is n=t-1, psi=psi_t, hint=hint_t, p=x_t and q=x_(t+1), with each lambda_t positive. Add each numerical inequality to `OnlineCumulativePotential.finite_regret_identity` after the explicit finite EReal-to-real identification. Time-varying regularizer differences remain separate. The output removes dependence on the next-point distance from the stability summand, so it is the source's missing second performance edge.

## Reuse audit and alternative selection

Read-only search of `BanditRLProof/Online*.lean` found no existing arbitrary-continuous-dual quadratic-penalty optimization theorem or cumulative dual bound. Existing Euclidean OGD and OSD norm-square algebra concerns different update identities and does not provide this actual objective producer. Mathlib `Analysis/Normed/Operator/Basic.lean:239` provides `ContinuousLinearMap.le_opNorm`; its bound is the needed genuine norm parent. Existing generic scalar inequalities elsewhere in bandit modules involve square roots and unrelated parameters; no source-specific public copy is needed.

The accepted sharp stability leaf is the only necessary new source dependency. The cumulative regularizer producer can supply some total-curvature premises in later applications but is not universally required here. Full iff and the vector adapter do not produce global support existence and are not decorative dependencies. Existing `stronglyConvex_minimum_growth` already supplies BTRL's negative movement at a genuine current-objective minimizer; another BTRL wrapper would not advance the missing theorem.

A qualified unhinted ghost extraction is mathematically possible only after an actual attainment producer with the appropriate source closedness/coercivity/domain hypotheses. Merely taking an `IsMinOn G` premise would leave the important existence work untouched; asserting attainment from current hypotheses would be unjustified. The dual-norm edge is ready now without hiding that gap. An attainment theorem remains a separate substantive next target.

## Proposed discriminating checks, not canary headers or BODY

Use E=R, n=0, V=[-2,2], psi(x)=x²/2, hint=0, current loss=2x, p=0, q=-2, lambda=1, g(x)=2x. All component premises hold; actual G(0)-G(-2)=2 and ‖g‖²/(2*lambda)=2. The current objective is not minimized at p. This checks the squared dual norm and factor2 using the actual cumulative provider; an assumed output bound or bare arithmetic demonstration would not suffice. A non-Euclidean two-coordinate case can additionally distinguish operator norm from coordinate Euclidean norm, but should be independently scoped before adding a second consumer.

For the excluded lambda0 branch, choose V=[-1,1], psi=hint=0, loss=x, p=0, q=-1 and unit functional. The sharp-parent premises hold with zero curvature and actual difference1, while the divided expression evaluates to0 in Lean. This explicit failed extension justifies strict positivity. It does not weaken the existing sharp theorem, which continues to allow lambda0.

## Red boundaries and review gates

Reject any replacement of prediction minimization by current-G minimization, added G-support or output-bound premise, regularizer-only curvature restriction, assumed pairing bound, g≠0 restriction, coordinate Euclidean norm substitution, or unsupported finite-dimensional norm-attainment argument. Reject removing hbot because below-top permits bottom. The common finite-on-V branch remains a qualification relative to Algorithm7.8; Algorithm15.9 already prints common finite domain.

The positive terminal gap `G_T(z)-G_T(u)` in the frozen optimistic identity remains. Repeating the final hint does not make that gap nonpositive; truncating the last stability term does not fix it. The approved unhinted ghost requires h_(T+1)=0, psi_(T+1)=psi_T and an actual attained minimizer z of G_T. A repeated-hint alternative needs its explicit hint correction. This proposal chooses no ghost and deletes no terminal quantity.

For Theorem15.31, the approved repeated-point ghost and movement sum only through t<T remain distinct; the invalid repeated-loss endpoint is not rehabilitated by this positive-curvature numerical bound. General trajectory construction, qualified attainment/uniqueness, source global support existence, total finite/infinite branches, sum assembly, and repaired full7.47/15.31 remain open. All seven open-forward and six future C2 claims, accepted=false, null mandatory denominator and C1–16 hard targets remain unchanged.
