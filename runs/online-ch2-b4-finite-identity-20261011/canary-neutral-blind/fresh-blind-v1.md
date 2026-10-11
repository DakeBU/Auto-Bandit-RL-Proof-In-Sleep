# Fresh source-blind reconstruction v1

## Actor and exposure

Actor: delegated agent /root/b4_finite_identity_canary_blind. Requested configuration: Astra medium; runtime model and reasoning configuration were not independently attested. This report does not certify that requested configuration was used.

Only two external input files were actually read, both specified neutral complete-header text files. No PDF, source prose, imported Lean module, review, parent rationale, other workspace file, repository metadata, or memory file was opened. The actor inherited generic system/developer context, the available-tools and skills catalog, memory summary already embedded in that context, workspace AGENTS instructions, and the parent task message. It did not consult or use that embedded memory summary for reconstruction. Thus “source-blind” describes the two-file input boundary, not an assertion of an empty conversation context.

Inputs, actual SHA256:

- E:/ABRL/worktrees/research-online-book/tmp/online-ch2-b4-finite-identity-canary-proposal-20261011/neutral-one-round-complete-header-v1.txt: 7d10ab86d93f97a5ac03db64ce96b8759a0a64d7bd440fa5bfbbe666717be75e
- E:/ABRL/worktrees/research-online-book/tmp/online-ch2-b4-finite-identity-canary-proposal-20261011/neutral-two-round-complete-header-v1.txt: 718a2eb714597c34033cc4d35af06b00b3718768cd60799800c6e487c777af64

Both match the requested hashes. Both texts name namespace BanditRL.OnlineCumulativePotentialCanary, list imports, and supply a theorem type without a body. Imports were not opened. No Lean proof, elaboration, build, gate, source comparison, or source-faithfulness assessment was performed.

## Shared exact notation and identity

All time indices are natural numbers; v, u, z and all function values are real. Define sum over range n as sum over integer indices 0 <= t < n, with empty sums zero. Natural subtraction T-1 is truncated subtraction. G(t,v) = psi(t,v) + sum_{i=0}^{t} loss(i,v): its loss sum is inclusive of index t.

For each separately specified set of local lets below, abbreviate:

R = sum_{t=0}^{T-1} [loss(t,y(t)) - loss(t,u)].
A = psi(T-1,u) - psi(0,y(0)).
B = sum_{t=0}^{T-1} [G(t,y(t)) - G(t,y(t+1))].
C = sum_{0 <= t < T-1} [psi(t,y(t+1)) - psi(t+1,y(t+1))].
D = G(T-1,z) - G(T-1,u).

Each first conjunct is exactly R = A + B + C + D. In particular the terminal correction has the order z minus u, the potential variation has order t minus t+1, and the within-round difference uses the SAME G(t,.) at y(t) and y(t+1). In the header the final two terms are written '+ G(T-1,z) - G(T-1,u)', equivalent to +D. These abbreviations are exposition, not extra Lean hypotheses or lets.

## One-round declaration

Name: finite_identity_one_round_positive_gap.

All local lets, in order:

1. psi : N -> R -> R, psi(t,v) = v^2/2 for every t.
2. loss : N -> R -> R, loss(t,v) = (v-1)^2/2 for every t.
3. x : N -> R, x(t) = 1/2 for every t.
4. u : R = 1/2.
5. z : R = 2/3.
6. T : N = 1.
7. y : N -> R, y(t) = z if t=T, and x(t) otherwise.
8. G : N -> R -> R, G(t,v) = psi(t,v) + sum_{i=0}^{t} loss(i,v).

Consequently y(1)=2/3, and y(t)=1/2 for all t != 1, including t=0 and t>=2. This is a single-index endpoint splice, not a persistent change of all later points. For every natural t, G(t,v) = v^2/2 + (t+1)(v-1)^2/2, where t+1 is interpreted as a real coefficient.

The entire proposition is the conjunction of these SEVEN statements:

1. R = A+B+C+D.
2. R = 0.
3. A = 0.
4. B = -1/36.
5. C = 0.
6. D = +1/36.
7. NOT (R <= A+B+C).

Explicit index expansion: R=loss(0,y(0))-loss(0,u); A=psi(0,u)-psi(0,y(0)); B=G(0,y(0))-G(0,y(1)); C is the empty sum; D=G(0,z)-G(0,u).

Ordinary arithmetic cross-check: G(0,1/2)=1/4 and G(0,2/3)=5/18, giving B=-1/36 and D=1/36. The identity is 0 = 0-1/36+0+1/36. The last conjunct is NOT (0 <= -1/36), equivalently 0 > -1/36. It negates a bound that omits D; it does not negate the identity.

## Two-round declaration

Name: finite_identity_two_round_terminal_splice.

All local lets, in order:

1. psi : N -> R -> R, psi(t,v) = ((t:R)+1)*v^2/2.
2. loss : N -> R -> R, loss(0,v)=v; loss(1,v)=-2v+1; loss(t,v)=0 for t>=2.
3. x : N -> R, x(0)=0; x(1)=1; x(t)=100 for t>=2.
4. u : R = 3.
5. z : R = 2.
6. T : N = 2.
7. y : N -> R, y(t) = z if t=T, and x(t) otherwise.
8. G : N -> R -> R, G(t,v) = psi(t,v) + sum_{i=0}^{t} loss(i,v).

Consequently y(0)=0, y(1)=1, y(2)=2, and y(t)=100 for t>=3. Again only the exact endpoint index is spliced. G(0,v)=v^2/2+v; for every t>=1, G(t,v)=((t:R)+1)*v^2/2-v+1. In particular G(1,v)=v^2-v+1.

The entire proposition is the conjunction of these NINE statements:

1. R = A+B+C+D.
2. R = 1.
3. A = 9.
4. B = -7/2.
5. C = -1/2.
6. D = -4.
7. x(2) = 100.
8. y(2) = 2.
9. y(2) != x(2).

Explicit index expansion:

R = [loss(0,0)-loss(0,3)] + [loss(1,1)-loss(1,3)] = -3+4 = 1.
A = psi(1,3)-psi(0,0) = 9.
B = [G(0,0)-G(0,1)] + [G(1,1)-G(1,2)] = (0-3/2)+(1-3) = -7/2.
C = psi(0,y(1))-psi(1,y(1)) = 1/2-1 = -1/2.
D = G(1,2)-G(1,3) = 3-7 = -4.

Thus the displayed identity reduces to 1 = 9-7/2-1/2-4. The original endpoint x(2)=100 does not enter B: the t=1 term uses the spliced y(2)=2. No failed-inequality conjunct is present in this declaration.

## Premises, boundaries, ambiguity and evidence limits

These are closed propositions with fixed local definitions. There are no free theorem arguments and no algorithm, update-rule, minimizer, convexity, differentiability, feasibility, or domain-restriction premises. The variable v ranges over all real numbers and time functions are defined on all natural numbers. Some defined functions may possess further properties, but no such property is a premise or a conjunct here. The names x and y do not themselves impose an algorithmic interpretation.

T is exactly 1 in the first declaration and exactly 2 in the second. Neither theorem quantifies over arbitrary horizons or asserts a T=0 case. T-1 is respectively 0 and 1, so the variation sums are respectively empty and a singleton with t=0. The round sums are respectively the singleton {0} and the pair {0,1}. Both require the value y(T) through the last summand of B, but include loss indices only through T-1 in R and terminal G.

No ambiguous mathematical expression or inconsistent numeric conjunct was found in the exposed headers by direct arithmetic reconstruction. The first header intentionally includes the negation of a false bound with its terminal gap omitted; this is consistent with its positive D. The second explicitly distinguishes x(T) from y(T). These observations concern only the exposed statements. Because no theorem body was supplied, this report establishes no Lean elaboration, compilation, proof, general theorem, or correspondence with any external source.

Outputs were created only in the requested temporary output directory. No production, root, Tests, documentation, or RUN files were modified. The output location was described as ignored by the task; ignore status was not independently inspected, because that would exceed the two-input exposure boundary.