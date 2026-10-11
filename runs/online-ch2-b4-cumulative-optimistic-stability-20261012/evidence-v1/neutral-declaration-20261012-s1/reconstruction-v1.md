# Blind mathematical reconstruction

Declaration: `BanditRL.OnlineConvex.cumulative_optimistic_stability`.

Verified inputs:

- `declaration-v1.txt`: 1474 bytes; SHA-256 `b713181a47d73e4858a39309986bcb6ad98e4b24bea68911b0e7f24f51cfa51b`.
- `context-v1.txt`: 556 bytes; SHA-256 `bfc73f9b19e171f2e42819742a593171f0d5236b1d742b683474e94d31d93f79`.

## objects

- E is a real normed vector space. V is a convex subset of E.
- psi and hint are real-valued functions on E. loss is a sequence indexed by natural numbers, each term being a function E -> EReal. n is a natural number and lam is a nonnegative real parameter.
- p is a specified feasible minimizer of the prediction objective. g is a specified continuous real linear functional on E. q is an arbitrary specified feasible comparison point.
- Define P_n(x) := embed(psi(x)) + sum_{i=0}^{n-1} loss(i,x) + embed(hint(x)). This is the objective that p minimizes over V.
- Define G_n(x) := embed(psi(x)) + sum_{i=0}^{n} loss(i,x) + extendedIndicator(V,x). This is the function whose strong convexity is assumed and whose difference occurs in the conclusion.
- For x in V, define the finite real loss values l_i(x) := toReal(loss(i,x)), for 0 <= i <= n, and D_n(x) := l_n(x) - hint(x). The hypothesis on g is a supporting inequality for D_n on V at p.

## domains_types

- The implicit carrier binder is {E : Type*}, followed by [NormedAddCommGroup E] and [NormedSpace R E]. No finite-dimensional, Euclidean, inner-product, completeness or coordinate-equivalence assumption is present.
- Explicit binders, in declaration order, are (V : Set E), (hV : Convex R V), (psi hint : E -> R), (loss : Nat -> E -> EReal), (n : Nat), (lam : R), hbot, hdom, hlam, hstrong, (p : E), hp, hprediction, (g : E ->L[R] R), hdifference, (q : E), hq.
- i is a natural index. x,y,z,p,q are points of E. a and lam are real scalars. Every displayed norm is the given original norm on E.
- g is a continuous real-valued linear functional, not a vector in an auxiliary coordinate space. g(v) is functional application and has type R; no inner-product identification is invoked.
- P_n and G_n have codomain EReal. Strong convexity and the minimizer comparison use EReal inequalities. hdifference and the conclusion use real inequalities after toReal.
- The two local let-bindings named G, one in hstrong and one in the conclusion, have the same defining formula G_n. Neither is an additional universally quantified function.

## assumptions

- hV states that V is convex over R.
- hbot states: for every natural i, if i < n+1, then for every x in E, loss(i,x) is not bottom (negative infinity). It is global in x and includes the current index i=n, as well as all previous indices. It imposes nothing on indices greater than n.
- hdom states: for every natural i, if i < n+1, then V is a subset of effectiveDomain(loss i). By the supplied definition this means for every x in V, loss(i,x) < top (positive infinity).
- effectiveDomain as supplied excludes top but does not by itself exclude bottom. Combining hdom with hbot makes each loss(i,x) finite for all i<=n and x in V. Global finiteness outside V is not assumed.
- hlam is 0 <= lam.
- hstrong states that G_n satisfies the displayed strong-convexity interpolation inequality on V with parameter lam, for all x,y in V and all real 0<a<1. It is an assumption on the current cumulative function including loss n and the indicator, not on P_n or merely the previous prefix.
- hp is p in V, separately from hprediction. By the supplied IsMinOn definition, hprediction is: for every z in V, P_n(p) <= P_n(z). The minimized objective includes psi, losses 0 through n-1, and hint, with no explicit indicator term in its formula.
- hdifference states: for every z in V, l_n(p)-hint(p)+g(z-p) <= l_n(z)-hint(z). Thus g supports the current-loss-minus-hint difference at p on V. It is not a separately asserted derivative and is not asserted to support that function outside V.
- hq is q in V. There is no minimizing, stationarity or update-rule assumption on q.
- No differentiability, continuity or separate convexity of psi, hint, each individual loss or D_n is listed. The continuity requirement applies to g as a continuous linear functional.

## quantifiers

- The theorem is universally parameterized by all its listed data and proof arguments. For any such data satisfying the hypotheses, it yields the conclusion for the specified q in V. It does not assert existence of p or g.
- hbot order: for every i in Nat, i<n+1 -> for every x in E, loss(i,x) != bottom.
- hdom order, with subset expanded: for every i in Nat, i<n+1 -> for every x in E, x in V -> loss(i,x)<top.
- hstrong order: for every x in E, x in V -> for every y in E, y in V -> for every a in R, 0<a -> a<1 -> the interpolation inequality for G_n.
- hprediction order: for every z in E, z in V -> P_n(p)<=P_n(z). hdifference order: for every z in E, z in V -> D_n(p)+g(z-p)<=D_n(z). The same fixed g must work for all those z.
- p is supplied with feasibility and a minimizer certificate before g and its support certificate are supplied. q is then arbitrary subject only to feasibility. There is no existential choice of a fresh functional depending on z or q in hdifference.
- n is arbitrary but fixed in each instantiation. Hypotheses concern this one prefix up to n; the conclusion is not itself a sum over multiple times or a jointly specified sequence of iterates.

## operations

- embed denotes coercion R -> EReal. extendedIndicator(V,x) is 0 when x is in V and top otherwise.
- The notation sum over range n includes exactly 0,...,n-1, while range(n+1) includes exactly 0,...,n. The current cumulative objective adds loss n and drops hint relative to the minimized prediction objective, on V.
- On V all relevant losses are finite, the indicator is zero, and psi and hint are already real-valued. Consequently both P_n and G_n are finite on V, and toReal(G_n(x)) = psi(x)+sum_{i=0}^{n} l_i(x). Also toReal(P_n(x)) = psi(x)+sum_{i=0}^{n-1} l_i(x)+hint(x).
- Thus on V, toReal(G_n(x)) = toReal(P_n(x)) + D_n(x). This finite-value identity describes the relationship between the two formulas; it is not an additional assumption.
- The exact strong-convexity inequality is G_n(a*x+(1-a)*y) <= embed(a)*G_n(x)+embed(1-a)*G_n(y)-embed((lam/2)*a*(1-a)*norm_E(x-y)^2). Scalar-vector multiplication here means real scalar action.
- Convexity of V keeps a*x+(1-a)*y in V for the tested weights. Its G_n value is consequently finite as well.
- The local support displacement is z-p: D_n(p)+g(z-p)<=D_n(z). At z=q it uses g(q-p). The conclusion instead uses g(p-q); by linearity this is -g(q-p). The sign must not be interchanged without negation.
- The conclusion's exact real inequality is toReal(G_n(p))-toReal(G_n(q)) <= g(p-q)-(lam/2)*norm_E(p-q)^2.
- Equivalently, with the same premises, toReal(G_n(q)) >= toReal(G_n(p))+g(q-p)+(lam/2)*norm_E(q-p)^2. This uses g(p-q)=-g(q-p) and norm symmetry.
- The supplied toReal definition sends either infinity to zero, but the feasible endpoint values in the conclusion are finite by hbot and hdom, so this collapse of infinities plays no role there. Individual losses outside V may equal top.

## conclusion

- For every supplied feasible p minimizing P_n, every supplied continuous functional g satisfying the V-restricted support condition for D_n at p, and every feasible comparison q, the current cumulative objective difference obeys the specified linear-minus-quadratic upper bound.
- The left side compares the current objective G_n at p and q, including loss n. It does not compare P_n values, hint alone, or only the previous cumulative losses.
- The quadratic penalty uses the original norm on E and the coefficient lam/2. The linear term is g(p-q), with the direction from q to p.
- The declaration does not conclude that p minimizes G_n or that q minimizes any objective. In particular, the right side need not be nonnegative, and the type asserts no independent sign for the left side.
- It does not provide an algorithm, iterate sequence, existence or uniqueness of a minimizer, existence of a supporting g, a dual-norm bound, a displacement bound, or a multi-step regret bound.
- It does not assert global support for D_n outside V, global finite loss values, or strong convexity of each component or of the prediction objective.
- A checked inhabitant of this type would certify this conditional inequality. The supplied statement and literal definitions alone do not establish that a body exists or was accepted, reveal its dependencies, or identify its proof method.
- No source theorem, version, intended provenance, source fidelity, or interpretation based on the declaration's name is inferred.

## edge_cases

- lam=0 is allowed. The assumed interpolation property reduces to ordinary open-weight convexity of G_n on V, and the conclusion reduces to toReal(G_n(p))-toReal(G_n(q)) <= g(p-q). No positive-curvature or distance conclusion is automatic.
- n=0 is allowed. range 0 is empty, so P_0=embed(psi)+embed(hint), and p minimizes this over V. range 1 contains index 0, so G_0=embed(psi)+loss 0+indicator. hbot and hdom still constrain loss 0, and hdifference supports toReal(loss 0)-hint.
- p=q is allowed. Both objective values cancel, g(0)=0 and the norm term vanishes, so the conclusion becomes 0<=0.
- V is not explicitly assumed nonempty by a separate Nonempty binder, but hp supplies p in V, and hq supplies q in V. Thus an instance with all hypotheses cannot have V empty. There is no substantive empty-domain vacuity after p and hp are supplied.
- A singleton V is allowed. The minimizer and support comparisons then involve only its point; no nonempty-interior or distinct-point assumption occurs.
- Only weights 0<a<1 occur in hstrong; endpoint weights a=0 or a=1 are not part of that quantified hypothesis.
- Losses through index n are forbidden to be bottom everywhere, but are forbidden to be top only on V. Losses at indices greater than n are unconstrained. SourceProper is not an explicit premise; neither is a global subdifferential premise.
- g=0 is allowed if its support condition holds. In that special case the displayed inequality is a quadratic lower-growth comparison for G_n relative to p; the general declaration does not assert g=0.
- The carrier may have arbitrary dimension and the original norm need not arise from an inner product. There is no coordinate norm to substitute into the conclusion.

## Uncertainty and scope

- Evidence is restricted to the two current neutral files, with verified byte counts and SHA-256 hashes. Earlier reconstructions are not used.
- No imported module, source paper, PDF, manifest, review, contract, other workspace file or external resource was consulted. No Lean execution, proof search or proof-body inspection was performed.
- Supplied auxiliary definitions were expanded literally. Standard mathematical readings of the named normed-space structures, finite sums and real linearity are used without consulting their implementations.
- Statements about finiteness, index ranges, displacement signs and degenerate cases are semantic consequences of the displayed binders and definitions; they are not independent Lean verification or proof-route evidence.
