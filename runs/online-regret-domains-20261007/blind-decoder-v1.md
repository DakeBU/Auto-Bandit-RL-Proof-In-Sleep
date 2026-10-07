# Neutral reconstruction: context a-j and N01-N10

Actor `/root/osd_blind`; requested GPT-6 Astra / medium without escalation. Runtime model and effort are not independently attested. This is not a human/external review or an external-independence attestation.

Prior-history disclosure: this actor previously decoded the neutral 20261007 current-support, policy, absolute-loss, linearization, optimal-step, unit-scaling, foundations, sharp-prefix, and recursive-state packets. This is reused neutral context, not a history-free first exposure. For this task ONLY `online-regret-domains-20261007/blind-packet-v1.md` was read. No source identity, actual alias map, proof bodies, old verdicts, other repository material, or external source was consulted.

## Complete context a-j

**a.** For an arbitrary type X, a real-valued loss sequence ell:N->X->R, prediction sequence p:N->X, comparator u:X, and natural horizon T,
\[
a(\ell,p,u,T)=\sum_{t=0}^{T-1}\ell_t(p_t)-\sum_{t=0}^{T-1}\ell_t(u).
\]
This is a difference of two finite real sums. It is not an infimum over comparators or an absolute value. Predictions and comparators must be elements of the loss's typed domain X.

**b.** For V subset X, b(V,ell,p) is the one-sided eventual property
\[
\forall u\in V,\ \forall\varepsilon\in\mathbb R,\quad\varepsilon>0\Longrightarrow
\forall^{\mathrm{eventually}}T\in\mathbb N,\quad a(\ell,p,u,T)/T\le\varepsilon.
\]
Equivalently, for each fixed u and positive epsilon there exists N such that all natural T>=N satisfy the displayed non-strict inequality. The threshold may depend on u and epsilon. There is no uniform-in-u threshold in the written quantifier order, no lower bound, no absolute-value convergence, and no feasibility requirement p_t in V. Predictions need only belong to X, the loss domain. Real division is totalized at T=0, but eventuality can omit zero.

**c.** Given V,W subset X with hVW:V subset W, c(V,W,hVW) maps the subtype V into subtype W by keeping the underlying element and transporting its membership proof:
\[
c_{V,W}:\{x\in X:x\in V\}\longrightarrow\{x\in X:x\in W\},\qquad c_{V,W}(u).\mathrm{val}=u.\mathrm{val}.
\]
It is an inclusion, not projection, nearest-point choice, or modification of the point. No reverse map or extension outside W is defined.

**d,e.** These are real sets d=[0,1] and e=[0,2], with inclusive endpoints.

**f.** A typed loss on the larger-domain subtype: \(f:\mathbb N\to\{x\in\mathbb R:x\in[0,2]\}\to\mathbb R\), \(f_t(x)=-x.\mathrm{val}\) for every t. It is time-independent but defined on subtype e, not on an unconstrained ambient real argument by this declaration.

**g.** A constant prediction sequence of subtype e: \(g_t=\langle2,2\in e\rangle\) for every t. The underlying point 2 is allowed by the loss domain but is outside d.

**h,i.** Fixed subtype-e comparators \(h=\langle1,1\in e\rangle\), \(i=\langle0,0\in e\rangle\). Their underlying values are respectively 1 and 0.

**j.** This is a SET OF SUBTYPE-e ELEMENTS:
\[
j=\{x:\!\uparrow e\mid x.\mathrm{val}\in d\}.
\]
Thus j is not literally the original real set d, although its underlying real values are [0,1]. The type X used in b(j,f,g) is subtype e.

No topology on X, geometry, probability law, expectation, independence, filtration, learner construction, or strict-past prediction rule is supplied. Real topology is used only for the limits of scalar bound sequences in N02. Finite-horizon equalities depend on losses in their played time range; this is not a proof that arbitrary supplied predictions are causal.

Each proposition below has seven slots: objects; quantifiers; assumptions; conclusion; constants and indices; probability and information; boundary. Closed typed propositions and this reconstruction do not supply proofs.

## N01

1. **Objects.** Arbitrary type X, ell:N->X->R, p:N->X, u:X and T:N.
2. **Quantifiers.** Universal over all these objects, including every natural T.
3. **Assumptions.** None beyond the types.
4. **Conclusion.** Difference of sums equals sum of pointwise differences:
   \[\forall X,\ell,p,u,T,\quad a(\ell,p,u,T)=\sum_{t=0}^{T-1}(\ell_t(p_t)-\ell_t(u)).\]
   Both expressions compare the same predictions with the same fixed comparator.
5. **Constants and indices.** Factor 1 and zero offset; t ranges through 0,...,T-1. u is held fixed across terms.
6. **Probability and information.** Pure finite-sum algebra with real losses. No assumption about how p was obtained or which data it uses.
7. **Boundary.** T=0 gives equality of zero empty sums. No comparator subset, prediction feasibility beyond X, sign restriction, or nonnegativity of a is required.

## N02

1. **Objects.** Arbitrary X, set V subset X, real losses ell, predictions p, and real bound function B:X->N->R.
2. **Quantifiers.** For every X,V,ell,p,B, require each hypothesis separately for every u in V. The conclusion then quantifies every u in V and every real epsilon>0, with eventuality in T.
3. **Assumptions.** For every u in V, eventually \(a(\ell,p,u,T)/T\le B(u,T)\); and for every u in V,
   \[B(u,\cdot)\longrightarrow0\quad\text{as natural }T\to\infty.\]
   Neither bound hypothesis is required at every finite T or uniformly in u.
4. **Conclusion.** The one-sided eventual comparator property b follows:
   \[\forall X,V,\ell,p,B,\quad
   [(\forall u\in V,\ \forall^{\rm eventually}T,\ a(\ell,p,u,T)/T\le B(u,T))
   \land(\forall u\in V,\ B(u,T)\to0)]
   \Rightarrow\forall u\in V,\forall\varepsilon>0,\ \forall^{\rm eventually}T,\ a(\ell,p,u,T)/T\le\varepsilon.\]
5. **Constants and indices.** Limit exactly 0; denominator real-coerced T; non-strict <= in the eventual conclusion. No numerical rate or common threshold is specified.
6. **Probability and information.** Deterministic scalar convergence and eventual order comparison, not convergence in probability or an expectation. The bound may depend on u and T.
7. **Boundary.** V may be empty, yielding vacuous comparator quantifiers. No B>=0 assumption. A persistently negative average can satisfy the conclusion, so it is not two-sided convergence to zero. T=0 and finite exceptional indices do not obstruct eventuality. No requirement that p_t belong to V.

## N03

1. **Objects.** Arbitrary ambient type X, V,W subset X, inclusion c from subtype V to subtype W, losses ell:N->subtype W->R, predictions p:N->subtype W, comparator u:subtype V, T:N.
2. **Quantifiers.** Every such collection with the supplied set inclusion; prediction sequence remains in the larger typed domain W, not necessarily V.
3. **Assumptions.** V subset W only beyond the types. Comparator u already carries V-membership; p carries W-membership.
4. **Conclusion.** The mixed-domain comparison is the sum of its per-round real differences after embedding u:
   \[\forall X,V,W,\ell,p,u,T,\quad V\subseteq W\Rightarrow
   a(\ell,p,c_{V,W}(u),T)=\sum_{t=0}^{T-1}(\ell_t(p_t)-\ell_t(c_{V,W}(u))).\]
5. **Constants and indices.** Same T, same embedded comparator at every index, exact equality.
6. **Probability and information.** Type-correct evaluation: both arguments supplied to ell lie in subtype W. Inclusion does not modify the underlying comparator point or require p_t in V.
7. **Boundary.** T=0 allowed. No extension of ell to all ambient X is asserted. If V has no members there is no supplied u:subtype V; this is not an existence claim. Predicting in W outside V is allowed.

## N04

1. **Objects.** X,V,W with inclusion c; loss ell defined on subtype W; predictions p and comparator u BOTH in subtype V; natural T.
2. **Quantifiers.** All such typed objects under V subset W.
3. **Assumptions.** V subset W. Unlike N03, p has the smaller-domain type N->subtype V.
4. **Conclusion.** Restricting the larger-domain loss and evaluating smaller-domain predictions equals embedding both predictions and comparator into the larger domain:
   \[\forall X,V,W,\ell,p,u,T,\quad V\subseteq W\Rightarrow
   a((t,v)\mapsto\ell_t(c_{V,W}(v)),p,u,T)
   =a(\ell,(t\mapsto c_{V,W}(p_t)),c_{V,W}(u),T).\]
5. **Constants and indices.** No scaling or residual; identical evaluation at every t<T.
6. **Probability and information.** This is a restriction/inclusion identity, not a construction of an extension and not a projection of arbitrary larger-domain predictions.
7. **Boundary.** Does not apply to a prediction sequence lying outside V unless a distinct smaller-domain sequence is provided. T=0 valid; all subtype proof data preserve underlying values.

## N05

1. **Objects.** Fixed real sets d=[0,1], e=[0,2], and real point 2.
2. **Quantifiers.** A closed three-conjunct numerical/set statement; inclusion internally means every real member of d is in e.
3. **Assumptions.** None beyond the explicit definitions.
4. **Conclusion.** The smaller interval is included in the larger, with point 2 in the larger only:
   \[[0,1]\subseteq[0,2]\quad\land\quad2\in[0,2]\quad\land\quad2\notin[0,1].\]
5. **Constants and indices.** Inclusive endpoints 0,1,2; no time or horizon.
6. **Probability and information.** Concrete domain-separation test, not stochastic feasibility or a loss evaluation.
7. **Boundary.** Inclusion is not equality. The point 2 is a valid larger-domain value despite being outside the smaller comparator set.

## N06

1. **Objects.** Arbitrary X,W subset X; two real loss streams ell,m defined on subtype W; common p:N->subtype W, u:subtype W and T:N.
2. **Quantifiers.** All such inputs, with equality required for EVERY t<T and EVERY x:subtype W.
3. **Assumptions.** \(\forall t<T,\forall x:\!\uparrow W,\ \ell_t(x)=m_t(x)\).
4. **Conclusion.** Loss-stream agreement on the entire typed domain throughout the prefix preserves the cumulative comparison:
   \[\forall X,W,\ell,m,p,u,T,\quad
   (\forall t<T,\forall x:\!\uparrow W,\ell_t(x)=m_t(x))\Rightarrow a(\ell,p,u,T)=a(m,p,u,T).\]
5. **Constants and indices.** Time prefix exactly range T; no agreement required at T or later. Same p,u on both sides.
6. **Probability and information.** Deterministic functional equality on the stated domain, not merely scalar observations at one path. It does not assert that recomputing an unspecified algorithm under m yields the same p.
7. **Boundary.** T=0 premises vacuous and both expressions zero. No claim about losses outside W; no ambient extension is provided or needed.

## N07

1. **Objects.** X,W, typed real losses ell:N->subtype W->R, p:N->subtype W and u:subtype W.
2. **Quantifiers.** Universal over all these objects, at fixed horizon zero.
3. **Assumptions.** None beyond typing.
4. **Conclusion.** Empty-horizon comparator difference is zero:
   \[\forall X,W,\ell,p,u,\quad a(\ell,p,u,0)=0.\]
5. **Constants and indices.** Both sums range over no indices. This is a claim about a itself, not a nonzero-denominator average.
6. **Probability and information.** Empty-sum evaluation, no observations consumed or probability model.
7. **Boundary.** No boundedness or nonnegativity needed. Supplying p,u on an empty subtype is not guaranteed by this universal statement; it makes no inhabitance claim.

## N08

1. **Objects.** Fixed subtype-e loss f_t(x)=-x.val, prediction g_t=2, comparator h.val=1, horizon 2.
2. **Quantifiers.** Closed conjunction, not a universal domain result.
3. **Assumptions.** None beyond the fixed typed objects.
4. **Conclusion.** The prediction is legal in e but outside d, and its signed comparison with h is negative:
   \[(g_0).\mathrm{val}\in e\land(g_0).\mathrm{val}\notin d\land a(f,g,h,2)=-2.\]
   The played total is -4 and comparator total -2, giving -2.
5. **Constants and indices.** Membership checked explicitly at time 0; g is constant by definition. Two losses, each -2 versus -1.
6. **Probability and information.** Concrete typed larger-domain prediction and smaller-domain comparator comparison. No undefined evaluation occurs because the loss is defined on subtype e.
7. **Boundary.** Signed comparator differences need not be nonnegative. A prediction outside d is not outside the loss domain e; conflating these would misstate the example.

## N09

1. **Objects.** Same fixed f,g; subtype-e comparators i.val=0 and h.val=1; horizon 2.
2. **Quantifiers.** Closed four-conjunct example.
3. **Assumptions.** None.
4. **Conclusion.** Both comparator values belong to d, yet their comparisons differ:
   \[i.\mathrm{val}\in d\land h.\mathrm{val}\in d\land a(f,g,i,2)=-4\land a(f,g,h,2)=-2.\]
   Comparator totals are 0 for i and -2 for h, against common played total -4.
5. **Constants and indices.** Exact values -4 and -2; fixed horizon 2 and endpoints 0,1.
6. **Probability and information.** Changing only the fixed comparator changes the signed difference; no supremum, infimum, best comparator selection or randomization is part of a.
7. **Boundary.** Membership of comparators in the same set does not make their comparator regrets identical or nonnegative. This is a numerical illustration, not a universal relation for all loss streams.

## N10

1. **Objects.** Typed ambient X=subtype e, comparator set j subset X, loss f and prediction stream g.
2. **Quantifiers.** The closed target b(j,f,g) expands to EVERY u:subtype e whose underlying value lies in d, then EVERY real epsilon>0, then eventual natural T.
3. **Assumptions.** Only the conditional u in j and epsilon>0 inside that expanded property; f,g,j are fixed definitions. There is no prediction-in-j premise.
4. **Conclusion.** The one-sided eventual property holds:
   \[\forall u:\!\uparrow e,\quad u.\mathrm{val}\in[0,1]\Rightarrow
   \forall\varepsilon\in\mathbb R,\quad\varepsilon>0\Rightarrow
   \exists N\in\mathbb N,\forall T\ge N,\quad a(f,g,u,T)/T\le\varepsilon.\]
   For positive T the signed average has the explicit value u.val-2, which lies in [-2,-1]. This explains the mathematical meaning: a persistently negative average satisfies the one-sided condition.
5. **Constants and indices.** Denominator is real-coerced T; comparison uses <=epsilon, not |average|<=epsilon. For T>0, a(f,g,u,T)=T*(u.val-2).
6. **Probability and information.** Deterministic larger-domain prediction against the restricted comparator set. The target does not assert loss queries outside subtype e, any causal algorithm, or stochastic convergence. The displayed eventual quantifier is per comparator and epsilon, even though this fixed example has a stronger simple uniform behavior.
7. **Boundary.** g_t lies outside j for all t but is valid in subtype e. Negative averages do not converge to zero here, and b does not require them to. At T=0, a=0 and totalized real division gives zero; eventuality need not use that boundary. The property alone imposes neither small absolute regret nor feasible predictions within j.

## Evidence and ambiguity boundary

No ambiguity in the supplied types or definitions blocks reconstruction. In particular d and j have different types; f is typed only on the larger subtype; c is an inclusion; b is a one-sided, comparatorwise eventual property. The packet supplies closed proposition descriptions, not target proofs. This report makes no source-fidelity, source/compilation/proof acceptance, human/external review, chapter completion or Goal completion claim. Runtime settings remain unattested and prior actor history is disclosed.