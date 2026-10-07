# Neutral reconstruction of N01-N22

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, no escalation. Runtime model and effort are not independently attested. This is not human or external review.

Prior-history disclosure: this reused decoder has read earlier neutral interfaces in online-osd-public (v1/v2), online-osd-policy-public, online-guessing-osd-policy, online-guessing-public, online-linearization-public, and online-optimal-step-public, all in the 20261007 runs. It is not a first-exposure decoder. For this task ONLY `online-unit-scaling-public-20261007/blind-packet-v1.md` was inspected. No source identity, alias map, old verdict, proof body, repository search, or network material was inspected. This report reconstructs neutral statements; it supplies no fidelity or proof verdict.

## Complete notation and interpretation

N01-N02 quantify over an arbitrary additive commutative group D, independently of the Euclidean E context. Their X,L,H denote additive exponents only, not actual physical-unit types. N03-N10, N12-N20 and N22 universally quantify over E with the supplied normed additive commutative group, real inner-product, and finite-dimensional structure. N11 and N21 are scalar statements. All extra quantifiers are stated below.

K is the fixed WHOLE ambient space E, as a nonempty closed convex carrier. J is the actual nearest-point choice onto K; thus J(z)=z. The parameter k in H,Z,G,L,R is a dummy uniform-interface parameter: their recursion uses J for K, not projection onto k. Every target uses K. No covariance claim for an arbitrary constrained domain is present.

For extended-real f,
\[
Q(f)\equiv(\forall x\in E,f(x)\ne-\infty)\land(\exists x\in E,\exists r\in\mathbb R,f(x)=\operatorname{embed}(r)),
\]
\[
S(f,x)=\{g\in E:\forall y\in E,\ f(x)+\operatorname{embed}(\langle g,y-x\rangle)\le f(y)\},
\qquad B(f)\equiv Q(f)\land\forall x\in K,S(f,x)\ne\varnothing.
\]
The supports are global: every ambient comparison y is tested. Since K=E, B imposes support existence everywhere. Properness Q plus a support at x gives finite f(x); B therefore gives finiteness everywhere. Q alone permits positive infinity at other points. EReal.toReal is totalized (infinities convert to zero), so an algebraic equality of toReal sums is distinct from an actual finite-loss performance guarantee.

A policy p has inputs time t, exactly t strict-past whole loss functions, a length t+1 actual output history including the current point, and the current whole loss. It returns a vector. It is deterministic as a mathematical function, not an executable finite-query oracle. For original run (eta,f,a,p), write h_t=H(K,eta,f,a,p,t), x_t=Z(...,t), g_t=G(...,t). Then
\[
h_0=(a),\quad x_t=h_t(t),\quad g_t=p(t,f_{<t},h_t,f_t),\quad
h_{t+1}=\operatorname{snoc}(h_t,J(x_t-\eta_tg_t)).
\]
The initial argument called x1 is x_0=a; round one is Lean index zero. Current x_t exists before f_t is used for g_t and the successor. No comparator/future loss is an explicit policy input. Initial point, policy, and schedule are exogenous: their external selection is not certified independent of future information, and no stochastic law, filtration or measurability is stated.

L_T means only played legality: \(\forall t<T,g_t\in S(f_t,x_t)\). There is no universal off-path policy law assumed in the targets. Let
\[
R_T(\eta,f,a,p,u)=\sum_{t=0}^{T-1}(f_t(x_t)^{r}-f_t(u)^{r}),\qquad v^r=v.\mathrm{toReal}.
\]
For real c define
\[
F_c f(y)=f(cy),\qquad(e_c\eta)_t=\eta_t/c^2,
\]
\[
(a_cp)(t,P,h,f)=c\,p(t,(i\mapsto F_{c^{-1}}P_i),(i\mapsto ch_i),F_{c^{-1}}f).
\]
Here cy denotes scalar action. The adapted policy transforms ALL past whole functions and the current function back by c^{-1}, maps all output points back by c, and multiplies the original policy's selected vector by c. It is not an independently chosen legal policy.

For c>0 use primes for the fully transformed run
\[
\eta'=e_c\eta,\quad f'_t=F_cf_t,\quad a'=c^{-1}a,\quad p'=a_cp.
\]
Thus h'_t,x'_t,g'_t always refer to that particular corresponding run. These shorthands include all four transformations, not just scaled losses. Also U(A,B,eta)=A/(2 eta)+eta B/2 is a total real scalar function, with no inherent nonnegativity assumptions on A,B.

The seven slots below are objects/spaces; quantifiers; assumptions; conclusion (NL and LaTeX); constants/indices; operation/information; boundaries. A typed closed Prop is a statement, not its proof.

## N01

1. **Objects/spaces:** Arbitrary additive commutative group D; X,L,H in D.
2. **Quantifiers:** For every such D and every X,L,H.
3. **Assumptions:** H+(L-X)=X.
4. **Conclusion:** Solving this additive exponent equation gives \(\forall D,X,L,H,\ H+(L-X)=X\Rightarrow H=X+X-L\).
5. **Constants/indices:** X occurs twice; subtraction is group subtraction, no time index.
6. **Operation/information:** Algebraically isolate H; no norm, order, scalar rate, or algorithm.
7. **Boundaries:** No positivity or numerical interpretation required. This is not a physical-unit type system; arbitrary torsion groups are allowed by the stated type.

## N02

1. **Objects/spaces:** Arbitrary additive commutative group D; X,L in D.
2. **Quantifiers:** Every D,X,L, with no conditional premise.
3. **Assumptions:** None beyond the group structure.
4. **Conclusion:** Both additive identities hold:
   \[\forall D,X,L,\quad[X+X-(X+X-L)=L]\land[(X+X-L)+(L-X)+(L-X)=L].\]
   Complementing L relative to X+X twice restores L; the displayed combination with two L-X terms also equals L.
5. **Constants/indices:** Exactly two copies of X and two added L-X terms in the second identity.
6. **Operation/information:** Group arithmetic only; no learning rule or empirical quantities.
7. **Boundaries:** No sign constraints; no division by two or torsion-free assumption.

## N03

1. **Objects/spaces:** Every supplied finite-dimensional real inner-product E; real c; f:E->EReal.
2. **Quantifiers:** Universal E,c,f under c>0.
3. **Assumptions:** c>0 only; no Q or B.
4. **Conclusion:** Inverse precomposition undoes forward precomposition as WHOLE functions:
   \[\forall E,c,f,\quad c>0\Rightarrow F_{c^{-1}}(F_cf)=f.\]
5. **Constants/indices:** Uses c^{-1} and c, not a rescaling of function values.
6. **Operation/information:** Pointwise argument scaling cancels; applies to entire extended-real functions.
7. **Boundaries:** Zero and negative c are outside this target. Infinite function values are permitted; no finite-value conversion is needed.

## N04

1. **Objects/spaces:** Every E as above, real c, extended-real f.
2. **Quantifiers:** Every positive c and proper f.
3. **Assumptions:** c>0 and Q(f).
4. **Conclusion:** Positive argument scaling preserves properness:
   \[\forall E,c,f,\quad[c>0\land Q(f)]\Rightarrow Q(F_cf).\]
5. **Constants/indices:** No multiplicative factor on loss values; only argument c y.
6. **Operation/information:** Nonzero scaling transports the finite witness and preserves the nowhere-bottom condition.
7. **Boundaries:** Does not assert finite values everywhere or support existence. c=0 excluded because argument scaling need not reach a finite witness.

## N05

1. **Objects/spaces:** Every E, real c, f:E->EReal, points y,g in E.
2. **Quantifiers:** Every such tuple with actual g supporting f at c y.
3. **Assumptions:** c>0, Q(f), and g in S(f,c y).
4. **Conclusion:** The scaled vector supports the argument-scaled function:
   \[\forall E,c,f,y,g,\quad[c>0\land Q(f)\land g\in S(f,cy)]\Rightarrow cg\in S(F_cf,y).\]
5. **Constants/indices:** Vector multiplier c, query multiplier c, and coefficient 1 in the support inequality; not c^{-1}g.
6. **Operation/information:** Transform an actual global support; every ambient comparison remains quantified. No derivative assumption.
7. **Boundaries:** This is a one-direction membership implication, not stated whole-set equality. Properness is retained even if some algebra could use less. No finite-domain or chosen-policy restriction.

## N06

1. **Objects/spaces:** Every E, real c, extended-real f, whole-space K.
2. **Quantifiers:** All positive c and f satisfying B.
3. **Assumptions:** c>0 and B(f), i.e. proper and supported at every ambient point.
4. **Conclusion:** Full regularity survives scaling:
   \[\forall E,c,f,\quad[c>0\land B(f)]\Rightarrow B(F_cf).\]
5. **Constants/indices:** Same K=E, not a transformed constrained carrier.
6. **Operation/information:** Precompose by c and transport support existence and properness.
7. **Boundaries:** No merely feasible-subset reading of B is appropriate because K is whole space. c=0 excluded; no numerical norm bound implied.

## N07

1. **Objects/spaces:** Every E; arbitrary real c; REAL-valued f:E->R; y,g in E.
2. **Quantifiers:** Universal in c without positivity, and in f,y,g.
3. **Assumptions:** HasGradientAt f g (c y).
4. **Conclusion:** Chain rule at y with gradient c g:
   \[\forall E,c,f,y,g,\quad\operatorname{HasGradientAt}(f,g,cy)\Rightarrow\operatorname{HasGradientAt}(z\mapsto f(cz),cg,y).\]
5. **Constants/indices:** Single factor c; evaluation point c y; no time index.
6. **Operation/information:** Differentiate real scalar-function composition by linear argument scaling.
7. **Boundaries:** Includes negative c and c=0; at zero the conclusion is a constant function with zero gradient, while the original gradient-at-zero premise is still stated. Not an EReal differentiation claim.

## N08

1. **Objects/spaces:** Every E; arbitrary real c; real-valued f; y in E.
2. **Quantifiers:** All E,c,f,y satisfying differentiability at c y.
3. **Assumptions:** DifferentiableAt R f (c y).
4. **Conclusion:** The selected gradient operator obeys the exact chain rule:
   \[\forall E,c,f,y,\quad\operatorname{DifferentiableAt}(f,cy)\Rightarrow\nabla(z\mapsto f(cz))(y)=c\nabla f(cy).\]
5. **Constants/indices:** Factor c, not c^2; gradient evaluated at c y on the right.
6. **Operation/information:** Real differentiability justifies gradient identity; no policy selection involved.
7. **Boundaries:** c may be zero or negative. No differentiability conclusion for extended-real f or arbitrary nondifferentiable points is asserted.

## N09

1. **Objects/spaces:** Every E; real c,eta; x,g in E.
2. **Quantifiers:** All positive c, unrestricted real eta,x,g.
3. **Assumptions:** c>0 only.
4. **Conclusion:** Scaling an update down gives inverse-square rate adjustment and forward-scaled vector:
   \[\forall E,c,\eta,x,g,\quad c>0\Rightarrow c^{-1}(x-\eta g)=c^{-1}x-(\eta/c^2)(cg).\]
5. **Constants/indices:** eta/c^2 and c g together; exact identity.
6. **Operation/information:** Vector arithmetic on one update, not a legality/performance premise.
7. **Boundaries:** Eta=0 or negative allowed. c=0 excluded. No differentiability, support, or feasible-point assumption.

## N10

1. **Objects/spaces:** Every E; c,eta real; x,g in E.
2. **Quantifiers:** Positive c and all eta,x,g.
3. **Assumptions:** c>0 only.
4. **Conclusion:** Scaling back an unchanged-rate transformed update multiplies the original-coordinate rate by c squared:
   \[\forall E,c,\eta,x,g,\quad c>0\Rightarrow c(c^{-1}x-\eta(cg))=x-(c^2\eta)g.\]
5. **Constants/indices:** Multiplier c^2 eta, not eta/c^2.
6. **Operation/information:** Exact vector algebra, with both scaled point and scaled vector explicit.
7. **Boundaries:** Eta unrestricted in sign. No claim that arbitrary independent update rules share this identity.

## N11

1. **Objects/spaces:** Real c; schedule eta:N->R; natural t.
2. **Quantifiers:** Every c,eta,t with positive c and current eta_t.
3. **Assumptions:** c>0 and eta_t>0.
4. **Conclusion:** Rescaled current rate stays positive:
   \[\forall c,\eta,t,\quad[c>0\land\eta_t>0]\Rightarrow(e_c\eta)_t=\eta_t/c^2>0.\]
5. **Constants/indices:** Current index t only, divisor c^2.
6. **Operation/information:** Scalar schedule transformation; other rates need no condition.
7. **Boundaries:** Zero/negative current eta excluded here even though e is defined for them. No entire-prefix monotonicity or all-time positivity inferred.

## N12

1. **Objects/spaces:** Every E; c, arbitrary schedule eta, losses f, initial a, policy p, natural t; K=E.
2. **Quantifiers:** Every such tuple with c>0; primes denote the full transformation fixed in the context.
3. **Assumptions:** c>0 only, no rate positivity or loss/policy legality.
4. **Conclusion:** WHOLE actual histories scale inversely:
   \[\forall E,c,\eta,f,a,p,t,\quad c>0\Rightarrow h'_t=(i\mapsto c^{-1}h_t(i)).\]
5. **Constants/indices:** Equality of functions on Fin(t+1); includes initial and latest outputs. eta'=eta/c^2, a'=a/c, f'=F_cf, p'=a_cp.
6. **Operation/information:** The adapter restores past/current losses and all points before calling the SAME p; whole-space projection is used in both recursions.
7. **Boundaries:** t=0 compares a/c with a/c. Negative/zero rates and nonproper losses allowed. No extension to arbitrary constrained k or independently chosen policy.

## N13

1. **Objects/spaces:** Same universal E,c,eta,f,a,p,t and fully transformed pair of runs.
2. **Quantifiers:** All run inputs and natural t under c>0.
3. **Assumptions:** Positive c only.
4. **Conclusion:** Current outputs are inversely scaled:
   \[\forall E,c,\eta,f,a,p,t,\quad c>0\Rightarrow x'_t=c^{-1}x_t.\]
5. **Constants/indices:** Same time t, and all four run transformations as defined; no extra error term.
6. **Operation/information:** Read the last entries of the actual paired histories.
7. **Boundaries:** No positive-rate or finite-loss requirement; t=0 included. This does not compare runs with unrelated p or arbitrary domains.

## N14

1. **Objects/spaces:** Universal E,c,eta,f,a,p,t; actual selections in the paired runs.
2. **Quantifiers:** All such inputs with c>0.
3. **Assumptions:** Only c>0.
4. **Conclusion:** Actual selected vectors scale forward:
   \[\forall E,c,\eta,f,a,p,t,\quad c>0\Rightarrow g'_t=cg_t.\]
5. **Constants/indices:** Same current index t; multiplier c, not inverse c.
6. **Operation/information:** Exact adapted-policy identity with restored whole past/current losses and points. It holds whether the vector is a valid support or not.
7. **Boundaries:** No support legality or differentiability assumed. Positive c restriction retained; independent policy tie choices need not satisfy this identity.

## N15

1. **Objects/spaces:** Every E,c,eta,f,a,p and natural T; paired runs in K.
2. **Quantifiers:** All run inputs with positive c and the stated ORIGINAL played-prefix assumptions.
3. **Assumptions:** c>0, \(\forall t<T,Q(f_t)\), and L_T for the original run.
4. **Conclusion:** Played legality transports to the adapted run:
   \[\forall E,c,\eta,f,a,p,T,\quad[c>0\land(\forall t<T,Q(f_t))\land L_T(\eta,f,a,p)]\Rightarrow L_T(e_c\eta,F_cf,c^{-1}a,a_cp).\]
5. **Constants/indices:** Same prefix 0,...,T-1. No requirement that every loss is B or regular beyond that prefix.
6. **Operation/information:** Transport actual supports via N05 with actual scaled points/selections; no universal off-path policy law.
7. **Boundaries:** T=0 vacuous; rates unrestricted. Properness and played legality establish played finiteness, but do not by themselves certify arbitrary comparator finiteness.

## N16

1. **Objects/spaces:** Every E,c,eta,f,a,p,t; two actual current extended-real evaluations.
2. **Quantifiers:** All inputs under c>0.
3. **Assumptions:** Positive c only.
4. **Conclusion:** Current LOSS VALUES agree exactly:
   \[\forall E,c,\eta,f,a,p,t,\quad c>0\Rightarrow (F_cf_t)(x'_t)=f_t(x_t).\]
5. **Constants/indices:** No multiplication of loss values by c; both use time t.
6. **Operation/information:** Argument rescaling cancels output rescaling in an EReal equality.
7. **Boundaries:** May include infinite values; no properness or finiteness asserted. This identity is not itself a finite real-loss inequality.

## N17

1. **Objects/spaces:** Every E,c,eta,f,a,p,u and natural T; comparator u scaled to u/c.
2. **Quantifiers:** All run inputs and ambient comparators under c>0.
3. **Assumptions:** Only c>0; no Q, B, legality or rate positivity.
4. **Conclusion:** The algebraic totalized real sum is invariant:
   \[\forall E,c,\eta,f,a,p,u,T,\quad c>0\Rightarrow R_T(e_c\eta,F_cf,c^{-1}a,a_cp,c^{-1}u)=R_T(\eta,f,a,p,u).\]
5. **Constants/indices:** Same T, same summand indices; comparator transforms as u/c. Exact equality.
6. **Operation/information:** Matching played and comparator EReal values yield matching toReal differences; p still takes no comparator input.
7. **Boundaries:** T=0 both sums zero. With infinite losses this is an algebraic identity of totalized sums, not necessarily meaningful finite-loss regret. No arbitrary-domain or independent-policy invariance claimed.

## N18

1. **Objects/spaces:** Every E,c,eta,f,a,p,t; an alternative pair of actual runs.
2. **Quantifiers:** All such inputs under c>0.
3. **Assumptions:** Positive c only; eta unrestricted.
4. **Conclusion:** Keeping eta unchanged in scaled coordinates corresponds to multiplying the original-coordinate schedule by c squared:
   \[\forall E,c,\eta,f,a,p,t,\quad c>0\Rightarrow
   c\,Z(K,\eta,F_cf,c^{-1}a,a_cp,t)=Z(K,(s\mapsto c^2\eta_s),f,a,p,t).\]
5. **Constants/indices:** LEFT schedule is eta, not e_c eta; RIGHT schedule is c^2 eta. Both outputs evaluated at t.
6. **Operation/information:** Exact conjugacy under the adapter; it is different from the compensated-rate pair used for primes.
7. **Boundaries:** Includes t=0 and zero/negative rates. Does not claim scaled losses with an unchanged numerical rate reproduce the original eta trajectory after scaling back; the right schedule is explicitly different.

## N19

1. **Objects/spaces:** Every E; c real; arbitrary points x,u in E.
2. **Quantifiers:** All c,x,u with c>0.
3. **Assumptions:** c>0 only.
4. **Conclusion:** Squared distances scale inversely by c squared:
   \[\forall E,c,x,u,\quad c>0\Rightarrow\|c^{-1}x-c^{-1}u\|^2=\|x-u\|^2/c^2.\]
5. **Constants/indices:** Norm squared and inverse-square factor; no horizon.
6. **Operation/information:** Scalar homogeneity of the norm; no policy or loss inputs.
7. **Boundaries:** Includes x=u and zero vectors; c=0 excluded. No physical-unit typing or domain diameter assumption.

## N20

1. **Objects/spaces:** Every E,c,eta,f,a,p and natural T; actual selected vectors of the compensated pair.
2. **Quantifiers:** All such inputs under c>0.
3. **Assumptions:** c>0 only; no legality, norm bound or finiteness of losses.
4. **Conclusion:** The finite squared-vector sum scales by c squared:
   \[\forall E,c,\eta,f,a,p,T,\quad c>0\Rightarrow\sum_{t=0}^{T-1}\|g'_t\|^2=c^2\sum_{t=0}^{T-1}\|g_t\|^2.\]
5. **Constants/indices:** Same T terms; primes use e_c eta and a_c p, not a different run. Exact multiplicative c^2.
6. **Operation/information:** Norm scaling of the actual vectors, not an independently imposed gradient bound.
7. **Boundaries:** T=0 gives zero=zero. Zero/negative schedules permitted. No claim about unrelated policies or selections from other trajectories.

## N21

1. **Objects/spaces:** Real c,A,B,eta; scalar total function U.
2. **Quantifiers:** Every c,A,B,eta under positive c and eta; A,B arbitrary reals.
3. **Assumptions:** c>0 and eta>0, NO nonnegativity hypothesis on A or B.
4. **Conclusion:** Joint inverse/forward-square scaling leaves this scalar expression unchanged:
   \[\forall c,A,B,\eta\in\mathbb R,\quad[c>0\land\eta>0]\Rightarrow
   U(A/c^2,c^2B,\eta/c^2)=U(A,B,\eta).\]
5. **Constants/indices:** U=A/(2 eta)+eta B/2; both halves and all c^2 factors preserved.
6. **Operation/information:** Exact scalar substitution with A,B fixed across the comparison; not minimization, data-dependent optimization, or performance by itself.
7. **Boundaries:** A or B may be zero/negative. Eta=0 excluded by the target although U is total. No square roots, stochastic quantities, or physical-unit type structure are present.

## N22

1. **Objects/spaces:** Every E; real c,eta; arbitrary losses f, initial a, policy p, comparator u in E, natural T; K whole space.
2. **Quantifiers:** All such objects, with c,eta positive and original prefix assumptions, then any ambient comparator u. The transformed run is specifically compensated and adapted; the RHS refers to the SAME corresponding original constant-rate run.
3. **Assumptions:** c>0, eta>0, \(\forall t<T,B(f_t)\), and original played legality \(L_T((s\mapsto\eta),f,a,p)\). No bounded domain, uniform support-norm bound or off-path policy law. Since B gives global support existence and properness, losses at all original played points and u are finite; scaling also gives finite transformed values.
4. **Conclusion:** The scaled run's regret at u/c obeys the ORIGINAL-coordinate fixed-rate bound with a negative terminal residual:
   \[\forall E,c,\eta,f,a,p,T,u,\quad
   [c>0\land\eta>0\land(\forall t<T,B(f_t))\land L_T((s\mapsto\eta),f,a,p)]\Longrightarrow
   R_T(e_c(s\mapsto\eta),F_cf,c^{-1}a,a_cp,c^{-1}u)
   \le\frac{\|a-u\|^2}{2\eta}+\frac\eta2\sum_{t=0}^{T-1}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta},
   \]
   where x,g on the RHS are from (K,constant eta,f,a,p).
5. **Constants/indices:** Scaled constant rate eta/c^2 on the left; original eta in every right coefficient. Exact halves, factor 1, negative terminal term. T played indices end at T-1; x_T is the post-update endpoint.
6. **Operation/information:** This is a finite-loss performance inequality, not merely the algebraic R identity. Actual chosen supports and paired histories are retained. The comparator affects only evaluation and the bound, not the policy's explicit inputs.
7. **Boundaries:** T=0 allowed: assumptions on losses/legality vacuous, both regrets zero and initial/terminal terms cancel. Initial a and u need no separate feasibility because K=E. No extension to arbitrary bounded/constrained domains, independent scaled policies, zero eta or zero c. The bound need not be a uniform rate without further norm assumptions; no probabilistic or anytime guarantee is asserted.

## Evidence boundary

All N01-N22 are reconstructed as closed universally quantified descriptions, with assumptions retained even where a stronger algebraic extension might be possible. Their typing and this decoding are not theorem proofs or source acceptance. No semantic ambiguity in the packet blocks decoding; runtime model/effort and executable realizations remain unspecified/unverified. Earlier neutral context is disclosed. No source-fidelity, proof/review acceptance, human/external independence, chapter completion, or Goal completion is claimed.