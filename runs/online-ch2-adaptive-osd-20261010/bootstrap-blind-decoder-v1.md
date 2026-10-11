# Bootstrap neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no runtime model/effort attestation. This is a reused staged actor with related context history, not an absolutely blind, human or external review. The prior algorithm reconstruction (SHA256 07c34e00be6567973944e6185f6e777ae0914b477ef0c5a1d3420322343e2138) supplies the previously read Domain, support and properness interpretations. It was not reread here. Its disclosed incidental adjacent proof-line exposure remains a history limitation. This turn reads the neutral packet and narrow shared definitions of OracleLaw, canonicalPolicy and currentSubgradient; neighboring definition lines were also displayed, but no theorem proof was sought or assessed. No source correspondence or compilation is assessed.

## Shared objects and precise notation

In every statement, E : Type* has NormedAddCommGroup E, InnerProductSpace ℝ E and FiniteDimensional ℝ E. V is a Domain, whose carrier K is nonempty, closed and convex. P_K denotes its fixed projection. All statements universally quantify V, α,D:ℝ and f:ℕ→E→EReal in that order. Unless stated otherwise, next quantify x₁:E and p:SupportPolicy. The notation below always retains those identical run arguments.

The eight definitions in the packet are:
\[
A_0=((i\mapsto x_1),0),\quad H_t=(A_t).1,\quad Q_t=(A_t).2,\quad X_t=H_t(t),
\]
\[
G_t=p(t,(f_i)_{i<t},H_t,f_t),\qquad R_t=\frac{\alpha D}{\sqrt{Q_t+\|G_t\|^2}},
\]
\[
A_{t+1}=\left(\operatorname{snoc}\left(H_t,
 \begin{cases}X_t&G_t=0,\\P_K(X_t-R_tG_t)&G_t\ne0,\end{cases}\right),
 Q_t+\|G_t\|^2\right),
\]
\[
L_T\iff\forall t<T,\ G_t\in\partial f_t(X_t),\qquad
F(u,T)=\sum_{t=0}^{T-1}(\operatorname{toReal}f_t(X_t)-\operatorname{toReal}f_t(u)).
\]
Here H_t has domain Fin(t+1). The policy receives strict-past full loss functions, the entire actual action history including X_t, and current full f_t. Q_t precedes current feedback; its inclusive version is used in R_t. The zero-gradient branch skips projection.

The shared support definition is global:
\[
\partial f(x)=\{g:\forall y\in E,\ f(x)+\langle g,y-x\rangle\le f(y)\}.
\]
SubdifferentiableOn V f means (∀y, f(y)≠−∞), existence of at least one real-valued point anywhere, and ∀x∈K, ∂f(x) is nonempty. It does not require the algorithm's arbitrary p to select from that set. Global support and properness supply the finite-value meaning used below.

The newly read shared law is exactly
\[
\operatorname{OracleLaw}(V,p)\iff
\forall t\ \forall past:\operatorname{Fin}t\to(E\to\overline{\mathbb R})\
\forall h:\operatorname{Fin}(t+1)\to E\ \forall f:E\to\overline{\mathbb R},
\]
\[
\operatorname{SubdifferentiableOn}(V,f)\Rightarrow
h(t)\in K\Rightarrow p(t,past,h,f)\in\partial f(h(t)).
\]
It does not require earlier history entries to be feasible, past losses to be regular, or h to be a generated history. The canonical policy ignores past losses and all history entries except the last:
\[
p_{\rm can}(t,past,h,f)=\operatorname{currentSubgradient}(f,h(t)).
\]
The actual currentSubgradient definition chooses an element of ∂f(x) by Classical.choose when that set is nonempty, and otherwise returns zero. It is not a gradient, a minimum-norm selector, a unique-support assumption, or a sampler.

## certificate_1

1. Objects: the same actual A/Q/G run; energy and feedback are real/vector valued.
2. Quantifiers: ∀V,α,D,f,x₁,p, then ∀t:ℕ.
3. Assumptions: only the generic context and Domain structure; no legality, feasibility or scalar signs.
4. Conclusion: the energy after one more update equals its previous value plus the squared norm of the actual selected vector:
\[
Q_{t+1}=Q_t+\|G_t\|^2.
\]
5. Indices/constants: t is zero-based; feedback t first appears in Q_{t+1}; coefficient of the squared norm is one.
6. Information: G_t uses this run's actual history, not a separately supplied support sequence; legality is not claimed.
7. Boundary/evidence: at t=0, Q_0=0. G_t=0 leaves energy unchanged. Header only, no proof body.

## certificate_2

1. Objects: actual action X, selected vector G and inclusive-energy step R.
2. Quantifiers: ∀V,α,D,f,x₁,p,t.
3. Assumptions: none beyond the shared context; α,D may have any sign and x₁ may be infeasible.
4. Conclusion: the complete output recursion is
\[
X_{t+1}=\begin{cases}
X_t,&G_t=0,\\
P_K(X_t-R_tG_t),&G_t\ne0.
\end{cases}
\]
5. Indices/constants: R_t=αD/√(Q_t+‖G_t‖²), and the result is the next action.
6. Information: current action precedes current feedback; inclusive energy and step are computed before the next action. The skip branch performs no projection.
7. Boundary/evidence: total division handles zero denominator; if the current vector is zero an infeasible point may be retained. No universal projected-update formula without the branch is asserted. Header only.

## certificate_3

1. Objects: same-run cumulative energy and the sequence of actual G_t.
2. Quantifiers: ∀V,α,D,f,x₁,p, then ∀T:ℕ.
3. Assumptions: no sign, legality, support, or feasibility assumptions.
4. Conclusion:
\[
Q_T=\sum_{t=0}^{T-1}\|G_t\|^2.
\]
In words, accumulated energy is exactly the squared-norm sum along this trajectory.
5. Indices/constants: range T means 0≤t<T, excluding current index T; no averaging or square root appears.
6. Information: the sum is generated by the same p and same recursive history, even when p is not legal.
7. Boundary/evidence: at T=0 both sides are zero; vanishing total energy is compatible with a fully zero selected prefix, not a statement about all possible feedback. Header only.

## certificate_4

1. Objects: every coordinate of the generated finite history H_t.
2. Quantifiers: ∀V,α,D,f,x₁,p, then a premise hx₁:x₁∈K, then ∀t:ℕ and ∀i:Fin(t+1).
3. Assumptions: initial feasibility is the sole extra premise; no loss regularity, support legality, or restrictions on α,D.
4. Conclusion:
\[
H_t(i)\in K.
\]
Every stored action is feasible.
5. Indices/constants: i includes both the initial entry 0 and last entry t; the history has t+1 entries.
6. Information: feasibility concerns the actual history, not arbitrary policy inputs. Zero-skip and projection are the specified dynamics.
7. Boundary/evidence: at t=0 only the initial entry occurs; αD=0 and negative αD remain covered. The type asserts feasibility without a step-positivity condition. Header only.

## certificate_5

1. Objects: actual current output X_t.
2. Quantifiers: ∀V,α,D,f,x₁,p, hx₁:x₁∈K, then ∀t:ℕ.
3. Assumptions: only initial feasibility beyond common structure.
4. Conclusion:
\[
X_t\in K.
\]
5. Indices/constants: this is the last entry of H_t, including X_0=x₁.
6. Information: same generated run; no off-path feasibility is claimed.
7. Boundary/evidence: valid in the proposed type for arbitrary scalar signs and zero step/energy cases. It does not assert the initial point is feasible without hx₁. Header only.

## certificate_6

1. Objects: real energy Q_T.
2. Quantifiers: ∀V,α,D,f,x₁,p,T:ℕ, with the earlier variables having the shared types.
3. Assumptions: no extra assumptions.
4. Conclusion:
\[
0\le Q_T.
\]
5. Indices/constants: nonnegative, not strictly positive; covers every finite horizon.
6. Information: actual feedback need not be a subgradient, because the asserted quantity is built from squared norms.
7. Boundary/evidence: Q_0=0 and all-zero prefixes are admitted; no upper bound or rate is claimed. Header only.

## certificate_7

1. Objects: actual step R_t and next accumulated energy Q_{t+1}.
2. Quantifiers: ∀V,α,D,f,x₁,p,t.
3. Assumptions: no positivity, feasibility or legality premises.
4. Conclusion:
\[
R_t=\frac{\alpha D}{\sqrt{Q_{t+1}}}.
\]
This rewrites the step using the inclusive energy state.
5. Indices/constants: the denominator uses t+1, not t. No maximum, regularization constant or positive offset is introduced.
6. Information: Q_{t+1} already includes the current G_t; this identity does not make R_t independent of current loss.
7. Boundary/evidence: if Q_{t+1}=0, total real division gives R_t=0. No positive-step claim follows without additional signs/nonzero conditions. Header only.

## certificate_8

1. Objects: the current EReal loss at actual action X_t and at a feasible fixed point u, with real-part embeddings.
2. Quantifiers: ∀V,α,D,f,x₁,p; assume hx₁:x₁∈K; ∀t:ℕ; assume SubdifferentiableOn V f_t; ∀u:E; assume hu:u∈K.
3. Assumptions: initial and comparator feasibility and regularity of this one current loss. No regularity of earlier losses, no L_T, and no requirement that p be legal are included.
4. Complete two-part conclusion:
\[
f_t(X_t)=\bigl(\operatorname{toReal}f_t(X_t):\overline{\mathbb R}\bigr)
\quad\land\quad
f_t(u)=\bigl(\operatorname{toReal}f_t(u):\overline{\mathbb R}\bigr).
\]
Both actual EReal values equal embedded finite real values. This is stronger than merely forming a toReal expression.
5. Indices/constants: same t in both conjuncts; no horizon or sum; real embeddings are essential to the equalities.
6. Information: arbitrary prior losses still generate the feasible action through this fixed recursion. The support existence premise at feasible points is separate from actual selected support legality.
7. Boundary/evidence: t=0 is included; α,D unrestricted. Top values outside K are not excluded; properness excludes bottom globally. Neither differentiability nor global finite-valuedness is asserted. Header only.

## certificate_9

1. Objects: an arbitrary fixed policy p satisfying the shared universal OracleLaw, and its actual run.
2. Quantifiers: ∀V,α,D,f,x₁,p; hx₁:x₁∈K; ∀T:ℕ; hp:OracleLaw V p; hloss:∀t<T, SubdifferentiableOn V f_t.
3. Assumptions: initial feasibility, the above all-input OracleLaw, and current-loss regularity throughout the finite played prefix. No scalar signs, diameter bound or comparator.
4. Complete conclusion:
\[
L_T,\quad\text{i.e.}\quad
\forall t<T,\ G_t\in\partial f_t(X_t).
\]
The universal policy condition is a sufficient hypothesis for actual-prefix legality, not an equivalence.
5. Indices/constants: exactly 0,…,T−1; no guarantee for losses at T or later without corresponding assumptions.
6. Information: OracleLaw quantifies independently over all times, past-loss tuples, histories and current functions; only their last point's feasibility and current function regularity trigger legality. This is stronger than demanding legality solely on this generated history.
7. Boundary/evidence: T=0 makes the conclusion and prefix regularity vacuous, while hp and hx₁ remain hypotheses of this header. Zero/negative α,D remain allowed. No existence of such a policy is the conclusion here. Header only.

## certificate_10

1. Objects: the actual run with p fixed specifically to the shared canonicalPolicy, not an arbitrary legal policy.
2. Quantifiers: ∀V,α,D,f,x₁; hx₁:x₁∈K; ∀T:ℕ; hloss:∀t<T, SubdifferentiableOn V f_t. There is no p binder.
3. Assumptions: initial feasibility and finite-prefix regularity; no explicit OracleLaw premise and no scalar sign restrictions.
4. Complete conclusion:
\[
L(V,\alpha,D,f,x_1,p_{\rm can},T),
\]
equivalently, for every t<T, the vector chosen by p_can from its own actual current action and f_t lies in ∂f_t(X_t) on this same canonical run.
5. Indices/constants: prefix length T, zero-based times; all histories and energies in this L use p_can. There is no comparison with another run.
6. Information: p_can is concretely currentSubgradient of the current full function at the last action; it discards the past tuple and other history coordinates. currentSubgradient makes a classical choice from the global support set when nonempty, else returns zero. No computational selector implementation or unique value is promised.
7. Boundary/evidence: T=0 is included; the selector's empty-support fallback is part of its total definition but is not a legal-support claim outside these premises. The conclusion is not that every arbitrary policy is legal. Header only, with no supplied theorem proof.

## Scope and remaining ambiguity

All ten declarations are proposed headers with no theorem bodies. The preceding eight recursive definitions are actual supplied context, not evidence that these ten declarations have been proved or compiled. None is a regret bound, asymptotic result, policy optimizer, or probabilistic statement.

The fixed parameters V,α,D,x₁,p have no restrictions on their origin. Comparisons about information dependence require holding those parameters fixed; nothing here licenses a future-independent interpretation of a family that reselects them using the loss stream. Current full losses are visible to p after the current action exists. E may be zero dimensional; no nontriviality assumption occurs.

No unresolved mathematical context ambiguity remains after the limited canonical-policy and OracleLaw definition reads. The receipt binds only files actually read this turn and explicitly records reuse of prior context rather than claiming fresh API inspection.
