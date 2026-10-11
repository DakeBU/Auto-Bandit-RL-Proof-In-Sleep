# Neutral prefix-state reconstruction

Actor: /root/osd_blind. Requested GPT-6 Astra / medium; runtime model and effort are not attested. This actor has reused related staged decoder history, including the same eight definitions. This is source-withheld statement reconstruction, not absolute blindness, human/external review, source fidelity, compilation or proof acceptance.

The only file read in this turn is the algorithm-prefix neutral packet. Its raw SHA256 is 3d1ebbea726c0c5b99695c62702e0740ba3ad4e3d489b96fa1b708c828fb9400. Prior shared-API interpretation is reused explicitly from the previously produced algorithm-blind-decoder-v1.md, SHA256 07c34e00be6567973944e6185f6e777ae0914b477ef0c5a1d3420322343e2138; that report and those APIs were not reread in this turn. The prior report's disclosure about an incidental adjacent proof line remains part of this actor's history.

## Context and actual state

The packet repeats complete definitions A,H,Q,X,G,R,L,F. With fixed V,α,D,x₁,p, write A_t(f)=(h_t,q_t). The state has type
\[
(\operatorname{Fin}(t+1)\to E)\times\mathbb R.
\]
Initially h_0 is the one-entry history x₁ and q_0=0. Given state (h_s,q_s), the recursion forms
\[
g_s=p\bigl(s,(f_i)_{i<s},h_s,f_s\bigr),\qquad
S_s=q_s+\|g_s\|^2,
\]
and appends h_s(s) when g_s=0, otherwise appends
\[
P_V\left(h_s(s)-\frac{\alpha D}{\sqrt{S_s}}g_s\right).
\]
The new energy is S_s. H and Q are the state projections; X is the last history entry; G is this actual policy output; R is the inclusive-energy step size; L is actual played-prefix support legality; F is the same-run sum of real-part loss differences against a fixed comparator. L and F do not occur in the new proposition.

## certificate_three — seven semantic slots

1. **Objects/model.** E is an arbitrary type with NormedAddCommGroup E, InnerProductSpace ℝ E and FiniteDimensional ℝ E. V is a Domain on this E, hence the previously interpreted nonempty closed convex feasible set with its fixed projection. α,D are real numbers. f,f′ are two functions ℕ→E→EReal. The common x₁ belongs to E, and the common p has the SupportPolicy type: at each natural s it receives the finite strict-past tuple of full loss functions, an action history of length s+1 and the current full loss function, and returns a vector in E. t is a natural number.

2. **Quantifiers and order.** After the generic type and typeclass context, quantify in the exact header order over V, α, D, f, f′, x₁, p, t, then assume hloss. In ordinary logical notation the full proposition is
\[
\forall V\ \forall\alpha,D\in\mathbb R\
\forall f,f':\mathbb N\to(E\to\overline{\mathbb R})\
\forall x_1\in E\ \forall p:\mathrm{SupportPolicy}\ \forall t\in\mathbb N,
\quad
\left(\forall s\in\mathbb N,\ s<t\Rightarrow f_s=f'_s\right)
\Rightarrow
A(V,\alpha,D,f,x_1,p,t)=A(V,\alpha,D,f',x_1,p,t).
\]
There is one universally quantified p, not two policies related by a hypothesis.

3. **Assumptions.** The sole extra premise is equality of the loss functions at every time s<t. This is equality in E→EReal, equivalently f_s(y)=f′_s(y) for every ambient y∈E. Equality only at the played points, or only on V, is not the supplied assumption. There is no hypothesis of legal subgradients, SubdifferentiableOn, initial feasibility, positive α, nonnegative D, diameter bound, finite-valued losses, or positive horizon. Common V,α,D,x₁,p are enforced by using identical arguments in the conclusion, not by comparing independently selected parameters.

4. **Complete conclusion in natural language and formula.** For any two loss streams whose full loss functions agree strictly before time t, the two runs with identical remaining parameters have exactly the same complete length-(t+1) action history and the same accumulated energy at time t:
\[
(h_t(f),q_t(f))=(h_t(f'),q_t(f')).
\]
In particular, unpacking the product/function equality gives equality of history entries at every i:Fin(t+1) and equality of the real energy. The conclusion is stronger than equality of only the last action X_t. It is not an asserted equality of entire infinite trajectories.

5. **Constants, normalization and indices.** There are no new numerical constants or bounds. The matched losses are indexed 0,…,t−1, while the matched history contains actions 0,…,t; q_t contains accumulated energy from those t transitions. The real division and square root in the definition remain total operations: their zero cases are not removed by hidden conditions. The proposition compares exact states, not normalized regrets or distances.

6. **Algorithm/information and probability.** X_s is present before processing current f_s; p then reads strict-past full losses, actual history and f_s, and the update creates X_{s+1}. Thus the state after t transitions is compared under equality of precisely the loss functions consumed during those transitions. No agreement at t or later is assumed. Consequently this proposition does not assert equality of G_t, R_t or A_{t+1} without further agreement on the current loss. No probability, independent seed, measurability or stochastic averaging is involved. The fixed p is an ordinary mathematical function. Its interface does not restrict information encoded when p or the external parameters were chosen. A family that reselects p,V,α,D or x₁ from the full stream is outside the comparison unless those selected arguments coincide. The header offers no guarantee for different policies, even if they both satisfy support legality.

7. **Boundaries and evidence.** At t=0 the prefix premise is vacuous, and both sides are the same initialized singleton history and zero energy for arbitrary streams. α=0, D=0, negative α or D, and zero cumulative energy remain admitted; no cancellation or positive denominator is required by the statement. Zero selected feedback follows the same skip branch in matched runs. The initial point may lie outside V. E may have dimension zero: no nontriviality instance is required. Losses may take infinite extended values; toReal is not used in this conclusion. The packet supplies a theorem header with no theorem body. The recursion definitions are supplied; neither a proof of this target nor a compiler result is supplied or claimed here.

## Ambiguities and limits

No unresolved semantic or type-context ambiguity was found using the explicit same-context reference. This is a proposed exact prefix-state equality, not a proof or a source correspondence verdict. It supplies no support-policy existence assertion, no legality theorem, no performance bound, and no causality guarantee across changes to the external parameters.
