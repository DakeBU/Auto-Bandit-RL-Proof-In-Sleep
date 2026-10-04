# V3 source-blind reconstruction of F01–F18

## Evidence boundary

This report covers all 18 headers of `blind-packet-v3.md`, read directly for this reconstruction. No other source, proof, context, report, or verdict files were read for this v3 pass. No source identity is inferred. The decoder is a distinct automated actor, not a human or external-model reviewer. The packet supplies unproved mathematical headers; this report makes no compilation, proof-validation, or source-acceptance claim. Earlier diagnostic artifacts have not been edited or used as file inputs.

Independent raw-byte SHA-256 of this input packet:
`964805de5c70073daab3df66cd0ba003b8acd832708a7d7bb6388e11aee49bb1`.

## Mathematical definitions used throughout

All declarations have an ambient finite-dimensional real inner-product space E and its normed additive commutative group structure. The packet's Domain alias refers to AmbientDomain with this E. A domain supplies a carrier C⊆E together with nonemptiness, closedness, and convexity. It does not supply boundedness. No positive dimension is assumed. Each statement below retains these ambient binders even if its formula could make sense more generally.

For f:E→EReal, properness means

\[
(\forall z\in E,\ f(z)\ne-\infty)\ \land\
(\exists z\in E\ \exists r\in\mathbb R,\ f(z)=\iota(r)).
\]

The finite witness need not lie in C. Write

\[
S_f(x)=\{g\in E:\forall y\in E,\ f(x)+\iota(\langle g,y-x\rangle)\le f(y)\}.
\]

This is an all-query support condition, not an inequality restricted to feasible queries. Regularity means properness together with S_f(x) nonempty at every x∈C. No explicit global convexity assumption on f is included. Properness and a supporting vector at a point x force f(x) to be finite: properness rules out −∞, and testing support against the finite witness rules out +∞. Hence regularity gives finite values throughout C. In the headers toReal is the EReal-to-real conversion; its implementation is not reproduced in this packet. A converted real number alone does not certify the original extended-real value was finite. F13 explicitly supplies equality to a finite-real embedding, while other regularity/support premises supply the corresponding finite-value interpretation mathematically.

A linear policy A is an arbitrary family A_t:E^t→E, where E^t denotes functions on indices 0,…,t−1. The adjective linear does not require A_t itself to be linear. Universal feasibility is ∀t∀h∈E^t, A_t(h)∈C, including histories never played. A support policy p_t receives t whole past loss functions, t+1 output vectors, and the current whole loss function. It returns one vector. It has no explicit future-loss input, comparator input, or randomness input.

The universal Law(C,p) states, for every time t, every past-loss tuple b, every output tuple h, and every current f:

\[
\operatorname{Regular}_C(f)\land h_t\in C
\ \Longrightarrow\ p_t(b,h,f)\in S_f(h_t).
\]

There is no requirement that b or h arose on a generated run, nor that earlier entries of h are feasible. Default uses c(f,x), chosen classically from S_f(x) if nonempty and zero otherwise, by pᵈ_t(b,h,f)=c(f,h_t). It ignores b and earlier output coordinates. Classical choice is not a computational procedure or a uniqueness claim.

For h∈E^t define Q_A(h)∈E^{t+1} by

\[
Q_A(h)_i=A_i((h_j)_{j<i}),\qquad 0\le i\le t.
\]

For a fixed A, full loss sequence f, and fixed support policy p, the actual run is

\[
H_0=(),\quad x_t=A_t(H_t),\quad
 g_t=p_t((f_s)_{s<t},Q_A(H_t),f_t),\quad
 H_{t+1}=H_t\mathbin{\|}(g_t).
\]

Thus H_t contains selected vectors, not output vectors. The current vector g_t is appended after the current play x_t. The initial play is A₀(()) and is shared when A is held fixed; no separate initialization parameter exists. Actual legality L_T is only ∀t<T, g_t∈S_{f_t}(x_t). It constrains this played trajectory, not all histories.

For any vector sequence v:ℕ→E, define y_t^v=A_t((v_s)_{s<t}) and ℓ_t^v(z)=⟨v_t,z⟩. For real losses ℓ and predictions y define

\[
\mathcal C_T(\ell,y,u)=\sum_{t=0}^{T-1}\ell_t(y_t)-\sum_{t=0}^{T-1}\ell_t(u).
\]

This comparator expression does not minimize over u. The original regret is

\[
R_T(u;A,f,p)=\sum_{t=0}^{T-1}\big(\operatorname{toReal}f_t(x_t)-\operatorname{toReal}f_t(u)\big).
\]

All following statements are deterministic. No probability, expectation, filtration, independence, or high-probability qualification occurs. The same-run qualification means x,g,H use the identical A,f,p parameters, not a separately chosen trajectory. Every seven-slot reconstruction below uses exactly these definitions.

## F01

1. **Objects/spaces:** A_t:E^t→E, arbitrary h∈E^t, and reconstructed tuple Q_A(h).
2. **Quantifiers/order:** Every A, every t∈ℕ, and every h of the prescribed length.
3. **Assumptions:** Shared ambient structure only; no feasibility or legality.
4. **Exact conclusion:** Q_A(h)_t=A_t(h).
5. **Constants:** Last coordinate t in a tuple of length t+1, from an input of length t.
6. **Probability/information:** Deterministic; the output uses only the t supplied past vectors.
7. **Boundary/excluded regimes:** Includes t=0 and arbitrary off-trajectory histories. At zero this is the initial play, not necessarily the zero vector.

## F02

1. **Objects/spaces:** A,f,p and actual initial vector history H₀:Fin 0→E.
2. **Quantifiers/order:** Every such A,f,p.
3. **Assumptions:** No additional hypotheses.
4. **Exact conclusion:** H₀ equals the unique empty function Fin.elim0.
5. **Constants:** Zero vector-history length at time zero.
6. **Probability/information:** Deterministic; no current loss is used to fill an initial feedback coordinate.
7. **Boundary/excluded regimes:** This does not say x₀=0. Rather x₀=A₀ applied to this empty history.

## F03

1. **Objects/spaces:** Consecutive actual histories H_t,H_{t+1} and selected g_t.
2. **Quantifiers/order:** Every A,f,p and every natural t.
3. **Assumptions:** No regularity, feasibility, or support-law hypothesis.
4. **Exact conclusion:** H_{t+1}=H_t appended with g_t.
5. **Constants:** A single append at index t; length grows from t to t+1.
6. **Probability/information:** Deterministic. Current f_t is available to g_t; g_t is not an input to the already chosen x_t.
7. **Boundary/excluded regimes:** t=0 is included. A selected vector need not be a supporting vector without an additional legality premise.

## F04

1. **Objects/spaces:** H_t,H_{t+1} and i∈Fin t, embedded by the same index into Fin(t+1).
2. **Quantifiers/order:** For all run inputs, t, and earlier coordinates i<t.
3. **Assumptions:** Only the index bound in the type.
4. **Exact conclusion:** H_{t+1}(i)=H_t(i).
5. **Constants:** Index is unchanged; the new coordinate is t.
6. **Probability/information:** Deterministic persistence of existing vector-history entries.
7. **Boundary/excluded regimes:** No eligible i exists when t=0; the newly appended coordinate is not covered by this equality.

## F05

1. **Objects/spaces:** Actual history H_t and actual selected sequence g from identical A,f,p.
2. **Quantifiers/order:** Every run, every t, every i<t.
3. **Assumptions:** No extra hypotheses beyond the finite index.
4. **Exact conclusion:** H_t(i)=g_i.
5. **Constants:** Exactly index i, with no shift.
6. **Probability/information:** Deterministic correspondence to selections made earlier in this same run.
7. **Boundary/excluded regimes:** The current selection g_t is not in H_t. At t=0 the coordinate quantifier is empty.

## F06

1. **Objects/spaces:** Actual x_t,g and linear-policy trajectory y_t^g fed that selected sequence.
2. **Quantifiers/order:** Every run and every natural t.
3. **Assumptions:** No feasibility, regularity, or legality condition.
4. **Exact conclusion:** x_t=y_t^g=A_t(g₀,…,g_{t−1}).
5. **Constants:** Same index t and same strict-past prefix.
6. **Probability/information:** Deterministic identity. The full sequence g appears as an argument, but y_t queries only its entries below t.
7. **Boundary/excluded regimes:** Does not assert equality for an unrelated vector sequence. Covers t=0 and arbitrary selected vectors, whether legal or not.

## F07

1. **Objects/spaces:** Reconstructed tuple Q_A(H_t), actual output sequence x, and i∈Fin(t+1).
2. **Quantifiers/order:** Every run and t, then every 0≤i≤t.
3. **Assumptions:** No additional hypotheses.
4. **Exact conclusion:** Q_A(H_t)_i=x_i.
5. **Constants:** There are t+1 outputs, including current x_t.
6. **Probability/information:** Deterministic. Earlier output reconstruction truncates the available history to the corresponding strict prefix.
7. **Boundary/excluded regimes:** No claim about x_{t+1}; for t=0 the tuple has just x₀.

## F08

1. **Objects/spaces:** Domain C, policy A, arbitrary f,p, actual x_t.
2. **Quantifiers/order:** Every universally feasible A, every loss/support-policy pair, every t.
3. **Assumptions:** Feasible(C,A): A_s(h)∈C for all times s and every vector history h.
4. **Exact conclusion:** x_t∈C.
5. **Constants:** No numerical or distance bound.
6. **Probability/information:** Deterministic. Universal feasibility implies feasibility on this actual trajectory regardless of p's choices.
7. **Boundary/excluded regimes:** Includes zero time. The converse from actual to universal feasibility is not stated; regular losses are not required.

## F09

1. **Objects/spaces:** Two loss sequences f,f′, common fixed A,p, and paired H_t.
2. **Quantifiers/order:** Every such pair and t; assume f_s=f′_s for every s<t as functions E→EReal.
3. **Assumptions:** The strict-prefix whole-function equalities; A and p are identical in both runs.
4. **Exact conclusion:** H_t(A,f,p)=H_t(A,f′,p).
5. **Constants:** Cutoff is s<t, excluding current t.
6. **Probability/information:** Deterministic strict-past causality conditional on common fixed policies. Current and future losses may differ. This does not prove a policy chosen differently using future data would yield the same history.
7. **Boundary/excluded regimes:** t=0 has vacuous prefix assumptions. Equality of loss values merely at some queried points is insufficient to match the premise. Current selected vectors need not agree.

## F10

1. **Objects/spaces:** Actual outputs of the paired runs from F09's setup.
2. **Quantifiers/order:** Every A,p,f,f′,t with equality of losses at every strict-past time.
3. **Assumptions:** Same fixed A,p and f_s=f′_s for all s<t; no other restrictions.
4. **Exact conclusion:** x_t(A,f,p)=x_t(A,f′,p).
5. **Constants:** Strict cutoff t; no need for f_t=f′_t.
6. **Probability/information:** Deterministic nonanticipation of the play. Initialization is common because A₀ is common. Feedback may use f_t after the play.
7. **Boundary/excluded regimes:** Does not compare different A or p, nor claim strict-past invariance of g_t. Includes the initial play at t=0.

## F11

1. **Objects/spaces:** C,A,f,p,T, universal Feasible(C,A) and Law(C,p), actual L_T.
2. **Quantifiers/order:** Every such data tuple; conclusion is for each played t<T. Law's own quantifiers range over all possible loss/output histories.
3. **Assumptions:** A universally feasible; p satisfies the universal law; Regular_C(f_t) for all t<T.
4. **Exact conclusion:** L_T(A,f,p), i.e. every actual g_t supports f_t at actual x_t before T.
5. **Constants:** Rounds 0 through T−1.
6. **Probability/information:** Deterministic implication from universal premises to actual feedback legality. Off-trajectory behavior is required in the premise, not in the conclusion.
7. **Boundary/excluded regimes:** T=0 is allowed and the conclusion is vacuous. Neither converse nor legality beyond T is asserted.

## F12

1. **Objects/spaces:** C,A,f,T and the actual run with pᵈ=Default.
2. **Quantifiers/order:** Every universally feasible A and loss sequence regular on all t<T.
3. **Assumptions:** Feasible(C,A) and the horizon regularity; no additional caller-supplied Law premise.
4. **Exact conclusion:** L_T(A,f,pᵈ).
5. **Constants:** The default choice's fallback vector is zero; nonempty support sets at these points avoid the empty-set case.
6. **Probability/information:** Deterministic classical support selection from the current loss at the current output.
7. **Boundary/excluded regimes:** T=0 allowed. Default remains defined without regularity, but legality then is not claimed by this declaration.

## F13

1. **Objects/spaces:** C,A,f,p,T and one played loss value at time t<T.
2. **Quantifiers/order:** Every run satisfying horizon regularity and universal feasibility, then each eligible t.
3. **Assumptions:** Feasible(C,A), Regular_C(f_s) for all s<T, and t<T. No Law or actual LegalFeedback assumption is used.
4. **Exact conclusion:** f_t(x_t)=ι(toReal(f_t(x_t))) in EReal.
5. **Constants:** Exact equality with coefficient one; no bound on the magnitude of the finite value.
6. **Probability/information:** Deterministic finite-value guarantee using feasible outputs and regularity. Conversion alone is not the finite-value guarantee.
7. **Boundary/excluded regimes:** Infinite played loss is excluded by the conclusion. For T=0 no t satisfies the premise. No finiteness statement outside the horizon is made.

## F14

1. **Objects/spaces:** One extended-real f, arbitrary x,g∈E, and feasible comparator u∈C.
2. **Quantifiers/order:** Every f,x,g,u satisfying the listed premises; the support relation tests every y∈E.
3. **Assumptions:** Regular_C(f), u∈C, g∈S_f(x). In particular x∈C is not required.
4. **Exact conclusion:** toReal(f(x))−toReal(f(u))≤⟨g,x−u⟩.
5. **Constants:** Coefficient exactly one and no additive slack.
6. **Probability/information:** Deterministic. Properness plus support at x forces finite f(x), even if x is outside C; regularity and feasibility of u force finite f(u).
7. **Boundary/excluded regimes:** No policy, trajectory, gradient norm bound, or global feasibility is needed. An arbitrary unsupported or improper loss does not meet the premises.

## F15

1. **Objects/spaces:** Arbitrary g,x,u∈E and real-valued linear loss ℓ_g(z)=⟨g,z⟩.
2. **Quantifiers/order:** All g,x,u.
3. **Assumptions:** Shared inner-product-space setting only.
4. **Exact conclusion:** ℓ_g(x)−ℓ_g(u)=⟨g,x−u⟩.
5. **Constants:** Exact equality, unit coefficient, no remainder.
6. **Probability/information:** Deterministic algebraic relation; no information assumptions.
7. **Boundary/excluded regimes:** Zero vectors and all x,u allowed. Domain membership and EReal conversions are absent.

## F16

1. **Objects/spaces:** C,A,f,p,T,u; generated selected sequence g; linear losses ℓ^g and linear trajectory y^g for this same A.
2. **Quantifiers/order:** Every run and T with the premises, and each comparator u∈C.
3. **Assumptions:** Regular_C(f_t) for t<T; actual L_T(A,f,p); u∈C. No Feasible(C,A) or universal Law(C,p) hypothesis is listed.
4. **Exact conclusion:**
   \[
   R_T(u;A,f,p)\le\mathcal C_T(\ell^g,y^g,u)
    =\sum_{t<T}\langle g_t,y_t^g\rangle-\sum_{t<T}\langle g_t,u\rangle.
   \]
   F06 identifies y_t^g with the actual x_t; the right side is not regret on a separately chosen run.
5. **Constants:** Exact factor one, with no rate, additive error, or norm coefficient.
6. **Probability/information:** Deterministic. Actual support and properness supply finite played losses even without assuming A's feasibility; comparator losses are finite by regularity. g may be generated adaptively from current losses and prior histories.
7. **Boundary/excluded regimes:** T=0 gives empty sums. No off-trajectory legality or universal linear performance guarantee is required or concluded.

## F17

1. **Objects/spaces:** F16's run and arbitrary B:(ℕ→E)→E→ℕ→ℝ.
2. **Quantifiers/order:** Fix C,A,f,p and horizon T. Assume a bound for every full vector sequence v and every w∈C:
   \[\forall v\ \forall w\in C,\quad\mathcal C_T(\ell^v,y^v,w)\le B(v,w,T).\]
   Then apply the conclusion to each u∈C. The universal premise is at this fixed T, not a separately quantified all-horizons statement.
3. **Assumptions:** Horizon regularity, actual L_T, the universal performance premise above, and u∈C. Universal feasibility and universal support-law premises are absent.
4. **Exact conclusion:** R_T(u;A,f,p)≤B(g,u,T), where g=selected(A,f,p) is precisely the actual generated sequence.
5. **Constants:** No prescribed numerical constants or rate. B is arbitrary in type, need not be nonnegative, and may inspect the full sequence rather than just its first T entries.
6. **Probability/information:** Deterministic universal performance covers the adaptively generated g by instantiation; no independence or oblivious-adversary restriction is in the premise. A bound only for another sequence, or only in expectation, is not the stated input. A remains the same fixed policy in all comparator expressions.
7. **Boundary/excluded regimes:** T=0 is allowed if the corresponding universal bound holds. No vector-norm constraints accompany the universal quantifier; any restriction needed for a proposed B must be addressed in establishing hB. This does not itself provide a useful explicit rate or an anytime guarantee.

## F18

1. **Objects/spaces:** C,A,f,T,u and the Default-generated trajectory, selected gᵈ, and linear run y^{gᵈ}.
2. **Quantifiers/order:** Every domain, universally feasible A, regular horizon loss sequence, and every u∈C.
3. **Assumptions:** Feasible(C,A), Regular_C(f_t) for all t<T, and u∈C; no separately supplied LegalFeedback or Law premise.
4. **Exact conclusion:**
   \[R_T(u;A,f,p^d)\le\mathcal C_T(\ell^{g^d},y^{g^d},u).\]
   The linear vectors and original regret both use this same Default run, with identical plays by F06.
5. **Constants:** Exact coefficient one and no additional term.
6. **Probability/information:** Deterministic classical selection; universal feasibility and regularity provide actual legality and finite played values for this specialization.
7. **Boundary/excluded regimes:** T=0 included. Universal feasibility is required here, unlike in F16 where actual legality is supplied. No numerical B-bound is included in this conclusion.

## Remaining context limits

This v3 packet explicitly types the E parameters and includes the classical choice context used by Default. Its initial explanatory sentence still mentions v2; this report's coverage and hashes are expressly for the file named v3 and its displayed 18 headers. The definitions suffice for the mathematical reconstruction above. The implementation of EReal.toReal and library support facts are not expanded, so no independent elaboration or proof verification is inferred. Conditional strict-past invariance holds with common fixed A and p; no broader assertion about how outside callers select those policies is added. Source fidelity cannot be concluded without an original source and an independent comparison, neither of which was accessed here.
