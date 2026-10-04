# Blind reconstruction of F01–F18

This distinct automated decoder used only `blind-packet-v1.md` for this package. No other source, proof, context, report, or verdict file was read. No attribution is inferred from other packages. This is a mathematical decoding of unproved headers, not a proof check, compilation certificate, source-acceptance decision, human review, or external-model review.

Packet SHA-256, independently calculated on raw file bytes:
`8fa339b23741cd83f1d2e0c3b1710ab93b88ded4a4a7101be2bd441728800ce1`.

## Complete shared context

The ambient E is an arbitrary finite-dimensional real inner-product space with its normed additive commutative group structure. All headers retain this setting; no positive dimension is required. A domain V supplies a nonempty, closed, convex carrier C⊆E. Boundedness is not built into that structure.

Losses f_t:E→EReal are extended-real-valued. Properness means exactly that f never takes −∞ anywhere in E and that there exist z∈E and r∈ℝ with f(z)=r. This finite witness need not be in C. The support-vector set is

\[
S_f(x)=\{g\in E:\forall y\in E,\ f(x)+\iota(\langle g,y-x\rangle)\le f(y)\},
\]

where ι embeds a real into EReal. The query y ranges over all E, not just C or the finite-valued domain. Regularity is

\[
\operatorname{Reg}_C(f)\iff\operatorname{Proper}(f)
 \land\forall x\in C,\ S_f(x)\ne\varnothing.
\]

There is no separately stated global convexity hypothesis on f. Regularity supplies globally supporting vectors at every point in C. Properness plus a supporting vector at any point x forces f(x) to be finite: −∞ is excluded by properness, while +∞ contradicts the support inequality at the finite witness. In particular regularity gives finite values throughout C. This mathematical observation explains why actual finite-value production matters before using toReal. The packet does not reproduce the definition of EReal.toReal; no theorem here should be read as identifying arbitrary infinite values with finite losses merely because the conversion returns a real number.

A linear policy A consists of functions A_t:E^{\{0,…,t−1\}}→E. Despite its name, this is an arbitrary function of the strict-past vector history; A itself is not required to be a linear map. Universal feasibility means

\[
\forall t\in\mathbb N\ \forall h\in E^t,\quad A_t(h)\in C.
\]

It covers every input history, including histories not realized by the construction. A support policy p_t takes t past whole loss functions, t+1 output vectors, and the current whole loss function, returning a vector in E. It has no future-loss input. Its universal law says that for every t, arbitrary past functions, arbitrary output tuple h, and current f, if Reg_C(f) and h_t∈C, then p_t(past,h,f)∈S_f(h_t). It requires no consistency of that tuple with a run and no feasibility of earlier coordinates. This is stronger than legality only on one generated trajectory.

For h=(h₀,…,h_{t−1}), define the reconstructed output tuple

\[
Q_A(h)_i=A_i(h_0,\ldots,h_{i-1}),\qquad 0\le i\le t.
\]

The actual vector histories H_t, plays x_t, and selected vectors g_t for fixed A,f,p are

\[
H_0=(),\qquad x_t=A_t(H_t),\qquad
 g_t=p_t((f_s)_{s<t},Q_A(H_t),f_t),\qquad
 H_{t+1}=H_t\mathbin{\|}(g_t).
\]

History thus means a history of selected vectors, not outputs or losses. Current g_t is appended only after x_t is produced. The initial play is A₀ applied to the empty tuple, rather than a separately supplied initialization. Both policies A and p are fixed throughout any paired-run causality comparison.

Actual legality L_T(A,f,p) means ∀t<T, g_t∈S_{f_t}(x_t), only at the generated plays. It imposes nothing on off-trajectory histories or rounds t≥T. The default policy uses c(f,x), an arbitrary classical choice from S_f(x) when nonempty and zero otherwise; pᵈ_t(past,h,f)=c(f,h_t). It ignores past loss functions and all but the last output coordinate. It is not claimed to be computable or to select a unique supporting vector.

For any full vector sequence v:ℕ→E, define

\[
y_t^v=A_t(v_0,\ldots,v_{t-1}),\qquad \ell_t^v(z)=\langle v_t,z\rangle.
\]

For arbitrary real-valued losses ℓ_t, output sequence y, comparator u, and T∈ℕ, the comparator difference is

\[
\mathcal C_T(\ell,y,u)=\sum_{t=0}^{T-1}\ell_t(y_t)
 -\sum_{t=0}^{T-1}\ell_t(u).
\]

This is a difference of sums, not a minimum over comparators. Write

\[
R_T(u;A,f,p)=\sum_{t=0}^{T-1}
 [\operatorname{toReal}f_t(x_t)-\operatorname{toReal}f_t(u)].
\]

Time is zero based; T rounds means indices 0 through T−1. All displayed assertions are deterministic. There is no random variable, expectation, probability event, filtration, independence premise, or oracle sampling assumption. References below to these definitions always mean these exact objects and the same generated run unless two runs are explicitly compared.

## F01 — final coordinate of a reconstructed output history

1. **Objects/spaces:** A, time t, arbitrary h∈E^t, and Q_A(h)∈E^{t+1}.
2. **Quantifiers/order:** Every A, every natural t, and every finite vector history h.
3. **Assumptions:** Only the shared ambient structure and the stated types; no feasibility or loss assumptions.
4. **Exact conclusion:** Q_A(h)_t=A_t(h).
5. **Constants:** The last index is t; there are t+1 reconstructed outputs and t input vectors.
6. **Probability/information:** Deterministic; the play at t uses precisely the vectors with indices less than t.
7. **Boundary/exclusions:** At t=0 it is the initial play from the empty history. The assertion applies to arbitrary, possibly unrealized histories.

## F02 — empty initial vector history

1. **Objects/spaces:** Fixed A,f,p and H₀, a function from the empty index set Fin 0 into E.
2. **Quantifiers/order:** Every such policy pair and full loss sequence.
3. **Assumptions:** None beyond shared typing.
4. **Exact conclusion:** H₀ is the unique empty function Fin.elim0.
5. **Constants:** Zero history length at time zero.
6. **Probability/information:** Deterministic; no current or future loss contributes a vector before the initial play.
7. **Boundary/exclusions:** This is not a claim that x₀ is the zero vector. The initial output is A₀(()).

## F03 — append the current feedback

1. **Objects/spaces:** H_t,H_{t+1},g_t of one fixed A,f,p run.
2. **Quantifiers/order:** Every shared input tuple and every t∈ℕ.
3. **Assumptions:** No feasibility, regularity, or legal-feedback assumption.
4. **Exact conclusion:** H_{t+1}=H_t appended with g_t, as equality of functions with t+1 coordinates.
5. **Constants:** Exactly one vector is appended at index t.
6. **Probability/information:** Deterministic; g_t may depend on current whole loss f_t, whereas x_t has already been constructed from H_t.
7. **Boundary/exclusions:** Includes t=0. Appending an arbitrary policy output does not establish that it supports the loss.

## F04 — persistence of earlier vector coordinates

1. **Objects/spaces:** A run, t, and i∈Fin t, identified with the same index in Fin(t+1).
2. **Quantifiers/order:** Every run, t, and such earlier index i.
3. **Assumptions:** No additional restrictions.
4. **Exact conclusion:** H_{t+1}(i)=H_t(i).
5. **Constants:** The index is preserved, not shifted; the newly appended coordinate t is outside this statement.
6. **Probability/information:** Deterministic preservation of recorded past vectors.
7. **Boundary/exclusions:** For t=0 there is no i to instantiate. The declaration does not assert equality of the entire histories, whose lengths differ.

## F05 — history coordinates are the actual earlier selections

1. **Objects/spaces:** One generated run, H_t, and its selected sequence g.
2. **Quantifiers/order:** Every run and t, then every i<t.
3. **Assumptions:** Only the finite-index premise embodied by i∈Fin t.
4. **Exact conclusion:** H_t(i)=g_i.
5. **Constants:** Exact same index i; no offset between stored coordinates and selected vectors.
6. **Probability/information:** Deterministic identification with selections from this run, not from a recomputed run using other policies or losses.
7. **Boundary/exclusions:** t=0 gives no coordinate claims. There is no assertion about g_t being stored in H_t.

## F06 — identical plays on the generated linear feedback sequence

1. **Objects/spaces:** Generated x_t,g_t and the linear-policy trajectory y_t^g on the full selected sequence.
2. **Quantifiers/order:** Every A,f,p and every t.
3. **Assumptions:** No feasibility, legality, or regularity is required.
4. **Exact conclusion:** x_t=y_t^g=A_t(g₀,…,g_{t−1}).
5. **Constants:** Same time t and exactly the strict-past prefix.
6. **Probability/information:** Deterministic equality on the same generated vector sequence. Even though g is a full sequence, y_t^g only queries indices below t.
7. **Boundary/exclusions:** This does not equate the run to one driven by an arbitrary different vector sequence. It asserts trajectory identity, not performance.

## F07 — reconstructed output tuple matches every actual earlier play

1. **Objects/spaces:** Q_A(H_t), actual output sequence x, and i∈Fin(t+1).
2. **Quantifiers/order:** Every run and t, then each index 0≤i≤t.
3. **Assumptions:** No additional mathematical premise.
4. **Exact conclusion:** Q_A(H_t)_i=x_i.
5. **Constants:** The tuple includes the current play i=t as well as all previous plays.
6. **Probability/information:** Deterministic; recomputing an earlier play uses only its own vector prefix even when a longer history is supplied to Q_A.
7. **Boundary/exclusions:** Does not include x_{t+1}. For t=0 it identifies the sole reconstructed coordinate with the initial output.

## F08 — actual plays are feasible under a universal policy condition

1. **Objects/spaces:** Domain C, universally feasible A, and arbitrary f,p.
2. **Quantifiers/order:** Every such domain/policy/run and every t∈ℕ.
3. **Assumptions:** ∀s ∀h∈E^s, A_s(h)∈C.
4. **Exact conclusion:** x_t∈C.
5. **Constants:** No distance, dimension, or norm bound.
6. **Probability/information:** Deterministic restriction inherited from all-history feasibility, without restrictions on what vectors p selects.
7. **Boundary/exclusions:** Includes time zero and all later times. The premise is stronger than feasibility on a single run; the converse is not asserted.

## F09 — strict-past causality of vector histories

1. **Objects/spaces:** Two loss sequences f,f′ with common fixed A and p, and their histories at time t.
2. **Quantifiers/order:** For every A,p,f,f′,t, if f_s=f′_s as whole functions for all s<t, then the histories coincide.
3. **Assumptions:** Exactly strict-past equality of losses; no regularity or legal feedback.
4. **Exact conclusion:** H_t(A,f,p)=H_t(A,f′,p).
5. **Constants:** The cutoff is s<t, not s≤t.
6. **Probability/information:** Deterministic nonanticipation conditional on holding both policies fixed. Current and future losses may differ. This does not certify the absence of externally encoded information if one changes A or p depending on the loss sequence.
7. **Boundary/exclusions:** At t=0 the premise is vacuous. It does not assert equality of g_t when current loss functions differ; equality at played points alone is weaker than the required whole-function equality.

## F10 — strict-past causality of actual plays

1. **Objects/spaces:** The paired runs with shared A,p and possibly different losses.
2. **Quantifiers/order:** For every t, assuming whole-function equality f_s=f′_s for each s<t.
3. **Assumptions:** The stated prefix equality, with policies A and p identical between runs.
4. **Exact conclusion:** x_t(A,f,p)=x_t(A,f′,p).
5. **Constants:** Strict cutoff at t; current loss need not agree.
6. **Probability/information:** Deterministic causality for the play, not for current feedback. The initialization is shared automatically because A₀ is the same fixed map.
7. **Boundary/exclusions:** t=0 is included. No statement compares different policies or external choices of policy tied to different future data.

## F11 — universal laws produce played-trajectory legality

1. **Objects/spaces:** C,A,p,f,T, universal Feasible(C,A), universal Law(C,p), and actual L_T.
2. **Quantifiers/order:** Every such run and horizon T; the conclusion quantifies only over actual rounds t<T.
3. **Assumptions:** A feasible at every vector history; p obeys the oracle law at every allowed tuple; Reg_C(f_t) for all t<T.
4. **Exact conclusion:** L_T(A,f,p), namely g_t∈S_{f_t}(x_t) for every t<T.
5. **Constants:** Horizon range {0,…,T−1}.
6. **Probability/information:** Deterministic implication from two universal conditions to an actual-run condition. Law's antecedent requires only its tuple's last output to belong to C; it is not itself confined to generated tuples.
7. **Boundary/exclusions:** T=0 is allowed and legality is vacuous. No assertion that actual legality implies either universal law, and no restrictions after the horizon.

## F12 — default support selection is legal along a feasible run

1. **Objects/spaces:** C,A,f,T and the run generated with pᵈ=Default.
2. **Quantifiers/order:** Every domain, universally feasible A, loss sequence, and horizon with regular losses before T.
3. **Assumptions:** Universal feasibility of A and Reg_C(f_t) for every t<T.
4. **Exact conclusion:** L_T(A,f,pᵈ).
5. **Constants:** Default's fallback is vector zero when no supporting vector exists; the assumptions ensure support exists at these played points.
6. **Probability/information:** Deterministic classical choice, not random selection. No separate Law premise is requested from the caller.
7. **Boundary/exclusions:** T=0 allowed. Default is defined even for irregular losses, but legality in those regimes is not concluded here.

## F13 — played loss equals its finite-real embedding

1. **Objects/spaces:** C,A,f,p,T and one t<T, with actual x_t.
2. **Quantifiers/order:** All shared run data and horizon, followed by any natural t satisfying t<T.
3. **Assumptions:** Universal feasibility of A and Reg_C(f_s) for every s<T. No legality or universal law for p is required.
4. **Exact conclusion:** f_t(x_t)=ι(toReal(f_t(x_t))) as equality in EReal. This identifies the played loss as a finite real value.
5. **Constants:** The embedding has coefficient one; there is no numerical loss bound.
6. **Probability/information:** Deterministic finite-value production from regularity and feasibility, not a conclusion obtained merely by applying a total conversion function.
7. **Boundary/exclusions:** For T=0 there is no eligible t. No conclusion about times t≥T or arbitrary outside-domain points. Both infinite values at the displayed point are excluded by the equality.

## F14 — one supporting vector bounds finite loss difference

1. **Objects/spaces:** C, one extended-real loss f, arbitrary x,g∈E, and comparator u∈C.
2. **Quantifiers/order:** Every such f,x,g,u satisfying the listed premises; support quantifies over every query y∈E.
3. **Assumptions:** Reg_C(f), u∈C, and g∈S_f(x). There is no x∈C premise and no trajectory here.
4. **Exact conclusion:** toReal(f(x))−toReal(f(u))≤⟨g,x−u⟩.
5. **Constants:** Exact coefficient one, no additive error or norm factor.
6. **Probability/information:** Deterministic. Properness plus support at x supplies finite f(x) even outside C; regularity and u∈C supply finite f(u). Thus this is a finite loss-difference inequality under its assumptions.
7. **Boundary/exclusions:** Does not require x feasible or a policy universally legal. Properness cannot simply be omitted while interpreting toReal terms as finite losses. It asserts no global smoothness or magnitude bounds.

## F15 — linear loss difference identity

1. **Objects/spaces:** Arbitrary g,x,u∈E, with ℓ_g(z)=⟨g,z⟩∈ℝ.
2. **Quantifiers/order:** Every triple g,x,u.
3. **Assumptions:** Only the ambient real inner-product structure; no domain or regularity condition.
4. **Exact conclusion:** ℓ_g(x)−ℓ_g(u)=⟨g,x−u⟩.
5. **Constants:** Exact equality and coefficient one.
6. **Probability/information:** Deterministic algebraic identity, unrelated to an information restriction or random outcome.
7. **Boundary/exclusions:** Zero vectors and arbitrary x,u are included. These linear losses are real-valued; no EReal coercion is involved.

## F16 — actual loss regret is bounded by same-trajectory linear regret

1. **Objects/spaces:** C,A,f,p,T,u; actual sequence g selected by this run; linear losses ℓ_t^g and plays y_t^g.
2. **Quantifiers/order:** Every such run and T, then every u∈C, under regularity and actual legality on t<T.
3. **Assumptions:** Reg_C(f_t) for every t<T; L_T(A,f,p); u∈C. Crucially there is no universal Feasible(C,A) or Law(C,p) premise.
4. **Exact conclusion:**
   \[
   R_T(u;A,f,p)\le\mathcal C_T(\ell^g,y^g,u)
   =\sum_{t<T}\langle g_t,y_t^g\rangle-\sum_{t<T}\langle g_t,u\rangle.
   \]
   F06 identifies y_t^g with the actual x_t. This is a reduction on the identical generated trajectory, not a new independent execution on arbitrary vectors.
5. **Constants:** Exact factor one; no additive remainder, gradient bound, step size, or asymptotic rate.
6. **Probability/information:** Deterministic. Actual legality and properness suffice for finite played losses even without assumed feasibility of A; comparator finiteness follows from regularity. The generated g can depend on current loss and past outputs.
7. **Boundary/exclusions:** T=0 yields empty sums. No universal performance guarantee is claimed by this header alone, and no off-trajectory legality is needed.

## F17 — transfer of a universal linear-performance bound

1. **Objects/spaces:** The data of F16 and an arbitrary real-valued functional B:(ℕ→E)→E→ℕ→ℝ.
2. **Quantifiers/order:** Fix C,A,f,p and the particular horizon T, with regularity and actual legality. Choose B with the premise
   \[
   \forall v:\mathbb N\to E\ \forall w\in C,
   \quad\mathcal C_T(\ell^v,y^v,w)\le B(v,w,T).
   \]
   Then for each u∈C the conclusion applies to g=selected(A,f,p). Universality is over every full vector sequence and every feasible comparator, at this fixed T; the premise is not explicitly universal over horizons.
3. **Assumptions:** Exactly horizon regularity, actual L_T, the universal bound just displayed, and u∈C. No universal feasibility or oracle-law premise is listed.
4. **Exact conclusion:** R_T(u;A,f,p)≤B(g,u,T), with the actual generated sequence g as B's first argument.
5. **Constants:** No particular numerical rate or constants are specified. B can depend on the whole sequence, comparator, and horizon, and need not be nonnegative or a prefix-only functional by type.
6. **Probability/information:** Deterministic universal premise can be instantiated with the adaptively generated feedback sequence; it does not require that sequence be independent or chosen in advance. A claim only for one other sequence or in expectation would not match this premise. All uses of A and its linear run refer to the same fixed A.
7. **Boundary/exclusions:** T=0 allowed, provided its universal premise holds. Conditional vector bounds are not separately present in hB; any such restrictions must be accounted for when establishing the universally quantified premise. This header does not itself prove a useful B, an anytime rate, or independence of B from future vectors.

## F18 — default-policy regret reduction

1. **Objects/spaces:** C,A,f,T,u and the actual run with Default; its selected sequence gᵈ and linear run y^{gᵈ}.
2. **Quantifiers/order:** Every domain, universally feasible A, loss sequence and horizon with regularity, then each u∈C.
3. **Assumptions:** Feasible(C,A), Reg_C(f_t) for all t<T, and u∈C. No separate LegalFeedback or Law premise is demanded.
4. **Exact conclusion:**
   \[
   R_T(u;A,f,p^d)\le\mathcal C_T(\ell^{g^d},y^{g^d},u).
   \]
   Both the selected sequence and the left-side loss regret belong to the same Default-generated run; its outputs equal the linear-run outputs.
5. **Constants:** Exact coefficient one and no additional error term.
6. **Probability/information:** Deterministic reduction with classical support selection. Feasibility and regularity supply the needed actual legality and finite losses. It does not require random or independent feedback.
7. **Boundary/exclusions:** T=0 included. Unlike F16, universal feasibility is a premise here because legality is derived rather than supplied. No numerical linear-performance bound B is part of this conclusion.

## Scope limitations

The packet gives enough mathematical definitions to reconstruct the finite-history trajectory, law scopes, comparator expression, and quantifier order. EReal.toReal itself and supporting library facts are not expanded in the packet, so this report does not assert a formal validation of those implementation details. F13's explicit equality and properness-plus-support in F14/F16/F17 identify the necessary finite-value interpretation. The declarations are unproved data here; no theorem body, compiler, original source, or acceptance evidence was consulted. Same-policy strict-past invariance is preserved without upgrading it to an unrestricted claim about how externally supplied policies are chosen.
