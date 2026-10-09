# Eight neutral signatures and two Option recursions

Actor /root/osd_blind; requested GPT-6 Astra / medium; runtime model and effort are not independently attested. This reused automated decoder has related staged history, including neutral divergence and extended-loss definitions. It is not a fresh source-naive, absolutely blind, human or externally independent actor. Only the current specified file was read in this task. Imported meanings below use that disclosed prior neutral context, not a new production-body inspection. No proof, compilation or source acceptance is assessed.

The raw input matches the requested SHA256. It supplies two actual definition bodies and eight proposed theorem signatures. The definitions contain classical choice and are noncomputable; their existence in the text does not supply proofs of the theorem signatures.

## Shared context

Except for the final theorem, E is an arbitrary real normed vector space: NormedAddCommGroup E and NormedSpace R E, with neither completeness nor an inner product required. The final theorem explicitly uses NormedAddCommGroup E, InnerProductSpace R E and CompleteSpace E. No statement requires finite dimension.

Use the retained neutral meanings
\[
D_\psi(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}\psi(b))(a-b),\qquad
J_{V,\psi,\alpha,f,x}(z)=f(z)+\iota(\alpha^{-1}D_\psi(z,x)).
\]
Here ι:R→EReal is the finite embedding, and fderiv is total, defaulting to zero when not differentiable. Real inverse at zero is zero. IsMinOn J V p means every z∈V satisfies J(p)≤J(z), without itself including p∈V. Extended-real arithmetic is retained; the first seven signatures and both definitions impose no properness or feasible finiteness, so comparisons involving top or bottom are not silently excluded.

Write A(V,ψ,α,f,x) for advance and I_t=iterate V ψ η loss x0 t. Option E has distinct cases none and some x. none represents the absence specified by this mathematical definition, not a timeout or an unknown computational answer.

## Definition 1: advance

For the supplied arguments, let S be the proposition that some feasible p minimizes J over V. If S holds, advance returns some of the point selected by Classical.choose from this existential; otherwise it returns none.
\[
S\equiv\exists p\in E,\ p\in V\land\forall z\in V,\ J(p)\le J(z),\qquad
A=
\begin{cases}\mathrm{some}(\operatorname{choose}(S)),&S,\\
\mathrm{none},&\neg S.
\end{cases}
\]

1. **Objects:** V:Set E, ψ:E→R, α:R, f:E→EReal, center x:E, and an Option E result.
2. **Quantifiers/order:** Definition applies to arbitrary V,ψ,α,f,x; existential p and its comparisons are inside the branch test.
3. **Assumptions:** No convexity, closedness, nonemptiness, differentiability, positivity, properness, completeness or attainment premise is required to define A.
4. **Operation:** Classical choice of one feasible global-over-V minimizer when one exists; otherwise none. The branch includes both membership and IsMinOn.
5. **Boundaries:** Empty V yields no feasible witness. α=0 or negative is allowed; α=0 uses zero inverse. A minimizer with infinite objective values is not excluded by this bare definition.
6. **Information:** Uses V,ψ,α,f,x, including the current full function f. No future sequence input is an argument. This is a noncomputable mathematical selection, not an executable optimizer.
7. **Excluded scope:** No uniqueness, measurable selection, continuity of selection, finite objective value, or success guarantee is provided. Different extensionally equivalent objectives are not asserted to yield identical choices by any theorem in this packet.

## Definition 2: iterate

\[
I_0=\mathrm{some}(x_0),\qquad
I_{t+1}=I_t.\mathrm{bind}\bigl(x\mapsto A(V,\psi,\eta_t,\ell_t,x)\bigr).
\]
Thus if I_t=none, its successor is none; if I_t=some x, the next result is the current advance result from x.

1. **Objects:** V,ψ, step stream η:N→R, loss stream ℓ:N→E→EReal, and ambient initial x0.
2. **Quantifiers/order:** All parameters are fixed for one recursively defined function N→Option E. At successor t+1, the stream coordinates are indexed by t.
3. **Assumptions:** No feasibility of x0, step sign, loss regularity, or per-step attainment premise.
4. **Operation:** Initial success marker some x0 followed by Option.bind of actual advances. No fallback, reset or skipping of failed rounds.
5. **Boundaries:** I0 is always some, even if x0∉V or V is empty. I_t has consumed rounds 0,…,t−1. I_(t+1) additionally incorporates ℓ_t and η_t. No special T>0 assumption is built in.
6. **Information:** I_t uses the strict prefix of steps/losses relative to t; the post-update I_(t+1) reads the current loss ℓ_t. A future step/loss coordinate is not directly used. The fixed parameters could still be externally chosen using any data; no external protocol is specified.
7. **Excluded scope:** No prediction or regret definition, all-time existence, optimizer implementation, probability law, or online pre-current-loss action guarantee is defined.

## 1. divergence_extension_eq

If ψ and φ agree on X, a lies in X and b lies in its ambient interior, their divergences at the ordered pair (a,b) agree.
\[
\forall X,\psi,\phi,a,b,\quad
[\forall z\in X,\psi(z)=\phi(z)]
\Rightarrow a\in X\Rightarrow b\in\operatorname{int}X
\Rightarrow D_\psi(a,b)=D_\phi(a,b).
\]

1. **Objects:** Normed-core E, set X, two total real functions, points a,b.
2. **Quantifiers/order:** X,ψ,φ,hEq,a,b,ha,hb; all external objects universal.
3. **Assumptions:** Equality on X, a∈X, and b in ambient interior X. No differentiability, convexity or completeness premise.
4. **Conclusion:** Exact equality of divergences with derivative based at b.
5. **Boundaries:** a may be a boundary point. Mere b∈X is insufficient as the stated premise; a set with empty interior admits no such b. Coincident points are allowed.
6. **Information:** Local equality around the derivative base and equality at the evaluated point; no extension algorithm or temporal structure.
7. **Excluded scope:** Does not assert equality of arbitrary advances or chosen iterates under equivalent extensions. Nondifferentiable cases still use total fderiv. No proof supplied.

## 2. advance_some_spec

A successful actual advance returns a feasible minimizer of its exact objective.
\[
\forall V,\psi,\alpha,f,x,p,\quad
A(V,\psi,\alpha,f,x)=\mathrm{some}(p)
\Rightarrow p\in V\land \operatorname{IsMinOn}(J,V,p).
\]

1. **Objects:** Normed-core space and one actual advance with supplied result p.
2. **Quantifiers/order:** V,ψ,α,f,x,p, then success equality.
3. **Assumptions:** Only the actual some-result equality, with no positivity or regularity condition.
4. **Conclusion:** Feasibility and global-over-V minimization, both explicitly conjoined.
5. **Boundaries:** Applies also to α=0/negative and extended infinite objectives; success, not finiteness, is the premise.
6. **Information:** Specification of the point actually returned, not an arbitrary independently selected minimizer.
7. **Excluded scope:** No converse asserting every minimizer is the returned point, no uniqueness, and no general success claim. No proof supplied.

## 3. advance_none_iff

An advance returns none exactly when no feasible minimizer of its objective exists.
\[
A(V,\psi,\alpha,f,x)=\mathrm{none}
\Longleftrightarrow
\neg\exists p,\ p\in V\land\operatorname{IsMinOn}(J,V,p).
\]

1. **Objects:** Arbitrary normed-core V,ψ,α,f,x and the exact regularized objective.
2. **Quantifiers/order:** All five parameters universal, followed by an iff whose right side negates an existential feasible minimizer.
3. **Assumptions:** None beyond the context types.
4. **Conclusion:** Both directions connecting none with absence of an attained feasible minimum.
5. **Boundaries:** Empty V is included; nonempty V can still lack attainment. Zero/negative steps and infinities are not excluded.
6. **Information:** none is a logical nonexistence branch of the noncomputable definition, not a convergence or runtime failure report.
7. **Excluded scope:** Does not equate failure with nonuniqueness or with unboundedness alone; no claim of efficient decidability or proof supplied.

## 4. iterate_prefix

Two runs with the same V,ψ,x0 and equal steps and loss functions at every index strictly below t have equal Option states at t.
\[
[\forall s<t,\eta_s=\eta'_s]\land[\forall s<t,\ell_s=\ell'_s]
\Rightarrow I_t(V,\psi,\eta,\ell,x_0)=I_t(V,\psi,\eta',\ell',x_0).
\]

1. **Objects:** Two normed-core runs, two step streams, two loss streams and common center/domain/generator.
2. **Quantifiers/order:** V,ψ,η,η',loss,loss',x0,t, then hη and hloss.
3. **Assumptions:** Strict-prefix step equality and equality of whole functions loss s=loss' s, not merely equality at played or feasible points.
4. **Conclusion:** Option equality, including either both none or the same some value.
5. **Boundaries:** At t=0 premises are vacuous and both states are some x0. Index t itself and all later coordinates may differ.
6. **Information:** Strict-past dependence of the state I_t; it does not make I_(t+1) independent of loss t.
7. **Excluded scope:** Does not compare runs with different V,ψ,x0 or only matching feasible objective values. No proof supplied.

## 5. iterate_succ_some_spec

If the next state succeeds with p, there exists a previous successful state x from which p is feasible and minimizes the current objective.
\[
I_{t+1}=\mathrm{some}(p)\Rightarrow
\exists x,\ I_t=\mathrm{some}(x)\land p\in V
\land\operatorname{IsMinOn}
\bigl(z\mapsto\ell_t(z)+\iota((\eta_t)^{-1}D_\psi(z,x)),V,p\bigr).
\]

1. **Objects:** One normed-core run, x0, proposed returned p, and natural index t.
2. **Quantifiers/order:** V,ψ,η,loss,x0,p,t and successor-success premise; previous x is existential in the conclusion.
3. **Assumptions:** Success at t+1 only; no step sign, loss properness or initial feasibility.
4. **Conclusion:** Prior success, next-point feasibility and exact current-step minimization based at that prior x.
5. **Boundaries:** At t=0 the prior state is some x0, even if x0 is outside V. Uses η_t and loss t, not t+1.
6. **Information:** Returned p is after current loss processing; existential x is constrained by the actual previous run, not freely selected.
7. **Excluded scope:** No supplied success proof or minimizer existence theorem for arbitrary runs; does not say prior x∈V at t=0.

## 6. iterate_no_recovery

Once a run is none at t, it is none at every index t+k.
\[
\forall t,k\in\mathbb N,\quad I_t=\mathrm{none}\Rightarrow I_{t+k}=\mathrm{none}.
\]

1. **Objects:** One fixed normed-core run and natural t,k.
2. **Quantifiers/order:** V,ψ,η,loss,x0,t,k, then failure premise.
3. **Assumptions:** Only I_t=none.
4. **Conclusion:** Failure persists at the exact offset index t+k.
5. **Boundaries:** k=0 included. t=0 failure is incompatible with the definition I0=some x0; the implication remains conditional.
6. **Information:** Option.bind propagates absence rather than restarting from future losses.
7. **Excluded scope:** No identification of the first failed round or why attainment failed; no proof supplied.

## 7. iterate_complete_of_step_attained

For a fixed horizon T, suppose that at each earlier round, every state actually returned successfully at that round admits a feasible minimizer for its current objective. Then the state at T is successful.
\[
\left[\forall t<T,\ \forall x,\ I_t=\mathrm{some}(x)\Rightarrow
\exists p\in V,\ \operatorname{IsMinOn}
\bigl(z\mapsto\ell_t(z)+\iota((\eta_t)^{-1}D_\psi(z,x)),V,p\bigr)\right]
\Rightarrow\exists p,\ I_T=\mathrm{some}(p).
\]

1. **Objects:** Normed-core run, fixed finite horizon T and attainment restricted to actual successful states.
2. **Quantifiers/order:** V,ψ,η,loss,x0,T, then hatt with nested t<T, all x, success implication, existential feasible p; output is existential terminal p.
3. **Assumptions:** Step attainment on the same trajectory before T. Not universal attainment from every ambient center or for every horizon.
4. **Conclusion:** Existence of some successful terminal state at T. The literal conclusion does not include its membership.
5. **Boundaries:** At T=0 hatt is vacuous and output can be x0, which need not be feasible. For positive T success is post-update, but no additional membership clause is stated here.
6. **Information:** Conditional finite-horizon continuation, with current η_t and loss t used in each attainment premise.
7. **Excluded scope:** Does not establish hatt, all-time completeness, positivity, regularity, computability or an optimizer. “Complete” in the name does not add a CompleteSpace typeclass to this theorem.

## 8. iterate_one_step

In a complete real inner-product space, suppose the actual consecutive states are some x and some p. For the current round assume positive η_t, proper current loss, global supporting vectors at every feasible point, convex V, and ambient differentiability of ψ at x and p. Then every feasible u satisfies the real finite-part loss bound with the two signed divergence residuals.
\[
\begin{aligned}
&I_t=\mathrm{some}(x),\quad I_{t+1}=\mathrm{some}(p),\quad
\eta_t>0,\quad\operatorname{Convex}(V),\\
&\operatorname{Proper}(\ell_t),\quad
[\forall z\in V,\ \partial\ell_t(z)\ne\varnothing],\quad
\operatorname{DifferentiableAt}(\psi,x),\
\operatorname{DifferentiableAt}(\psi,p)\\
&\Longrightarrow \forall u\in V,\quad
\eta_t\bigl((\ell_t(p)).\mathrm{toReal}-(\ell_t(u)).\mathrm{toReal}\bigr)
\le D_\psi(u,x)-D_\psi(u,p)-D_\psi(p,x).
\end{aligned}
\]

1. **Objects:** Complete real inner-product E; V,ψ,step/loss streams,x0, actual consecutive x,p and t, plus feasible u.
2. **Quantifiers/order:** V,hV,ψ,η,loss,x0,x,p,t,hx,hp,hη,hf,hs,hdx,hdp, then all u∈V. Both state equalities concern the same run.
3. **Assumptions:** Current-step positivity only, convex V, ambient properness of loss t (no bottom anywhere and an ambient finite witness), and ∀z∈V ∃g ∀ambient y support comparisons. ψ differentiable at both endpoints. There is no f/loss derivative, ψ convexity, x∈V, separately supplied p∈V, or explicit IsMinOn premise here.
4. **Conclusion:** The same-current-loss finite-part difference is multiplied by η_t and bounded by +D(u,x)−D(u,p)−D(p,x). Successful recursion is the input encoding the step and its selected minimizer, instead of a free minimizer hypothesis.
5. **Boundaries:** x may be outside V at t=0; successful p is a post-update point. Earlier step sizes are not assumed positive; only η_t is. No finite dimension, closed V, or T>0 parameter. u=p is permitted when feasible and gives cancellation. Without ψ convexity neither subtracted residual is asserted nonnegative.
6. **Information/extended values:** loss t is consumed to form p; x is the prior state. Proper/global supports supply the intended finite feasible-loss setting, while top values outside V remain allowed; bottom is excluded globally for this current loss. No stochastic law or standard pre-current-loss prediction is asserted.
7. **Excluded scope/proof boundary:** No existence of successful states or supporting vectors is proved by the header, nor uniqueness, telescoping regret, source fidelity or all-time convergence. Earlier mathematical meanings are disclosed neutral context, not proof acceptance.

## Completeness and unresolved context

All eight theorem signatures and both definition bodies have been reconstructed with seven slots and explicit branch/index boundaries. No unresolved semantic question remains under the disclosed retained imported meanings. Their exact implementation identity in production was not inspected. No theorem proof body is present; declaration meaning and the two definitions are not compilation or proof evidence.
