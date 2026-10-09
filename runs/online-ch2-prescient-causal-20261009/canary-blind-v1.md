# Four neutral Option-run canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, without runtime model/effort attestation. This is a reused automated actor with related neutral-definition history, not a fresh source-naive, absolutely blind, human or externally independent reviewer. Only the current neutral file was read. No production proof, source card, paper, or other current material was consulted.

## Context and one missing definition

From disclosed earlier neutral context, write
\[
D_\psi(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}\psi(b))(a-b).
\]
fderiv defaults to zero at a nondifferentiable base. Let A be the actual advance: it returns some chosen feasible minimizer of f(z)+ι(η⁻¹Dψ(z,x)) if one exists, and none otherwise. Let I_t(V,ψ,η,loss,x0) be the actual Option recursion: I0=some x0 and I_(t+1)=I_t.bind(advance using η_t,loss_t). Here ι embeds real values into EReal, top is +∞, and toReal sends both infinite endpoints to zero. IsMinOn alone supplies value comparisons, not membership.

Proper f means no bottom anywhere and an ambient finite witness. A supporting vector at z must satisfy f(z)+ι(g(y−z))≤f(y) for EVERY real y; nonempty support at feasible z does not restrict y to the feasible set.

The input introduces SourceClosed but does not define it, and its exact definition is not present in this actor's retained neutral context. I retain that predicate literally in theorem 3. Its mathematical meaning cannot be certified as epigraph closedness, lower semicontinuity, or another condition from its name alone. This is the sole unresolved context item; no forbidden lookup was made. StrictConvexOn, IsClosed, Convex, EqOn, interior and scalar differentiability have their ordinary stated meanings. The import does not verify any theorem body or production-definition identity.

## 1. two_distinct_current_losses

The local lets fix
\[
V=[-1,1],\quad \psi(z)=z^4/4+z^2/2,\quad
f_0(z)=\begin{cases}\iota(|z|)&z\in V\\+\infty&z\notin V,\end{cases}
\quad
f_1(z)=\begin{cases}\iota(-5z/8)&z\in V\\+\infty&z\notin V,\end{cases}
\]
and loss_t=f0 when t=0, otherwise f1. They scope the full conjunction. Denote the run with constant step 1 and initial center 1/2 by I_t.

The sixteen top-level assertions are: properness of each loss; nonempty global supports for each loss at every feasible point; strict global convexity of ψ; nondifferentiability of abs at zero; top value at 2 for each loss; states some(1/2), some(0), some(1/2) at times 0,1,2; invariance of the time-2 state under arbitrary future step/loss choices matching the first two coordinates; two ordered divergence values; an all-feasible two-round loss comparison; and a separate numerical inequality.

\[
\begin{aligned}
&\operatorname{Proper}(f_0)\land\operatorname{Proper}(f_1)\\
&\land[\forall z\in V,\partial f_0(z)\ne\varnothing]
\land[\forall z\in V,\partial f_1(z)\ne\varnothing]\\
&\land\operatorname{StrictConvexOn}(\mathbb R,\psi)
\land\neg\operatorname{DifferentiableAt}(|\cdot|,0)\\
&\land f_0(2)=+\infty\land f_1(2)=+\infty\\
&\land I_0=\mathrm{some}(1/2)\land I_1=\mathrm{some}(0)
\land I_2=\mathrm{some}(1/2)\\
&\land[\forall\eta',\mathrm{loss}',\
\eta'_0=1\Rightarrow\eta'_1=1\Rightarrow
\mathrm{loss}'_0=f_0\Rightarrow\mathrm{loss}'_1=f_1
\Rightarrow I_2(V,\psi,\eta',\mathrm{loss}',1/2)=\mathrm{some}(1/2)]\\
&\land D_\psi(0,1/2)=11/64
\land D_\psi(1/2,0)=9/64\\
&\land[\forall u\in V,\
(F_0(0)-F_0(u))+(F_1(1/2)-F_1(u))\\
&\hspace{4em}\le D_\psi(u,1/2)-D_\psi(u,1/2)
-D_\psi(0,1/2)-D_\psi(1/2,0)]\\
&\land(-1/2\le-5/16),\qquad F_i=f_i.\mathrm{toReal}.
\end{aligned}
\]

1. **Objects:** Two distinct concrete extended-real losses, one nonquadratic generator, the exact actual Option run, a shared comparator u and variable comparison streams.
2. **Quantifiers/order:** All lets are fixed. Sixteen conjuncts; support clauses quantify feasible z then some g then every ambient y. The stream clause universally quantifies entire η',loss' and then four implications. Comparator u is universally quantified only in its clause.
3. **Assumptions:** No external premises. Regularity, properness, supports and actual successful states are conclusions, not supplied assumptions. Equality loss'0=f0 and loss'1=f1 is equality of full functions.
4. **Conclusion:** All sixteen properties above, including two actual state transitions and a sum of current-loss finite-part differences evaluated at post-update points 0 and 1/2. Both endpoint divergences have the same arguments and cancel; the two movement residuals are subtracted.
5. **Constants/boundaries:** Step 1 throughout the named run; first two losses at t=0,1. Loss t remains f1 at every later t, though no later success is stated. Both tested divergences have unequal ordered values. The comparator RHS is −20/64=−5/16; u=1/2 gives the separate −1/2≤−5/16. The time-zero state is the initial some value, before loss0.
6. **Information/finite values:** Time 1 consumes f0, time 2 consumes f1. The alternate-stream clause leaves every coordinate from 2 onward unrestricted and permits arbitrary signs there. Top values outside V are actual extended losses; finite-part comparisons are restricted to V.
7. **Excluded claims:** No failure-free infinite run, pre-current-loss prediction, all-stream theorem, best-comparator infimum, expectation, or proof/helper-dependency claim. Asymmetric divergence values must not be swapped or combined as equal.

## 2. boundary_outside_center_run

Local definitions are
\[
V=[0,1],\quad f(z)=\begin{cases}\iota(z)&z\in V\\+\infty&z\notin V,\end{cases}
\quad\psi(z)=z^2/2.
\]
The nine conjuncts assert proper f, global supports at every feasible point, strictly convex ψ, top loss at −1, center −1 outside V, actual one-step result some 0, one divergence value, a comparator bound and a numerical inequality.
\[
\begin{aligned}
&\operatorname{Proper}(f)\land[\forall z\in V,\partial f(z)\ne\varnothing]
\land\operatorname{StrictConvexOn}(\mathbb R,\psi)\\
&\land f(-1)=+\infty\land(-1\notin V)\\
&\land I_1(V,\psi,(1)_t,(f)_t,-1)=\mathrm{some}(0)
\land D_\psi(0,-1)=1/2\\
&\land[\forall u\in V,\ -u\le D_\psi(u,-1)-D_\psi(u,0)-D_\psi(0,-1)]\\
&\land(-1/2\le1/2).
\end{aligned}
\]

1. **Objects:** Linear finite loss restricted by top, quadratic generator, outside initial center and actual one-step Option output.
2. **Quantifiers/order:** Three local lets scope nine conjuncts. Support and comparator universals are internal; the run is fixed.
3. **Assumptions:** No external hypotheses. Actual success and center nonmembership are asserted. No abs or nondifferentiability clause occurs here.
4. **Conclusion:** First updated state is the boundary point 0 despite the outside center and its infinite loss. Comparator loss difference on V is −u, with exactly two negative divergence residuals.
5. **Constants/boundaries:** η0=1; I0=some(−1) by the retained definition, while the target explicitly specifies I1. The interval includes endpoints 0 and 1. u=0 yields equality and u=1/2 corresponds to the numeric clause.
6. **Information/extended values:** Center loss f(−1)=top is not a value substituted for ψ in the regularizer. The minimization step uses the current full f and regularization centered at −1; supports compare all ambient y.
7. **Excluded claims:** No necessity of feasible initialization, no claim f finite everywhere, no later-state assertion, no unconstrained minimizer or supplied proof.

## 3. closed_strict_regularizer_missing_minimum

The fixed lets are V=(−∞,0], f(z)=ι(z) for ALL real z, and ψ(z)=exp z. The fourteen conjuncts include explicit geometric/regularity properties, a supplied-but-undefined SourceClosed predicate, an exact objective formula, absence of any feasible minimizer, none from advance, and none at every positive iterate time.
\[
\begin{aligned}
&V\ne\varnothing\land\operatorname{IsClosed}(V)
\land\operatorname{Convex}(V)\land0\in V\\
&\land\operatorname{Proper}(f)
\land[\forall z\in\mathbb R,\partial f(z)\ne\varnothing]\\
&\land\operatorname{SourceClosed}(z\mapsto\iota(\psi(z)))\\
&\land\operatorname{StrictConvexOn}(\mathbb R,\psi)
\land[\forall z\in\mathbb R,\operatorname{DifferentiableAt}(\psi,z)]
\land0\in\operatorname{int}(\mathbb R)\\
&\land[\forall z\in\mathbb R,\ f(z)+\iota(D_\psi(z,0))
=\iota(e^z-1)]\\
&\land\neg\exists p,\ p\in V\land
\operatorname{IsMinOn}(z\mapsto f(z)+\iota(D_\psi(z,0)),V,p)\\
&\land A(V,\psi,1,f,0)=\mathrm{none}\\
&\land[\forall k\in\mathbb N,\
I_{k+1}(V,\psi,(1)_t,(f)_t,0)=\mathrm{none}].
\end{aligned}
\]

1. **Objects:** Closed half-line, everywhere finite linear EReal loss, exponential real generator, initial center 0, constant unit steps and constant loss stream.
2. **Quantifiers/order:** Three fixed lets and fourteen conjuncts. Support and differentiability run over every real z, not merely V. The minimum existential is negated as a whole. The final k is universally natural.
3. **Assumptions/context gap:** No external premises; all listed conditions are proposed conclusions. SourceClosed's exact definition is absent from the allowed input and cannot be decoded fully; its argument is precisely the EReal embedding of exp, not f or the full proximal objective.
4. **Conclusion:** The full objective identity is ambient and in EReal. There is no feasible attained minimum on V, the actual first advance is none, and all strictly positive states are none.
5. **Constants/boundaries:** p must lie in V in the negated existence statement. 0 belongs to V but the interior assertion is interior(univ), NOT interior V. k=0 gives failure at time 1; I0 is still some 0. η=1 makes inverse factor 1. The objective exp z−1 remains finite at every z; absence of attainment must not be conflated with an infinite value at a feasible point.
6. **Information/interpretation:** Static nonattainment causes the Option branch to fail; the recursion propagates none. The same generator can be strictly convex and differentiable while the given objective has no minimum on this noncompact domain. No stochastic or computational failure is asserted.
7. **Excluded claims:** The header does not specify an infimum value or prove a general nonexistence theorem, and does not make strict convexity/closedness sufficient for attainment. SourceClosed cannot be expanded from its name. None of these assertions has a supplied proof here.

## 4. interior_extension_boundary_difference

The fixed lets are
\[
X=[0,\infty),\qquad\psi(z)=z^2+z,\qquad\phi(z)=z^2+|z|.
\]
Nine conjuncts assert agreement on X, disagreement at −1, interior and membership facts, identical divergence at an interior base with value 1, different divergence values at boundary base 0, and nondifferentiability of φ there.
\[
\begin{aligned}
&[\forall z\in X,\psi(z)=\phi(z)]\land\psi(-1)\ne\phi(-1)
\land1\in\operatorname{int}X\land2\in X\\
&\land D_\psi(2,1)=D_\phi(2,1)
\land D_\psi(2,1)=1\\
&\land D_\psi(2,0)=4
\land D_\phi(2,0)=6
\land\neg\operatorname{DifferentiableAt}(\phi,0).
\end{aligned}
\]

1. **Objects:** Two actual real functions on the entire line and a closed half-line on which they agree; no minimization, loss stream or Option state appears.
2. **Quantifiers/order:** Three local lets, nine fixed conjuncts, with EqOn internally universal on X.
3. **Assumptions:** No external premise; equality, point membership and failure of differentiability are conclusions.
4. **Conclusion:** Exact ordered divergences at (2,1) agree and equal 1; at (2,0) the stated values differ, 4 versus 6. The base point is always the second argument.
5. **Constants/boundaries:** 1 is interior, 2 lies in X, and 0 is its boundary. Agreement on X does not extend to −1. At base 0 φ is nondifferentiable, so total fderiv's default zero is relevant to the value 6; this is not an ordinary derivative assertion there.
6. **Information/interpretation:** Demonstrates the distinction between agreement near an interior base and one-sided agreement at a boundary. The comparison is ambient differentiability, not a within-X derivative.
7. **Excluded claims:** No claim that all agreeing extensions give equal boundary divergences, no global equality, and no assertion ψ is nondifferentiable. Numeric equality does not establish implementation or helper-dependency evidence.

## Completion and unresolved item

All four complete let-bound types have been enumerated (16, 9, 14 and 9 top-level conjuncts), with prose, LaTeX and seven semantic slots. The sole unresolved context is the exact definition of SourceClosed in theorem 3. Its syntax, argument and conjunction scope are preserved without guessing. Consequently this is a complete syntactic reconstruction with that one explicitly unresolved semantic predicate, not a fully resolved semantic-context verdict. No extra file was read to resolve it.
