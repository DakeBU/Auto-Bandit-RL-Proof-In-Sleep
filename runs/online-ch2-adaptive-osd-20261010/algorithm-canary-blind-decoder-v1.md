# Algorithm canary neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no runtime model or effort attestation. This actor has related staged decoder history and prior shared-API exposure, including the previously disclosed incidental neighboring proof line, not used as proof evidence. This is source-withheld mathematical decoding, not absolute blindness, human/external review, source matching or proof acceptance. Only the specified packet was read this turn. No theorem proof, build or compilation was run.

## Complete context and fixtures

The generic recursion uses a finite-dimensional real inner-product space E, with its normed additive group structure, and a Domain whose carrier is nonempty, closed and convex. These canaries instantiate E=ℝ. V has carrier [0,1]; W has carrier {0}. Projection is the unique nearest-point projection.

For fixed domain U, real α,D, loss stream f, initial point a and policy p:
\[
A_0=((i\mapsto a),0),\quad H_t=(A_t).1,\quad Q_t=(A_t).2,\quad X_t=H_t(t),
\]
\[
G_t=p(t,(f_i)_{i<t},H_t,f_t),\qquad R_t=\frac{\alpha D}{\sqrt{Q_t+\|G_t\|^2}},
\]
\[
A_{t+1}=\left(\operatorname{snoc}\left(H_t,
\begin{cases}X_t,&G_t=0,\\P_U(X_t-R_tG_t),&G_t\ne0,\end{cases}\right),Q_t+\|G_t\|^2\right),
\]
\[
L_T\iff\forall t<T,\ G_t\in\partial f_t(X_t),\qquad
F(u,T)=\sum_{t=0}^{T-1}(\operatorname{toReal}f_t(X_t)-\operatorname{toReal}f_t(u)).
\]
History H_t has t+1 entries. The policy interface accepts full strict-past loss functions, the full actual history through the current point, and the current whole loss function, after the current action exists. The function type itself does not encode history feasibility. Zero selected feedback skips projection. Real division is total, including division by zero.

The supplied support is global:
\[
\partial f(z)=\{g:\forall y,\ f(z)+(\langle g,y-z\rangle:\mathrm{EReal})\le f(y)\}.
\]
SourceProper means no bottom value anywhere and some embedded real value somewhere. SubdifferentiableOn U f means SourceProper and nonempty global support at every point of U. IsConvexExtended means convexity over ℝ of {(z,c)∈E×ℝ:f(z)≤(c:EReal)}, with real epigraph heights. Its definition alone does not exclude either infinity.

Define the concrete feedback sequence and fixtures:
\[
v_t=\begin{cases}3,&t=1,\\-4,&t=3,\\0,&\text{otherwise},\end{cases}
\quad f_t(z)=(v_tz:\mathrm{EReal}),\quad p(t,past,h,f)=v_t.
\]
\[
f'_t(z)=\begin{cases}f_t(z),&t<2,\\7,&t\ge2,\end{cases}
\qquad f^0_t(z)=0,\qquad p^0(t,past,h,f)=0.
\]
Thus the concrete p ignores all inputs except time; p⁰ ignores every input. The packet asserts no universal off-path OracleLaw for p.
\[
x_\alpha(t)=X(V,\alpha,1,f,\tfrac12,p,t),\
q_\alpha(t)=Q(V,\alpha,1,f,\tfrac12,p,t),\
r_\alpha(t)=R(V,\alpha,1,f,\tfrac12,p,t).
\]
Lastly B(A,S,η)=A/(2η)+ηS/2 is a scalar definition, distinct from the recursion A. Its coefficient-value sets below quantify only η>0.

## certificate_1 — three conjuncts

1. Objects: arbitrary real Domain U, time t, the concrete linear extended-real function f_t, and its global supports.
2. Quantifiers: ∀U:Domain(ℝ), ∀t:ℕ; the third conjunct then quantifies ∀z:ℝ.
3. Assumptions: only U's built-in nonempty closed convex structure; no additional restriction on t, z, diameter or feasibility of z.
4. Complete conclusion:
\[
\operatorname{IsConvexExtended}(f_t)
\ \land\ \operatorname{SubdifferentiableOn}(U,f_t)
\ \land\ \forall z\in\mathbb R,\ v_t\in\partial f_t(z).
\]
In prose, every concrete loss has a convex real epigraph, is proper and has global support at every U-feasible point, and its stated slope is a support at every ambient real point.
5. Constants/indices: slopes 3 at index 1, −4 at index 3, zero at all other indices; no finite-horizon restriction.
6. Information: this is a property of the fixed functions and vectors, not a universal law for p on arbitrary current functions.
7. Boundaries/evidence: includes the zero-slope constant losses and arbitrary U; no proof body supplied.

## certificate_2 — two universally quantified conjuncts

1. Objects: actual selected feedback and energy of the concrete V,D=1,a=1/2,p run, with arbitrary real α.
2. Quantifiers: first conjunct ∀α:ℝ,∀t:ℕ; second independently ∀α:ℝ,∀T:ℕ, with implication T≤4.
3. Assumptions: no sign condition on α; only the second conjunct's T≤4 restriction.
4. Complete conclusion:
\[
(\forall\alpha\in\mathbb R,\forall t\in\mathbb N,\
G(V,\alpha,1,f,\tfrac12,p,t)=v_t)
\]
\[
\land\quad
\left(\forall\alpha\in\mathbb R,\forall T\in\mathbb N,\ T\le4\Rightarrow
q_\alpha(T)=
\begin{cases}
0,&T\le1,\\
9,&1<T\le3,\\
25,&3<T\le4
\end{cases}\right).
\]
The first assertion is all-time; the second gives the exact finite energy table.
5. Constants/indices: Q_T counts feedback indices strictly below T. Thus T=0,1 give 0; T=2,3 give 9; T=4 gives 25.
6. Information: selected feedback is time-fixed and independent of history in this concrete policy, so this assertion is not a claim that arbitrary policies have α-independent energy.
7. Boundaries/evidence: zero and negative α are included. The second conjunct does not assert an energy formula for T>4. Header only.

## certificate_3 — thirteen conjuncts

1. Objects: actual α=1 trajectory, step values, cumulative comparator-0 difference, terminal distance and a concrete projection.
2. Quantifiers: a closed proposition; no universally quantified α, t, T or comparator.
3. Assumptions: none beyond the fixed definitions; this is a numerical fixture, not an implication with supplied trajectory values.
4. All thirteen conjuncts:
\[
x_1(0)=\tfrac12\ \land\
x_1(1)=\tfrac12\ \land\
x_1(2)=0\ \land\
x_1(3)=0\ \land\
x_1(4)=\tfrac45
\]
\[
\land\ r_1(0)=0\ \land\
r_1(1)=\tfrac13\ \land\
r_1(2)=\tfrac13\ \land\
r_1(3)=\tfrac15
\]
\[
\land\ F(V,1,1,f,\tfrac12,p,0,4)=\tfrac32
\ \land\ |x_1(4)-0|^2=\tfrac{16}{25}
\]
\[
\land\ P_V(-\tfrac12)=0\ \land\ (-\tfrac12:\mathbb R)\ne0.
\]
In prose, five actions, four steps, the complete four-round score, terminal squared distance, projection value and nonzero preprojection point are all asserted together.
5. Constants/indices: the zero vector at t=2 skips updating even though r_1(2)=1/3 is nonzero. Steps use inclusive energies 0,9,9,25. The score uses actions 0,…,3, while the terminal distance uses action 4.
6. Information: these are outputs of the actual recursive definitions. The projection conjunct distinguishes a changed point from an identity update; the initial half is fixed.
7. Boundaries/evidence: zero initial energy is handled by total division. No general-time formula, alternative α trajectory or all-comparator score identity is included. Header only, no proof supplied.

## certificate_4 — four conjuncts

1. Objects: two actual trajectories with α=1 and α=√2/2, and a fixed scalar coefficient set.
2. Quantifiers: closed proposition. Only the last set contains ∃η:ℝ with η>0.
3. Assumptions: no external premises; fixtures have D=1, initial 1/2, comparator 0, horizon 4 and fixed p.
4. All four conjuncts:
\[
F(V,1,1,f,\tfrac12,p,0,4)\le\tfrac{59}{10}
\ \land\
F(V,1,1,f,\tfrac12,p,0,4)\le\tfrac{15}{2}
\]
\[
\land\
F(V,\sqrt2/2,1,f,\tfrac12,p,0,4)\le\sqrt{50}
\]
\[
\land\
\sqrt{50}=\sqrt2\,
\operatorname{sInf}\{b\in\mathbb R:\exists\eta>0,\ b=B(1,25,\eta)\}.
\]
These are two bounds for the α=1 score, one bound for the different α=√2/2 score, and an exact scalar-infimum equality.
5. Constants/indices: B(1,25,η)=1/(2η)+25η/2. The real value set over positive η is nonempty and bounded below. The header does not assert score equality across the two α values or between any score and an upper bound.
6. Information: the final infimum varies a scalar η with 1 and 25 fixed; it does not rerun either learner, change its history or optimize its realized score.
7. Boundaries/evidence: both coefficient inputs are strictly positive here, so this is not a zero-energy scalar instance. The first two rational bounds remain separate conjuncts. No proof or source interpretation supplied.

## certificate_5 — three conjuncts

1. Objects: the complete state pair A at time 2 for the original and modified-future loss streams, with common V,α=1,D=1,a=1/2,p.
2. Quantifiers: closed proposition, containing equalities and inequality of functions ℝ→EReal.
3. Assumptions: none; f′ is defined by the explicit time cutoff.
4. All three conjuncts:
\[
A(V,1,1,f,\tfrac12,p,2)=A(V,1,1,f',\tfrac12,p,2)
\quad\land\quad f_2\ne f'_2
\quad\land\quad f_1=f'_1.
\]
The first is equality of the entire three-entry action history and energy, not only the last action. The next clauses assert whole-function disagreement at time 2 and agreement at time 1.
5. Constants/indices: f′ agrees for t<2 and is constantly 7 from t=2 onward. In particular f_2 is constantly zero, not constantly 7. The state at time 2 has processed losses 0 and 1.
6. Information: common parameters and policy are fixed; no equality of current losses at index 2 is required for equality of that state. No generic theorem over arbitrary policy replacements is asserted.
7. Boundaries/evidence: no infinite-trajectory equality or later-state inequality is a conjunct. The policy ignores current loss, so function disagreement alone would not justify such an inequality. Header only.

## certificate_6 — five conjuncts

1. Objects: zeroLoss and zeroPolicy on V, α=D=1, initial 1/2; comparator 0 for the numerical horizon-4 clauses.
2. Quantifiers: first conjunct ∀t:ℕ; second independently ∀T:ℕ; the remaining three are closed numerical assertions.
3. Assumptions: none beyond the concrete zero fixtures.
4. All five conjuncts:
\[
(\forall t\in\mathbb N,\ X(V,1,1,f^0,\tfrac12,p^0,t)=\tfrac12)
\ \land\
(\forall T\in\mathbb N,\ Q(V,1,1,f^0,\tfrac12,p^0,T)=0)
\]
\[
\land\ F(V,1,1,f^0,\tfrac12,p^0,0,4)=0
\ \land\ |X(V,1,1,f^0,\tfrac12,p^0,4)-0|^2=\tfrac14
\ \land\ F(V,1,1,f^0,\tfrac12,p^0,0,4)\le0.
\]
The equality and inequality of the score are both retained.
5. Constants/indices: actions and energies are quantified all-time, including zero; score and nonzero terminal squared distance use horizon 4.
6. Information: zero feedback always selects the skip branch; zero energy does not make the terminal point equal to comparator 0.
7. Boundaries/evidence: denominator zero is handled by total division, and the distance can be nonzero despite zero score and energy. These clauses do not assert this behavior for every loss stream or policy. Header only.

## certificate_7 — five conjuncts

1. Objects: singleton domain W={0}, α=1,D=0, initial 0, original f and time-fixed p, comparator 0 and horizon 2.
2. Quantifiers: closed proposition, no universal policy, time or α range.
3. Assumptions: none beyond the singleton fixture and other supplied definitions.
4. All five conjuncts:
\[
X(W,1,0,f,0,p,2)=0
\ \land\ Q(W,1,0,f,0,p,2)=9
\ \land\ G(W,1,0,f,0,p,1)=3
\]
\[
\land\ F(W,1,0,f,0,p,0,2)=0
\ \land\ F(W,1,0,f,0,p,0,2)\le0.
\]
This is a zero-diameter instance with nonzero selected feedback and positive accumulated energy.
5. Constants/indices: the vector 3 is selected at time 1 and contributes its square to energy at time 2. D=0 does not force Q_2=0. Both score equality and its inequality are explicit.
6. Information: the actual update has zero numerator in its step, and projection onto the singleton retains 0; no information restriction or legality assertion for arbitrary current functions is added.
7. Boundaries/evidence: the zero-diameter case is distinct from the zero-energy fixture in certificate_6. It makes no all-time energy assertion or claim that every support vector vanishes. Header only.

## Completeness and evidence

Conjunct counts are respectively 3, 2, 13, 4, 3, 5, 5, counting each top-level mathematical clause and retaining the internal universal ranges. Seven complete certificates were reconstructed. All notation required to interpret the fixture is supplied or explicitly carried in the displayed definitions. No unresolved type/semantic ambiguity remains.

These are proposed statements, not evidence of theorem-body correctness, actual compilation, source fidelity or algorithmic optimality. No extra file was read, no proof was written, and no existing file was edited.
