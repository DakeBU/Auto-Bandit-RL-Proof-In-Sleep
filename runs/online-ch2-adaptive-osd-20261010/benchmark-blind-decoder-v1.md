# Benchmark neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, without runtime model/effort attestation. This is a reused staged source-withheld decoder with related context history, not an absolutely blind, human or external reviewer. Prior shared API interpretation and the previously disclosed incidental adjacent proof-line exposure are retained history; no proof evidence is inferred from them. Only the specified benchmark packet was read this turn. No source matching, proof or compilation assessment was performed.

## Definitions and context

The first four certificates concern only real scalars. They impose no learner, domain, probability, or information assumptions. The ambient section's E variables do not occur in these four closed scalar statements and are not needed to interpret them.

The scalar definition is total for A,S,η∈ℝ:
\[
B(A,S,\eta)=\frac{A}{2\eta}+\frac{\eta S}{2}.
\]
The argument A here is a scalar and distinct from the state recursion also named A. The certificates use A=D² and restrict the optimized scalar to η>0. Define explanatory notation
\[
\mathcal B(D,S)=\{b\in\mathbb R:\exists\eta\in\mathbb R,\ \eta>0\ \land\ b=B(D^2,S,\eta)\}.
\]
This is the image of the positive η domain under the scalar coefficient function, not the set of steps themselves, an inverse image, or a set of all numbers above a coefficient. No η=0 value belongs by that witness, even though B is defined there by total division.

IsGLB(𝓑,c) means c is a lower bound (∀b∈𝓑,c≤b) and every other real lower bound d satisfies d≤c. It does not mean c∈𝓑. The real sInf is a total operation; its meaningful greatest-lower-bound interpretation here is supported by a nonempty, bounded-below set: η=1 supplies an element, and for nonnegative D,S all positive-step values are nonnegative. No extended-real ±∞ infimum is used.

For certificate_5, E : Type* has NormedAddCommGroup E, InnerProductSpace ℝ E and FiniteDimensional ℝ E. V's carrier K is nonempty, closed and convex; P_K is its projection. No nontriviality assumption occurs. The packet's eight actual definitions, with fixed V,α,D,f,x₁,p, are
\[
A_0=((i\mapsto x_1),0),\quad H_t=(A_t).1,\quad Q_t=(A_t).2,\quad X_t=H_t(t),
\]
\[
G_t=p(t,(f_i)_{i<t},H_t,f_t),\qquad R_t=\frac{\alpha D}{\sqrt{Q_t+\|G_t\|^2}},
\]
\[
A_{t+1}=\left(\operatorname{snoc}\left(H_t,
\begin{cases}X_t,&G_t=0,\\P_K(X_t-R_tG_t),&G_t\ne0,\end{cases}\right),Q_t+\|G_t\|^2\right),
\]
\[
L_T\iff\forall t<T,\ G_t\in\partial f_t(X_t),\qquad
F(u,T)=\sum_{t=0}^{T-1}(\operatorname{toReal}f_t(X_t)-\operatorname{toReal}f_t(u)).
\]
H_t has t+1 entries. The policy sees strict-past full functions, actual action history including the current action, then current full f_t. A zero vector skips projection; the denominator otherwise uses inclusive current energy. Real division is total.

Reused shared semantics: ∂f(x) consists of g satisfying f(x)+(⟨g,y−x⟩:EReal)≤f(y) for every ambient y. SubdifferentiableOn V f requires no bottom anywhere, some finite real value somewhere, and a nonempty such global support set at every feasible point. The packet explicitly supplies extended convexity as convexity over ℝ of {(x,r)∈E×ℝ:f(x)≤(r:EReal)}. The heights are real; positive infinity contributes no such height, negative infinity every height. Convexity alone does not impose properness; the separate assumptions do. No convexity merely of toReal or merely on K is substituted.

## certificate_1

1. Objects: real D,S and the positive-step scalar value set 𝓑(D,S).
2. Quantifier order: ∀D,S:ℝ, followed by hD:0≤D and hS:0≤S.
3. Assumptions: both scalars nonnegative; no positivity or nondegeneracy.
4. Complete conclusion:
\[
\operatorname{IsGLB}\bigl(\mathcal B(D,S),D\sqrt S\bigr).
\]
In full ordinary language, D√S is below every positive-step coefficient value, and any real number below all those values is at most D√S. Both parts of greatest-lower-bound meaning are required.
5. Constants/indices: B(D²,S,η)=D²/(2η)+ηS/2, η>0. No time indices or finite sums.
6. Information/probability: a static scalar statement; D,S are fixed while η varies, with no random quantities or algorithm reruns in the type.
7. Boundaries/evidence: D=S=0, D=0<S and S=0<D are all included. The conclusion does not require attainment. Header only; no supplied proof.

## certificate_2

1. Objects: the same scalar value set and its real sInf.
2. Quantifier order: ∀D,S:ℝ; hD:0≤D; hS:0≤S.
3. Assumptions: nonnegative D,S only.
4. Complete conclusion:
\[
D\sqrt{2S}=\sqrt2\,\operatorname{sInf}\mathcal B(D,S).
\]
This is exact equality, not an inequality or a statement that a minimum exists.
5. Constants: factor 2 is inside the left square root, while √2 multiplies the right infimum. The set uses the same D²,S and positive η.
6. Information: S is fixed in the set as η varies. No learner, policy or probabilistic law is present.
7. Boundaries/evidence: either zero scalar makes both sides zero, including mixed-zero cases where attainment fails as classified below. The real nonempty/bounded-below setting is essential to interpreting sInf, rather than relying on empty-set conventions. Header only.

## certificate_3

1. Objects: existence of a strictly positive η attaining the scalar lower-bound value.
2. Quantifier order: ∀D,S:ℝ; hD:0≤D; hS:0≤S; the conclusion contains an existential η on the left of an equivalence.
3. Assumptions: only nonnegativity of D,S.
4. Full biconditional:
\[
\left(\exists\eta>0,\ B(D^2,S,\eta)=D\sqrt S\right)
\iff
\bigl((D>0\land S>0)\lor(D=0\land S=0)\bigr).
\]
Thus attainment occurs exactly in the strictly-positive pair or the both-zero pair.
5. Constants/domain: η ranges over positive reals, excluding η=0 and any putative infinite step. The equality is to D√S.
6. Information: pure scalar existence/classification; it supplies neither a learner nor a new realized trajectory.
7. Boundaries/evidence: mixed-zero pairs D=0<S and S=0<D have infimum zero but no positive attaining η. When both are zero, B=0 for every positive η by its formula; the header itself asserts existence, not uniqueness. No classification for negative D or S is claimed. Header only.

## certificate_4

1. Objects: strictly positive D,S, the candidate η*=D/√S, and all positive scalar η.
2. Quantifier order: ∀D,S:ℝ; hD:0<D; hS:0<S; then the conclusion's universally quantified η appears after its first two conjuncts.
3. Assumptions: strict positivity of both scalars. No other hypotheses.
4. Complete nested conclusion, retaining all four mathematical blocks:
\[
\eta_*=\frac D{\sqrt S}>0
\quad\land\quad
B(D^2,S,\eta_*)=D\sqrt S
\]
\[
\quad\land\quad
\forall\eta\in\mathbb R,\ \eta>0\Rightarrow
\left[
D\sqrt S\le B(D^2,S,\eta)
\ \land\
\bigl(B(D^2,S,\eta)=D\sqrt S\iff\eta=\eta_*\bigr)
\right].
\]
In prose: the displayed candidate is admissible; it attains the value; every positive η has at least that value; and equality for any positive η holds exactly at that candidate. The last two blocks are both inside the ∀η and positivity implication.
5. Constants/domain: denominator √S is strictly positive here. This is the positive minimum of the coefficient formula with factors 1/2, not an arbitrary regularized variant.
6. Information: D,S remain fixed during optimization; no dependence of S on η is supplied.
7. Boundaries/evidence: zero D or zero S are excluded, so the totalized candidate D/√S at a zero denominator is not claimed to attain anything by this header. Uniqueness concerns the positive scalar minimizer only. Header only.

## certificate_5

1. Objects: the actual finite-dimensional projected recursion at fixed α=√2/2, scale D, fixed p, loss stream f, feasible initial point, horizon T and fixed feasible comparator u. Let
\[
S_*:=Q(V,\sqrt2/2,D,f,x_1,p,T)
\]
denote the energy of this particular run; this is explanatory notation.
2. Quantifier order: ∀V; ∀D:ℝ; hD:0≤D; ∀f:ℕ→E→EReal; ∀x₁:E; ∀p:SupportPolicy; hx₁:x₁∈K; ∀T:ℕ; hconvex:∀t<T,IsConvexExtended(f_t); hloss:∀t<T,SubdifferentiableOn V f_t; hlegal:L(V,√2/2,D,f,x₁,p,T); hdiam:∀x∈K,∀y∈K,‖x−y‖≤D; ∀u:E; hu:u∈K.
3. Assumptions: nonnegative D, initial/comparator membership, global real-epigraph convexity and proper/global-support regularity on all played losses, actual-prefix legality of this fixed policy on this fixed-α run, and the diameter bound for the entire carrier. No positive horizon, strict D positivity, canonical-policy substitution, all-input OracleLaw, or energy upper bound is assumed.
4. Both complete conjuncts:
\[
F(V,\sqrt2/2,D,f,x_1,p,u,T)\le D\sqrt{2S_*}
\]
and
\[
D\sqrt{2S_*}=
\sqrt2\,\operatorname{sInf}
\left\{b\in\mathbb R:\exists\eta>0,\
b=\frac{D^2}{2\eta}+\frac{\eta S_*}{2}\right\}.
\]
The first is a same-run cumulative fixed-comparator bound. The second identifies its scalar upper-bound expression as √2 times a coefficient infimum, with exactly the same actual energy S_*.
5. Constants/indices: α remains √2/2 in every occurrence of F and Q; times summed are 0,…,T−1. The optimizing η is a separate bound variable appearing only in B, not a replacement of α or the sequence R_t. No terminal subtraction or division by T appears. The minimum candidate D/√S_* only has the strict-positive interpretation given by certificate_4.
6. Information: the actual policy sees strict-past functions, actual finite history and current loss in that order. u is absent from the recursion. The infimum does not rerun the algorithm for each η, recompute gradients, or let energy vary with η; it freezes S_* from the single fixed-α trajectory. It therefore does not assert performance relative to the best separate constant-step learner or to an optimized family of trajectories. External parameter choices are not constrained to exclude future information; causal comparisons require holding them and p fixed.
7. Boundaries/evidence: T=0 gives F=0 and S_*=0; loss-prefix assumptions are vacuous, but membership and diameter assumptions remain. D=0 gives a singleton feasible carrier and bound zero; selected vectors need not all vanish. If S_*=0 and D>0, the scalar infimum is zero and is not attained at a positive finite η. If D=0<S_*, the same nonattainment classification applies. If D=S_*=0 all positive η attain zero. If D,S_*>0 the unique positive coefficient minimizer is D/√S_*. Zero current feedback skips projection, and zero inclusive energy uses total division. Neither convexity alone nor toReal alone establishes finite losses; properness/support and feasible points supply that interpretation. Header only.

## Evidence and unresolved context

Five complete headers and nine definitions (eight dynamics definitions plus scalar B) were decoded, with the explicit imported convexity expansion. No theorem bodies, compilation result, source identity or reviewer conclusions were consulted. Standard IsGLB and real sInf meanings were interpreted directly; no extra files were read. No unresolved semantic/type ambiguity remains. These types propose scalar extremal characterizations and a finite performance conjunction; they do not themselves prove those claims or establish source fidelity.
