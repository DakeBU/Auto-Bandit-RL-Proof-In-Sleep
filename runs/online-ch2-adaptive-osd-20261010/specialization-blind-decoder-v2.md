# Specialization neutral reconstruction — v2

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no runtime attestation. This actor has related staged history and previously read shared source-named API definitions. This is source-withheld reconstruction, not absolute source/context blindness, human/external review, source matching or proof acceptance. The earlier incidental adjacent API proof-line exposure remains a disclosed history limitation, not proof evidence used here.

Only this turn's specified neutral packet was read. Shared Domain, support/properness and canonicalPolicy interpretations are reused from the prior algorithm report (SHA256 07c34e00be6567973944e6185f6e777ae0914b477ef0c5a1d3420322343e2138) and bootstrap report (SHA256 bead2a3bb7dd7e6fdd946d871cee2e8feab81f6c66cc5a0dd730da5e31237253), not reread. The v1 imported-predicate gap is resolved by the appended exact definitions in this v2 packet. The four headers are unchanged in the displayed version; this turn adds context interpretation, not new hypotheses or target conclusions. V1 output files are preserved.

## Context and the eight supplied definitions

E : Type* carries NormedAddCommGroup E, InnerProductSpace ℝ E, and FiniteDimensional ℝ E. There is no nontriviality assumption. Domain V supplies a nonempty closed convex carrier K. Its projection is denoted P_K.

For identical external V,α,D,f,x₁,p, the packet defines the finite history and energy recursively:
\[
A_0=((i\mapsto x_1),0),\quad H_t=(A_t).1,\quad Q_t=(A_t).2,\quad X_t=H_t(t),
\]
\[
G_t=p(t,(f_i)_{i<t},H_t,f_t),\qquad
R_t=\frac{\alpha D}{\sqrt{Q_t+\|G_t\|^2}},
\]
\[
A_{t+1}=\left(\operatorname{snoc}\left(H_t,
\begin{cases}X_t,&G_t=0,\\ P_K(X_t-R_tG_t),&G_t\ne0,\end{cases}\right),
Q_t+\|G_t\|^2\right),
\]
\[
L_T\iff\forall t<T,\ G_t\in\partial f_t(X_t),\qquad
F(u,T)=\sum_{t=0}^{T-1}\left(\operatorname{toReal}f_t(X_t)-\operatorname{toReal}f_t(u)\right).
\]
The history H_t has type Fin(t+1)→E. The policy receives all strict-past full loss functions, the actual history including X_t, and the current full function. It has no comparator argument. The feedback is selected after X_t exists; inclusive energy and step then determine X_{t+1}. Total real division handles a zero denominator.

The reused exact support interpretation is
\[
g\in\partial f(x)\iff
\forall y\in E,\quad f(x)+(\langle g,y-x\rangle:\overline{\mathbb R})\le f(y).
\]
SubdifferentiableOn V f means that f never equals bottom anywhere, has some finite real value somewhere, and has a nonempty global support set at every x∈K. Thus support is ambient, not restricted to feasible comparators. Under feasibility/regularity these hypotheses give the finite-value interpretation of the losses whose toReal values occur. Infinite values outside K are not thereby excluded.

The appended exact imported definitions resolve the earlier gap:
\[
\operatorname{realEpigraph}(f)=\{(x,r)\in E\times\mathbb R:f(x)\le(r:\overline{\mathbb R})\},
\qquad
C(f)=\operatorname{IsConvexExtended}(f)
\iff \operatorname{Convex}_{\mathbb R}(\operatorname{realEpigraph}(f)).
\]
Explicitly, for every x,y∈E, r,s∈ℝ with f(x)≤r and f(y)≤s, and every a,b∈ℝ with a≥0, b≥0 and a+b=1, one has
\[
f(ax+by)\le(ar+bs:\overline{\mathbb R}).
\]
These are ambient points, not only points of K, and real heights, not arbitrary EReal heights. Coefficients zero and one are allowed. This set-convexity formulation avoids guessing multiplication conventions at infinite function values: an x with f(x)=+∞ contributes no finite-height epigraph point, while f(x)=−∞ contributes every real height. Thus convexity alone does not assert properness, finite values, nonempty epigraph, or exclusion of either infinity; the separate properness and support assumptions retain their force. This is not convexity of toReal(f) or merely convexity on K. The appended material supplies definition bodies as notation context, not theorem proof bodies.

The reused exact canonical policy is
\[
p_{\mathrm{can}}(t,past,h,f)=\operatorname{currentSubgradient}(f,h(t)).
\]
The latter chooses a global support vector by Classical.choose if the support set is nonempty, otherwise returns zero. It ignores past loss functions and history entries other than the last. It is not asserted to be a gradient, unique vector, or executable numerical oracle.

## certificate_1

1. **Objects.** The actual run with α=1, arbitrary fixed policy p, real D, extended-valued loss stream f, feasible initial point and fixed feasible comparator u. E and V have the complete shared context above.
2. **Quantifier order.** ∀V; ∀D:ℝ; hD:0≤D; ∀f:ℕ→E→EReal; ∀x₁:E; ∀p:SupportPolicy; hx₁:x₁∈K; ∀T:ℕ; hconvex:∀t<T,C(f_t); hloss:∀t<T,SubdifferentiableOn V f_t; hlegal:L(V,1,D,f,x₁,p,T); hdiam:∀x∈K,∀y∈K,‖x−y‖≤D; ∀u:E; hu:u∈K.
3. **Assumptions.** Nonnegative D; initial and comparator membership; extended convexity and proper/global-support regularity throughout the played prefix; actual-prefix legality of this p on this α=1 run; global feasible diameter bound. There is no all-input OracleLaw assumption, differentiability, positive T, or positive D assumption.
4. **Full conclusion.** This run's cumulative loss difference against each feasible fixed comparator is bounded by three halves times the scale times the square root of its own accumulated energy:
\[
\sum_{t=0}^{T-1}\left(\operatorname{toReal}f_t(X_t^{1,p})-\operatorname{toReal}f_t(u)\right)
\le \frac32 D\sqrt{Q_T^{1,p}}.
\]
Here superscripts explicitly retain the same α and policy on both sides.
5. **Constants and indices.** α is exactly 1; coefficient 3/2 is a real quotient. Q_T accumulates the actual vectors at indices 0,…,T−1. There is no division by T, comparator minimum, or negative terminal term in this conclusion.
6. **Information.** p is fixed across this run; legality is only at its actual prefix histories. Current full f_t is available when G_t is selected, but after X_t is produced. The statement does not constrain how p or other external parameters were chosen.
7. **Boundaries/evidence.** T=0 gives the empty sum and Q_0=0; prefix assumptions are vacuous while structural/membership/diameter assumptions remain. D=0 is allowed and the zero-diameter feasible set is a singleton. Zero Q_T gives right side zero but does not by itself assert equality of all losses or F=0. Zero gradients skip projection; zero inclusive energy gives totalized step zero. Header only, no theorem body or compilation supplied.

## certificate_2

1. **Objects.** The same α=1 dynamics, now with the concrete canonical policy throughout F and Q; no arbitrary policy binder.
2. **Quantifier order.** ∀V; ∀D:ℝ; hD:0≤D; ∀f; ∀x₁:E; hx₁:x₁∈K; ∀T:ℕ; hconvex:∀t<T,C(f_t); hloss:∀t<T,SubdifferentiableOn V f_t; hdiam:∀x∈K,∀y∈K,‖x−y‖≤D; ∀u:E; hu:u∈K.
3. **Assumptions.** The same nonnegative scale, initial/comparator membership, prefix extended convexity and proper/support regularity, and feasible diameter bound as certificate_1. There is no externally supplied hlegal or OracleLaw premise. This removal accompanies substitution of p_can, not a claim that every arbitrary policy is automatically legal.
4. **Full conclusion.**
\[
F(V,1,D,f,x_1,p_{\mathrm{can}},u,T)
\le \frac32 D\sqrt{Q(V,1,D,f,x_1,p_{\mathrm{can}},T)}.
\]
This bounds the canonical run's cumulative fixed-comparator difference by its own energy.
5. **Constants and indices.** α=1, coefficient 3/2, horizon range 0,…,T−1; no averaging or terminal correction. Energy and actions must be those of p_can.
6. **Information.** The particular selector consumes current f_t and the actual last point; its support-choice definition is why this statement can specify a concrete policy without requiring the user to supply a separate legality premise. The header does not provide a proof of that justification.
7. **Boundaries/evidence.** T=0, D=0 and Q_T=0 are admitted with the same total arithmetic and empty-sum conventions. The selector's empty-support fallback is part of its total definition, not a claim of legality outside regular feasible cases. No proof or compilation supplied.

## certificate_3

1. **Objects.** The actual run with fixed α=√2/2, arbitrary fixed p, scale D, loss stream, initial point and comparator.
2. **Quantifier order.** ∀V; ∀D:ℝ; hD:0≤D; ∀f; ∀x₁:E; ∀p:SupportPolicy; hx₁:x₁∈K; ∀T:ℕ; hconvex:∀t<T,C(f_t); hloss:∀t<T,SubdifferentiableOn V f_t; hlegal:L(V,√2/2,D,f,x₁,p,T); hdiam:∀x∈K,∀y∈K,‖x−y‖≤D; ∀u:E; hu:u∈K.
3. **Assumptions.** Exactly the corresponding prefix and membership/diameter assumptions, with legality evaluated on the √2/2 run. No premise compares this run with the α=1 run. α is not a universally quantified variable in this header.
4. **Full conclusion.**
\[
F(V,\sqrt2/2,D,f,x_1,p,u,T)
\le D\sqrt{\,2Q(V,\sqrt2/2,D,f,x_1,p,T)\,}.
\]
The sum defining F is the complete cumulative current-action minus fixed-comparator real-loss sum on this same run.
5. **Constants and indices.** α=Real.sqrt 2/2, a strictly positive fixed real. The factor 2 is inside the square root in the exact conclusion. Same horizon T and same policy appear on both sides. The statement does not assert an inequality between the energies generated by the two α choices.
6. **Information.** Actual-prefix legality, not universal off-path legality. Changing α can change the action history, selected vectors and energy, even with the same policy function and loss stream; the different constant alone is not a comparison of numerical performance between runs.
7. **Boundaries/evidence.** T=0, D=0, zero feedback and zero total energy remain allowed. Nonnegative D does not mean positive steps when the numerator or inclusive energy vanishes. No asymptotic or minimax optimality assertion occurs; header only.

## certificate_4

1. **Objects.** The canonical run specialized to α=√2/2, with the common finite-dimensional domain context.
2. **Quantifier order.** ∀V; ∀D:ℝ; hD:0≤D; ∀f; ∀x₁:E; hx₁:x₁∈K; ∀T:ℕ; hconvex:∀t<T,C(f_t); hloss:∀t<T,SubdifferentiableOn V f_t; hdiam:∀x∈K,∀y∈K,‖x−y‖≤D; ∀u:E; hu:u∈K.
3. **Assumptions.** Nonnegative D, feasible initial/comparator, all played-prefix extended convexity and proper/global-support regularity, and full feasible diameter bound. Neither arbitrary p nor explicit hlegal/OracleLaw occurs.
4. **Full conclusion.**
\[
F(V,\sqrt2/2,D,f,x_1,p_{\mathrm{can}},u,T)
\le D\sqrt{\,2Q(V,\sqrt2/2,D,f,x_1,p_{\mathrm{can}},T)\,}.
\]
The comparator is fixed in the sum and universally quantified over K; no hindsight minimum or existence of a minimizing comparator is asserted.
5. **Constants and indices.** Exactly √2/2 in the recursion, exactly 2 multiplying its own Q_T inside the square root, and horizon indices 0,…,T−1. No loss at T is assumed regular.
6. **Information.** This is a concrete selector instance rather than an arbitrary-policy result without legality. It uses current full loss and last actual point, and it is the same selector in the actual recursion, score and energy.
7. **Boundaries/evidence.** Includes zero horizon, zero diameter, zero energy and zero-dimensional E. Zero diameter does not force all selected support vectors to be zero. No randomization, expectation, ordinary limit, oracle computation or source correspondence is claimed. Header only.

## Scope, v1 gap resolution and evidence

All four headers retain hconvex explicitly; it must not be silently dropped merely because other assumptions may suffice for a bound. They are finite, same-run, all-feasible-fixed-comparator statements. There is no uniform energy upper bound, learning-rate optimization theorem, sublinear-rate conclusion or probability law supplied. Externally choosing p, x₁, V or D using future information is not excluded by their types; causal comparisons require these external parameters to remain fixed.

V1 correctly left the expansion of IsConvexExtended unresolved. V2 appends realEpigraph and IsConvexExtended definitions and endpoint context; it changes no displayed certificate assumptions, conclusion or recursion. The exact expansion above resolves the only previously recorded semantic gap for all four hconvex premises. All four complete seven-slot reconstructions are retained in this report; no unresolved semantic/type context remains.

Only v2 was read this turn. No old file was reopened to claim a new bytewise comparison; preservation of the v1 packet prefix is supplied version context, while this report directly decodes the displayed v2 definitions and four headers. The old report and receipt were not modified. Eight recursion definitions and the two appended imported definitions are context; four headers have no theorem bodies. No compilation, proving or source-fidelity assessment was performed.
