# Six neutral statements: reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, with runtime model and effort not independently attested. This automated actor has related staged history. This is source-withheld reconstruction, not absolute blindness, fresh-history independence, human review or external review. Only neutral-packet-v2.md was read for this task; no source or prior verdict was consulted. Names are identifiers, not evidence of source identity. These are proposed headers without proof bodies.

## Canonical context

Use ι:R→EReal for the real embedding. The effective domain is {z:f(z)<top}; this condition alone allows bottom. Proper(f) requires no bottom anywhere AND an ambient finite real witness. A global support at z is a vector g satisfying
\[
\forall y\in E,\quad f(z)+\iota(\langle g,y-z\rangle)\le f(y).
\]
Nonempty subdifferential at feasible z has order ∀z∈V ∃g ∀ambient y; comparisons are not restricted to V. Properness and such supports supply the intended finite feasible values, but not finiteness everywhere. toReal is total and sends infinities to zero; it is not a substitute for finiteness hypotheses.

The extended indicator is 0 on X and top outside X. SourceClosed(F) means every finite-real-threshold sublevel {z:F(z)≤ι(r)} is ambient closed. Thus for F=ι∘ψ+indicator X, those sets are {z∈X:ψ(z)≤r}; closedness is in E, not merely relative to X.

Write
\[
D(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}\psi(b))(a-b),\qquad
J_{\alpha,f,a}(z)=f(z)+\iota(\alpha^{-1}D(z,a)).
\]
D has its derivative base in the second argument. fderiv is total, defaulting to zero without differentiability. advance A(V,ψ,α,f,a) tests existence of p∈V with IsMinOn J V p, chooses such a p and returns some p if it exists, and returns none otherwise. IsMinOn compares all feasible objective values but does not itself include p∈V. iterate I starts at I0=some x0 and uses Option.bind with current α=η_t and f=loss t at step t. Hence I_(t+1) uses the current loss, while I_t consumes indices below t. Neither algorithm is a numerical implementation; choice is noncomputable.

No randomness or probabilistic information assumptions occur. All objects below are universally quantified unless an existential appears explicitly. No theorem body, attainment proof or compiler evidence is supplied.

## 1. sourceProper_of_domain

For any type E, any extended-real function f and nonempty subset V, if f never takes bottom anywhere and V is contained in its effective domain, then f is proper.
\[
\forall E,\ f:E\to\overline{\mathbb R},\ V\subseteq E,\quad
V\ne\varnothing\Rightarrow
(\forall z\in E,f(z)\ne-\infty)\Rightarrow
(\forall z\in V,f(z)<+\infty)\Rightarrow\operatorname{Proper}(f).
\]

1. **Objects:** E is merely Type*, with no topology, norm, vector structure, dimension or completeness assumptions.
2. **Quantifiers/order:** E,f,V,hV,hbot,hdom; conclusion contains the finite-witness existential from Proper.
3. **Assumptions:** Nonempty V, global no-bottom, and effective-domain inclusion. Neither inclusion alone nor no-bottom alone supplies a finite witness.
4. **Conclusion:** The same global no-bottom condition together with existence of an ambient point having a finite embedded real value.
5. **Boundaries:** Top is still allowed outside V; bottom is forbidden everywhere. Empty V is excluded. The effective domain definition is not “finite values” without hbot.
6. **Information:** Pure static existence implication; no minimizer, feedback or derivative.
7. **Excluded scope:** Does not produce a minimizer or assert convexity, closedness, all-ambient finiteness, or uniqueness.

## 2. penalized_strictConvex

In a real inner-product space, let V be convex and contained in X, let ψ be strictly convex on X, and let f be proper with global supports at every feasible point. For positive η and any ambient center a, the finite-part penalized objective is strictly convex on V:
\[
\operatorname{StrictConvexOn}_{\mathbb R}
\left(V,z\mapsto(f(z)).\mathrm{toReal}+\eta^{-1}D(z,a)\right).
\]

1. **Objects:** E with NormedAddCommGroup and InnerProductSpace R; V,X,ψ:E→R,f:E→EReal,η:R,a:E. No CompleteSpace or FiniteDimensional binder.
2. **Quantifiers/order:** V,X,hV,hVX,ψ,hψ,f,hf,hs,η,hη,a, all universal.
3. **Assumptions:** Convex V, V⊆X, strict convexity of ψ on X, proper f, ∀z∈V nonempty global support, η>0. No differentiability of f or ψ, no center membership or closedness requirement.
4. **Conclusion:** Strict convexity of the real objective on V, not a minimum-existence statement and not global strict convexity on all E.
5. **Constants/boundaries:** Coefficient is η⁻¹, no half factor. Zero and negative η are excluded. Center a may be outside X or at a nondifferentiable point of ψ: the frozen fderiv at a is still a continuous linear functional by total definition. Empty/singleton V are allowed by this header; strictness only compares distinct feasible points.
6. **Information:** Fixed current objective and center. Global support scope is all ambient y; supporting vectors can vary with feasible z.
7. **Excluded scope:** No attained minimum, coercivity, uniqueness theorem as a separate conclusion, or actual advance result is asserted. Strict convexity does not itself imply existence.

## 3. advance_eq_some_of_minimizer

In the additionally complete real inner-product space, under the same convexity/properness/support/positive-step assumptions, any supplied feasible minimizer p of the extended objective is exactly the point returned by advance.
\[
p\in V\ \land\ [\forall z\in V,\ J_{\eta,f,a}(p)\le J_{\eta,f,a}(z)]
\Longrightarrow A(V,\psi,\eta,f,a)=\mathrm{some}(p).
\]

1. **Objects:** E with normed additive, real inner-product and CompleteSpace structures; V,X,ψ,f,η,a,p. Finite dimension is not assumed.
2. **Quantifiers/order:** V,X,hV,hVX,ψ,hψ,f,hf,hs,η,hη,a,p,hp,hmin.
3. **Assumptions:** Every premise of statement 2 plus completeness, p∈V and actual extended-real global-over-V minimization. No ψ differentiability or center-feasibility premise.
4. **Conclusion:** Exact Option identity with the supplied p, stronger than merely existence of some successful point or feasibility of a selected point.
5. **Boundaries:** hp separately supplies membership absent from IsMinOn. It rules out empty V in a realized instance. Infinite values outside V are allowed; feasible values are controlled by properness/support. Positive η only.
6. **Information/uniqueness:** The conclusion identifies the same chosen advance with any p satisfying these premises, expressing uniqueness-compatible selection. It is conditional on a minimizer already supplied and does not construct its existence.
7. **Excluded scope:** No general attainment theorem, executable optimizer, finite-dimensional restriction or proof of the identity is supplied.

## 4. iterate_eq_of_source_updates

In the complete real inner-product context, suppose a supplied sequence starts at x0 and each of its next points is a feasible minimizer of that round's objective centered at its previous point. With positive played steps and proper globally supported current losses, it agrees with the canonical successful Option iterate through T.
\[
\begin{aligned}
&x_0^{\mathrm{seq}}=x0,\quad
\forall t<T,\ \eta_t>0,\ \operatorname{Proper}(\ell_t),\
[\forall z\in V,\partial\ell_t(z)\ne\varnothing],\\
&\forall t<T,\quad x_{t+1}\in V\ \land\
\operatorname{IsMinOn}(J_{\eta_t,\ell_t,x_t},V,x_{t+1})\\
&\Longrightarrow\forall t\le T,\quad I_t=\mathrm{some}(x_t).
\end{aligned}
\]
Common antecedents are convex V⊆X and strictly convex ψ on X.

1. **Objects:** Complete real inner-product E; V,X,ψ,step/loss streams,x0,sequence x:N→E and natural T.
2. **Quantifiers/order:** V,X,hV,hVX,ψ,hψ,η,loss,x0,x,T,hinit,hη,hf,hs,hmin, then every t≤T.
3. **Assumptions:** Shared domain/generator conditions; x 0=x0; played-step positivity; properness and supports for t<T; explicit membership AND IsMinOn for each actual supplied successor. No differentiability, interior or closedness premise.
4. **Conclusion:** Same sequence equals actual Option recursion at every prefix through T, including nonfailure. No equality past T is asserted.
5. **Boundaries:** T=0 is allowed and update/loss/step hypotheses are vacuous; only initialization matters for the result. Initial x0 need not be feasible. For positive steps the next state is feasible; η_T and later losses are unrestricted.
6. **Information:** Each x_(t+1) minimizes the current loss ℓ_t with center x_t; this is not a pre-current-loss predictor. The same η stream is used in both hypotheses and recursion.
7. **Excluded scope:** Does not prove such a supplied sequence exists, or that arbitrary feasible traces coincide with iterate. Minima are hypotheses, not generated by strict convexity alone.

## 5. source_fixed_regret

Now E has NormedAddCommGroup, InnerProductSpace R and FiniteDimensional R E. CompleteSpace is not a separately written binder in this wrapper. Fix constant η>0. In addition to convex nonempty closed V⊆X, assume strict convexity of ψ on X, closed sublevel sets of its indicator extension, and differentiability on interior X. A supplied sequence starts at x0, remains in interior X through T and makes the specified feasible minimizing updates. At each played round the loss is never bottom anywhere, is below top on V and has global supports on V. Then for every u∈V,
\[
\sum_{t<T}\left[(\ell_t(x_{t+1})).\mathrm{toReal}-(\ell_t(u)).\mathrm{toReal}\right]
\le\frac{D(u,x0)}{\eta}
-\frac{\sum_{t<T}D(x_{t+1},x_t)}{\eta}.
\]

1. **Objects:** Finite-dimensional real inner-product E; V,X,ψ,constant η,ℓ,x0,x,T and fixed feasible comparator u.
2. **Quantifiers/order:** V,X,hV,hVn,_hVc,hVX,ψ,hψ,_hψc,hd,η,hη,loss,x0,x,T,hinit,hinterior,hbot,hdom,hs,hmin,u,hu.
3. **Assumptions:** Include BOTH explicitly underscore-named conditions: IsClosed V and SourceClosed(ι∘ψ+indicator X). Underscores do not remove them. hbot is ∀t<T ∀ambient z,ℓ_t(z)≠bottom; hdom is ∀t<T V⊆{z:ℓ_t(z)<top}; V is nonempty. These supply properness without an explicit hf binder. Supports compare all ambient y. hmin includes x_(t+1)∈V and minimization of J with η⁻¹. Interior membership is for every t≤T and hd is DifferentiableOn ψ (interior X).
4. **Conclusion:** Unnormalized real cumulative finite-part difference against one fixed u, with initial divergence/η and one subtracted total movement term/η. No terminal comparator-divergence term is in this exact conclusion.
5. **Constants/boundaries:** T may be zero. Then the LHS and movement sum are empty; the RHS is D(u,x0)/η, not automatically zero. η stays strictly positive. x0 need not be in V but lies in interior X via hinit/hinterior. Comparator u need not be interior. No derivative of loss is required.
6. **Information:** This wrapper accepts explicit minimizing updates, not hseq as an input. Statement 4 describes the corresponding canonical-trajectory identity, but no proof of that bridge is supplied here. Current loss is evaluated at its post-minimization x_(t+1). Extended losses may equal top outside V.
7. **Excluded scope:** No attainment/existence conclusion, asymptotic no-regret, expectation, bounded-gradient hypothesis, or strict numerical inequality. Nonempty/closedness conditions remain part of the type even if a proof might not use them.

## 6. source_variable_regret

Use the same finite-dimensional domain and generator conditions. Let T>0 and steps be positive for t<T and nonincreasing across adjacent played steps. With the same initialization, interior, no-bottom/domain/support and feasible minimizing-update assumptions (now at η_t), every u∈V satisfies
\[
\sum_{t<T}\left[(\ell_t(x_{t+1})).\mathrm{toReal}-(\ell_t(u)).\mathrm{toReal}\right]
\le\frac{\max_{0\le t<T}D(u,x_t)}{\eta_{T-1}}
-\sum_{t<T}\frac{D(x_{t+1},x_t)}{\eta_t}.
\]

1. **Objects:** E with the three finite-dimensional wrapper structures, variable step stream, actual specified update sequence, positive horizon and one feasible u.
2. **Quantifiers/order:** V,X,hV,hVn,_hVc,hVX,ψ,hψ,_hψc,hd,η,loss,x0,x,T,hT,hη,hinit,hinterior,hmono,hbot,hdom,hs,hmin,u,hu.
3. **Assumptions:** All wrapper conditions described for statement 5, except steps vary. Positivity is only ∀t<T,η_t>0. Monotonicity is ∀t,t+1<T→η_(t+1)≤η_t. The objective uses (η_t)⁻¹. Closedness and SourceClosed remain explicit. Neither loss differentiability nor minimizer uniqueness is an extra premise.
4. **Conclusion:** Finset.sup' over range T is the exact finite nonempty maximum of comparator divergence at x0,…,x_(T−1), divided by the last played step η_(T−1), minus the movement terms with their own denominators.
5. **Constants/boundaries:** T>0 provides the nonempty-range witness; there is no T=0 clause or default maximum. Terminal x_T is excluded from the maximum. At T=1 it reduces to D(u,x0)/η0 minus the single movement term/η0; monotonicity is vacuous. η_T is irrelevant. There is no 1/2 factor or normalization by T.
6. **Information:** Maximum is on this same η-dependent supplied minimizing trajectory for this comparator, not a separately tuned run or an all-path constant. Current losses feed their corresponding updates; no stochastic or adversarial generation rule is encoded.
7. **Excluded scope:** Cannot replace the maximum by initial divergence without a new premise. No all-time convergence, success without supplied minimizers, production proof or source acceptance is asserted.

## Completeness and anomalies

All six scoped statements are reconstructed with seven slots and all eight supplied canonical definitions accounted for. No unresolved semantic-context issue or apparent scope anomaly was identified. Typeclass distinctions are retained: statement 1 needs no structure, statement 2 a real inner-product space without completeness, statements 3–4 explicit completeness, and statements 5–6 explicit finite dimension without a separately written CompleteSpace binder. The proposed strictness/uniqueness-compatible selection and trajectory bridges do not establish attainment; the wrappers retain every minimum hypothesis. No theorem proof or source verdict is supplied.
