# Neutral minimizer comparison: statement reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and reasoning effort are not independently attested. This is a reused staged automated decoder with earlier mathematical/project context, not a fresh source-naive, absolutely blind, human, or externally independent actor. Only the single supplied neutral file was consulted in this decode; no source or other repository context was read. The file supplies a proposed theorem header without a proof body. This report does not establish proof, compilation, or source fidelity.

## Natural-language reconstruction

Let E be any real normed vector space. Let V be a subset of E, f and h be real-valued functions on E, and p be a point of V. Assume f is convex on V, and that p minimizes f+h relative to every point in V. Suppose h has an ordinary ambient Fréchet derivative at p, given by a specified continuous real-linear functional h'. Then, for every u in V, the difference f(p)−f(u) is at most h' applied to the displacement u−p.

The condition IsMinOn compares the value at p with values on V; by itself it does not assert that p belongs to V. The independent hp premise explicitly supplies this membership.

## LaTeX reconstruction

For every real normed vector space E,
\[
\begin{aligned}
&\forall V\subseteq E,\ \forall f,h:E\to\mathbb R,\ \forall p\in E,\\
&p\in V,\quad \operatorname{ConvexOn}_{\mathbb R}(V,f),\quad
\bigl[\forall z\in V,\ f(p)+h(p)\le f(z)+h(z)\bigr],\\
&\forall h'\in\mathcal L_{\mathbb R}(E,\mathbb R),\quad
Dh(p)=h'\\
&\hspace{2em}\Longrightarrow
\forall u\in V,\quad f(p)-f(u)\le h'(u-p).
\end{aligned}
\]
Here \(\mathcal L_{\mathbb R}(E,\mathbb R)\) denotes continuous real-linear maps, and \(Dh(p)=h'\) denotes HasFDerivAt, not a presumed derivative notation for f. Formally the binders occur in order V,f,h,p,hp,hf,hmin,h',hd, followed by the universally quantified u and its membership hypothesis. The bundled ConvexOn premise includes convexity of V as well as convexity of f on that set.

## Seven semantic slots

1. **Objects:** An arbitrary E with NormedAddCommGroup E and NormedSpace R E; a set V⊆E; total real-valued functions f,h on E; a supplied p∈E; and a supplied continuous linear functional h':E→L[R]R. The conclusion concerns another arbitrary feasible point u. There is no inner product, gradient vector, projection, or extended-real objective in the statement.

2. **Quantifiers and order:** All ambient objects are universally quantified. The point p is supplied first, then its membership, convexity and minimization premises, then h' and its derivative premise. The conclusion holds for every u∈V using this same p,f,h,h'. There is no existential choice of a minimizer, derivative, or comparison point in the conclusion.

3. **Assumptions and regularity:** hp says p∈V. hf says ConvexOn R V f, including convex V. hmin means every z∈V satisfies (f+h)(p)≤(f+h)(z); it does not include membership. hd is ambient HasFDerivAt h h' p. It requires differentiability of h at this point, with the supplied continuous linear derivative, rather than only differentiability within V. No differentiability or continuity of f is separately assumed; no convexity of h or f+h is assumed; no global differentiability of h is assumed.

4. **Conclusion:** For every feasible u, f(p)−f(u)≤h'(u−p). The sign and order are exactly as written: the displacement is u−p and the difference is f at p minus f at u. The bound is for the f component, not a direct comparison of f+h, and uses derivative evaluation rather than an unprovided inner product with a gradient.

5. **Constants, normalization, and degenerate boundaries:** There are no numerical factors, denominators, step sizes, horizons, sums, or asymptotic normalizations. u=p is permitted and gives the zero-versus-zero comparison. V cannot be empty under hp; V may be a singleton or lower-dimensional set and p may lie on its boundary. V need not be open, closed, bounded, or compact. Zero-dimensional E is permitted. No interior-point premise on p is supplied.

6. **Information structure and existence scope:** The statement is deterministic; no law, seed, filtration, update rule, or temporal information order appears. Minimization is global over the supplied V, not merely local, and not necessarily over all E. A minimizing p with the listed properties is assumed, rather than produced. The theorem does not guarantee that such a point exists for arbitrary f,h,V. No uniqueness premise or conclusion is present. The only space structure is a real normed vector space: completeness, finite dimension, and an inner-product structure are not required.

7. **Excluded claims and proof boundary:** The header neither constructs a minimizer nor proves existence/uniqueness or an algorithmic convergence statement. It does not impose f differentiable, h convex, V closed, or E complete. It does not weaken hd to a derivative within V. Its proposed comparison has no supplied proof in this input, and neither imports nor the word “theorem” establish typechecking or source acceptance.

## Context sufficiency

The one header has been fully reconstructed. No unresolved type or semantic-context ambiguity was identified. The difference between IsMinOn's comparison condition and the explicit hp membership premise is retained. No source was consulted in this decode; no proof, compilation, or source verdict is given.

