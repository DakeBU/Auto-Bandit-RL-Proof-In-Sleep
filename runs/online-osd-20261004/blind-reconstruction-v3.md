# Source-blind reconstruction of the v3 packet

Only blind-packet-v3.txt was read for this decoding. This report reconstructs its supplied semantics and unproved statement; it is not a source comparison, proof, compilation result, or independent human review.

## Seven semantic slots

1. **Ambient space and actual projection.** E is any finite-dimensional real inner-product space with its normed additive group structure. A Domain V supplies a nonempty, closed, real-convex carrier C contained in E. Denote its imported project operator by P_C. The packet identifies this operator as the actual classical choice of a nearest point, with
   \[
   P_C(z)\in C,\qquad
   \|z-P_C(z)\|=\inf_{w\in C}\|z-w\|.
   \]
   Finite-dimensionality supplies completeness. The operator is thus a genuine norm-minimizing projection onto C, not an unconstrained next-point symbol.

2. **Function hypotheses and global-support definition.** The function f : E -> EReal is proper in the exact sense
   \[
   (\forall y\in E, f(y)\ne-\infty)
   \land(\exists y_0\in E)(\exists r\in\mathbb R), f(y_0)=\operatorname{coe}(r).
   \]
   Its support set is exactly
   \[
   \partial f(v)=\{s\in E:\forall y\in E,
   f(v)+\operatorname{coe}(\langle s,y-v\rangle)\le f(y)\}.
   \]
   Tests range over every ambient point y. SubdifferentiableOn V f requires properness and a nonempty such support set at every v in C. This is an all-feasible-point hypothesis, not merely a condition at one query. There is no explicit global convexity, differentiability, or boundedness hypothesis on f. Convexity and closedness are explicit properties of C.

3. **Complete quantification and arbitrary ambient query.** Universally for every V and f satisfying the preceding condition, every real eta with eta>0, every x in E, every u in C, and every g in partial f(x), both inequalities in slot 5 hold. Crucially x is an arbitrary ambient query: there is no x in C hypothesis. The comparator u must be feasible. The supplied g is any actual global supporting vector at this x, not necessarily a particular algorithmically chosen support. The theorem requires existence of such g through its supplied membership witness, even when x is outside C. The all-feasible-point hypothesis by itself makes no assertion of support existence at an arbitrary infeasible x. No norm bound on g, horizon, time index, or loss sequence is present in this standalone theorem.

4. **Finite values justified independently at x and u.** Properness supplies y0 with an actual finite value coe(r). The given support membership hg at the possibly infeasible query x supplies its inequality with y0, excluding f(x)=+infinity; properness excludes f(x)=-infinity. Hence f(x) has an actual finite real witness. For u, feasibility and SubdifferentiableOn supply a support there, and the same finite-comparison-point reasoning yields a real witness for f(u). Therefore the displayed toReal difference is the genuine finite difference of these two witnesses. This explains the hypothesis semantics, not a checked formal proof. The packet explicitly says toReal maps both infinite endpoints to zero, so its unconditional use would not suffice. Properness alone would not ensure a finite value at every ambient query; the supplied hg matters. Positive infinity at other ambient points is permitted.

5. **Exact two-inequality conclusion.** For the arbitrary ambient x and the supplied g, let p=P_C(x-eta g), where eta g is scalar multiplication. The theorem asserts the conjunction
   \[
   \eta\bigl(\operatorname{toReal}(f(x))-\operatorname{toReal}(f(u))\bigr)
      \le \eta\langle g,x-u\rangle
   \]
   and
   \[
   \eta\langle g,x-u\rangle
      \le \frac{\|x-u\|^2}{2}
      -\frac{\|P_C(x-\eta g)-u\|^2}{2}
      +\frac{\eta^2}{2}\|g\|^2.
   \]
   Both inequalities use the same x, u, g, and strictly positive eta. The subtractive distance is from the actual projection of x-eta g to u. The initial distance, both factors one half, and eta squared in the correction are retained. These are single-step inequalities, not an equality or cumulative regret estimate. No feasibility of x is needed as a stated premise; feasibility of u and the actual projection geometry are present.

6. **Separate algorithm definitions and their structural information order.** currentSubgradient(f,x) is a noncomputable local-classical choice from partial f(x) if the set is nonempty; otherwise it is zero. The fallback has no asserted support property. Its arguments are the current function and current point, with no comparator, horizon, or future losses. It receives the whole function and uses a global support set, so this is not an executable local-value oracle specification. The algorithmic step is
   \[
   \operatorname{step}(V,\eta,f,x)
      =P_C(x-\eta\operatorname{currentSubgradient}(f,x)).
   \]
   For X_t=iterate V eta loss x1 t, the recursion is X_0=x1 and
   \[
   X_{t+1}=\operatorname{step}(V,\eta_t,\operatorname{loss}_t,X_t).
   \]
   Thus the parameter spelled x1 is the zero-indexed initial iterate. Structurally X_t uses earlier losses and step sizes, and the current loss_t updates it to X_{t+1}. No prefix-invariance or formal causality theorem accompanies this recursion. Initialization and the step-size schedule are external inputs, with no causal-generation requirements. The definitions do not require feasible initialization, positive step sizes, or subdifferentiable losses. Applying the standalone theorem to a selected step requires its actual premises, including a true support at the query; arbitrary infeasible initialization alone does not supply that support. The standalone theorem is more general in g than the selected update. Finally the regret definition is
   \[
   R_T(u)=\sum_{t=0}^{T-1}
      [\operatorname{toReal}(\operatorname{loss}_t(X_t))
       -\operatorname{toReal}(\operatorname{loss}_t(u))].
   \]
   It imposes no comparator-feasibility or finite-value premises itself, so outside additional hypotheses it is only a sum of real projections of extended-real values.

7. **Degenerate cases, exclusions, and scope.** Empty C is excluded by the Domain fields. Singleton and lower-dimensional feasible sets are allowed; there is no full-dimensionality or interior assumption. E may be zero-dimensional; then C contains its sole zero vector, properness forces the sole f value finite, all vectors and distances are zero, and both conclusions reduce to 0<=0. Eta=0 and negative eta are excluded by the theorem but accepted by the definitions. T=0 yields the empty regret sum. There are no global boundedness, differentiability, loss-convexity, Lipschitz, or support-norm hypotheses in the theorem. It makes no blanket support-existence claim outside C; a particular outside query is covered when hg is supplied. The packet supplies enough semantics to interpret the statement, but no theorem proof, compilation evidence, prefix theorem, all-round invariant theorem, telescoping result, regret guarantee, convergence guarantee, or step-size recommendation. No source identity or source fidelity can be determined from it.

## Evidence boundary

This v3 report and its receipt are the only files written in this decoding. No earlier packet, report, receipt, reviewer output, or external source was read or changed. Requested model and medium reasoning effort record the assignment request, not independent verification of runtime identity.
