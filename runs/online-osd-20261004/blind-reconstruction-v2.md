# Source-blind reconstruction: v2 semantic packet

This independent reconstruction uses only blind-packet-v2.txt. The packet supplies shared interface semantics and an unproved theorem statement. No source identity, theorem proof, implementation outside the packet, or other review was consulted. This is a distinct automated decoding, not a human review or compilation result.

## Seven semantic slots

1. **Spaces, feasible set, and actual projection.** E is any finite-dimensional real inner-product space with its normed additive group structure. A Domain V consists of a carrier C contained in E, with explicit nonemptiness, closedness, and real convexity. Write P_C for the packet's actual imported project V. It is defined by classical choice from a nearest-point existence result, with the supplied specification
   \[
   P_C(z)\in C,\qquad
   \|z-P_C(z)\|=\inf_{w\in C}\|z-w\|.
   \]
   Finite-dimensionality supplies completeness. Thus P_C is an actual norm-minimizing feasible projection, not a free next-point variable. These geometric assumptions on C are distinct from assumptions on the loss function.

2. **Proper function and all-feasible-point subdifferentiability.** For f : E -> EReal, properness means
   \[
   (\forall y\in E, f(y)\ne-\infty)
   \land(\exists y_0\in E)(\exists r\in\mathbb R), f(y_0)=\operatorname{coe}(r).
   \]
   The exact support set is
   \[
   \partial f(v)=\{g\in E:\forall y\in E,
     f(v)+\operatorname{coe}(\langle g,y-v\rangle)\le f(y)\}.
   \]
   Every test point is ambient and unrestricted; the support inequality is global. SubdifferentiableOn V f is the conjunction of properness and nonemptiness of this set for every v in C. It is not merely support existence at the current x, nor existence of a local or feasible-set-only support. No explicit global convexity or differentiability hypothesis on f is stated.

3. **Quantifiers, current query, and comparator.** Universally for every such E and V, every f satisfying the preceding conjunction, every real eta with eta>0, every x,u in C, and every g in partial f(x), the theorem asserts both inequalities in slot 5. The current query is x, u is an arbitrary feasible comparator, and g is any given true global supporting vector at x. It need not equal the particular currentSubgradient choice. No bound on its norm is assumed. Eta is strictly positive; zero and negative eta are not theorem instances. No time index, horizon, schedule, sequence, or initial condition is quantified in this one-step theorem.

4. **Actual finite values before toReal.** Properness supplies an actual finite comparison value f(y0)=coe(r), although y0 need not be feasible. At every feasible v there is a global support s. Its comparison with y0 excludes f(v)=+infinity, since adding the finite inner product to +infinity cannot be at most the finite r. Properness separately excludes f(v)=-infinity. Hence every feasible v has a real witness a_v with f(v)=coe(a_v), in particular both x and u. This describes the mathematical content of the hypotheses, not a checked implementation proof. Accordingly toReal(f(x))-toReal(f(u)) is the actual difference a_x-a_u in this theorem. The packet explicitly states that toReal sends both infinite endpoints to zero, so toReal by itself cannot establish finiteness. Positive-infinite values outside C are permitted; they remain legitimate ambient comparison values in the support definition.

5. **Exact conjunction of two inequalities.** For p=P_C(x-eta g), the theorem states
   \[
   \eta\bigl(\operatorname{toReal}(f(x))-
               \operatorname{toReal}(f(u))\bigr)
      \le \eta\langle g,x-u\rangle
   \]
   and
   \[
   \eta\langle g,x-u\rangle
      \le \frac{\|x-u\|^2}{2}
       -\frac{\|P_C(x-\eta g)-u\|^2}{2}
       +\frac{\eta^2}{2}\|g\|^2.
   \]
   Scalar multiplication is meant by eta g. The projection is of the actual unprojected update x-eta g; the subtracted squared distance uses its nearest feasible point. The initial distance is to the same comparator u, with coefficient one half, and the correction is eta squared times the squared support norm divided by two. The first conclusion compares the finite loss difference with the supporting inner product; the second is the projected geometric estimate. The claim is neither equality nor a sum over rounds.

6. **Selector, iterate initialization, and structural information order.** For each current function f and point x, currentSubgradient makes a local-classical, noncomputable choice from partial f(x) if it is nonempty, and returns zero otherwise. The fallback is not claimed to be a true support when the set is empty. Its explicit arguments include no comparator, horizon, or future losses. The step is
   \[
   \operatorname{step}(V,\eta,f,x)
    =P_C(x-\eta\operatorname{currentSubgradient}(f,x)).
   \]
   With X_t=iterate V eta loss x1 t, initialization and update are exactly
   \[
   X_0=x_1,\qquad
   X_{t+1}=\operatorname{step}(V,\eta_t,\operatorname{loss}_t,X_t).
   \]
   The parameter name x1 does not shift the indexing: the first evaluated loss is loss_0 at X_0=x1. Structurally X_t uses earlier loss functions and step sizes; the current loss_t is used to form X_{t+1}. However, no prefix-invariance or formal causality theorem is supplied. The selector receives the whole current function and refers to its global support set, not just a numerical function value or a specified executable oracle response. The initial point and entire eta schedule are supplied externally; the packet imposes no causal-generation constraint on them. The definitions allow arbitrary initial points, arbitrary real step sizes, and losses without support existence. They alone do not meet the hypotheses needed to apply the single-step theorem at each round. The regret definition is exactly
   \[
   R_T(u)=\sum_{t=0}^{T-1}
      [\operatorname{toReal}(\operatorname{loss}_t(X_t))
       -\operatorname{toReal}(\operatorname{loss}_t(u))].
   \]
   It is defined without feasibility, finite-value, positivity, or per-loss subdifferentiability hypotheses. Without further hypotheses it is a sum of real projections, not automatically a sum of genuine finite loss differences.

7. **Degeneracies, remaining limits, and absence of performance claims.** C cannot be empty because nonemptiness is a Domain field. It may be a singleton or a lower-dimensional closed convex set; there is no interior or full-dimensionality hypothesis. Zero-dimensional E is allowed: C is its sole point, properness makes f finite there, every vector is zero, and both inequalities reduce to 0<=0. No global boundedness of C, f, or supports is assumed; no global convexity, differentiability, Lipschitz constant, or strong convexity premise on f appears. Convexity and closedness are explicit for C. If the initial point is not feasible, the theorem's hx does not apply at the initial round; the definition imposes no initial-feasibility premise. T=0 makes regret an empty sum. No theorem here establishes a prefix-dependence property, an all-round invariant, a telescoped regret estimate, a step-size prescription, convergence, or algorithmic performance. Although the packet now supplies the relevant shared semantics for interpreting the one-step claim, it supplies no theorem proof or compilation evidence. Source identity and source fidelity remain unassessed.

## Evidence boundary

Only the v2 packet was read for this reconstruction, and only the new v2 report and receipt were written. The previous report and receipt were neither read nor modified. Requested model and medium effort identify the assignment request; runtime model identity has not been independently attested.
