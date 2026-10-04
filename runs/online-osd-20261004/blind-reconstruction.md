# Source-blind reconstruction of the frozen draft

Only this run's blind-packet.txt was read. This is a distinct automated reconstruction, not human review, source comparison, proof validation, or compilation. The displayed theorem is an unproved draft statement. Imported dependencies were not opened.

## Seven semantic slots

1. **Ambient objects and dependency boundary.** E is an arbitrary finite-dimensional real inner-product space with its normed additive group structure. V is an object of the imported Domain type and V.carrier is its feasible set. The function f : E -> EReal may take extended-real values. The packet invokes the actual imported project V operator, not an arbitrary postulated next point. However, the fields of Domain, the definition/specification of project, and the definitions of SourceProper and SourceSubdifferential are not included. Consequently the exact encoded closedness, convexity, nonemptiness, nearest-point specification, properness convention, and supporting-inequality convention cannot be checked from this packet. Below, P_V denotes exactly that imported operator; its intended interpretation is projection onto V.carrier. No dependency theorem has been assumed verified.

2. **Properness and support at every feasible point.** The displayed definition is exactly
   \[
   \operatorname{SubdifferentiableOn}(V,f)
   :=\operatorname{SourceProper}(f)\ \land\
   \forall v\in V.\mathrm{carrier},\
      \operatorname{SourceSubdifferential}(f,v)\ne\varnothing.
   \]
   Thus properness is a separate conjunct, and existence of a global supporting vector is required at every feasible point, not only at the current point or comparator. The comment identifies these as global supports. In the usual global-support reading, g at x means f(x)+<g,y-x> <= f(y) for every ambient y, with real inner products embedded into the extended reals. In the usual properness reading, f never equals negative infinity and has a finite real value somewhere. These expansions are conditional interpretations of the named dependencies: their exact definitions are absent from this packet. No explicit globally convex or differentiable-function hypothesis appears. No boundedness hypothesis on f, its supports, or the feasible set appears in the displayed theorem; hidden Domain fields cannot be ruled in or out.

3. **Complete theorem quantification.** For every V, f and witness hf of the preceding conjunction; every real eta with eta>0; every x,u in E with x and u both in V.carrier; and every g in E with g in SourceSubdifferential f x, the conjunction of the two inequalities below is asserted. The supplied g is arbitrary among the actual global supports at x. It is not required to be the selected currentSubgradient. The comparator u may be any feasible point. There is no horizon T, time index t, loss sequence, starting point, norm-bound constant, or step-size schedule in this single-step theorem. Eta=0 and negative eta are excluded by its hypothesis even though the step and iterate definitions accept arbitrary real step sizes.

4. **Exact two conclusions and actual projection expression.** Write r(v)=toReal(f(v)) and p=P_V(x-eta g), with scalar multiplication meant by eta g. The theorem states both
   \[
   \eta\bigl(r(x)-r(u)\bigr)
       \le \eta\langle g,x-u\rangle
   \]
   and
   \[
   \eta\langle g,x-u\rangle
       \le \frac{\|x-u\|^2}{2}
          -\frac{\|P_V(x-\eta g)-u\|^2}{2}
          +\frac{\eta^2}{2}\|g\|^2.
   \]
   The order, signs, factors of one half, eta squared, and projected argument are part of the claim. The second distance is to the actual displayed projection of x-eta g, not to x-eta g itself or to a separately chosen iterate. Under the intended projection semantics this is the feasible projected step; the operator's actual nearest-point property must be supplied by its unseen dependency. The first inequality is the loss-difference-to-support comparison; the second is the geometric single-step comparison. The conclusion is a conjunction of two inequalities, not equality and not a cumulative bound.

5. **Finite-value and toReal semantics.** The displayed quantities are toReal projections of extended-real values. A difference of such projections is an ordinary finite loss difference only when both function values have actual finite real witnesses. The theorem does not list those witnesses separately. Under the usual properness and global-support definitions described in slot 2, properness plus support existence at every feasible point ensures finite values there: a finite comparison point supplied by properness rules out a positively infinite supported value, while properness rules out negative infinity. This explains the intended finite-value use at x and u, but exact derivability depends on the omitted definitions. The packet contains no explicit finite-value theorem or proof. The separate regret definition takes toReal unconditionally, so its definition alone does not guarantee finite original loss values at any round or comparator.

6. **Selection, initial condition, indices, and information order.** For a function f and point x, currentSubgradient f x makes a noncomputable classical choice from SourceSubdifferential f x when that set is nonempty, and otherwise returns zero. Its explicit arguments contain neither a comparator nor a horizon nor future losses. Step is exactly
   \[
   \operatorname{step}(V,\eta,f,x)
      =P_V(x-\eta\operatorname{currentSubgradient}(f,x)).
   \]
   Put X_t=iterate V eta loss x1 t. Then X_0=x1 and
   \[
   X_{t+1}=\operatorname{step}(V,\eta_t,\operatorname{loss}_t,X_t).
   \]
   Despite the parameter spelling x1, its recursive index is 0. The point X_t is formed using earlier indexed functions loss_0,...,loss_{t-1} and earlier step sizes, then loss_t is evaluated there and supplies the support for the update to X_{t+1}. Recursion gives this dependency order; the packet supplies no separate formal causality theorem. The selector receives the whole current function and tests existence of an ambient global support, not merely a numerical oracle response at x. It is classical and noncomputable, so this is an argument/dependency restriction, not an executable limited-information oracle implementation. The initial point and step-size schedule are input parameters with no displayed causal-generation constraints; they could have been chosen externally using additional information. The iterate definition does not require initial feasibility, positive step sizes, or subdifferentiability of each loss. Those would need hypotheses when using the single-step theorem repeatedly. The selected vector is a true support in the nonempty branch; zero in the fallback branch has no asserted support property. The regret definition is exactly
   \[
   R_T(u)=\sum_{t=0}^{T-1}
       \left(\operatorname{toReal}(\operatorname{loss}_t(X_t))
                  -\operatorname{toReal}(\operatorname{loss}_t(u))\right).
   \]
   Its initial round is t=0, and T=0 gives the empty sum. Neither comparator feasibility nor per-round finite values are premises of this definition.

7. **Boundaries and scope limits.** Zero-dimensional E is not excluded by the displayed ambient assumptions. Whenever all premises can be instantiated there, x=u=g=0 and any projection value in E is also zero, so both displayed inequalities reduce to 0<=0. If an empty feasible carrier were permitted by the unseen Domain definition, no x,u satisfying hx,hu could instantiate the theorem; the packet does not reveal whether such a Domain exists. The theorem handles any feasible comparator and any supplied true support, without an explicit norm bound, global differentiability, or global convexity premise on f. It does not assert support existence outside the feasible carrier. The actual Domain may itself include geometric assumptions, which are absent from the packet. No theorem here establishes feasibility of all iterates, finite round losses, telescoping, a regret upper bound, a step-size choice, convergence, or completed algorithmic performance. The displayed context freezes two single-step inequalities and several definitions only. No source title, source numbering, external result identity, proof status beyond unproved draft, or implementation correctness can be inferred.

## Evidence and role boundary

This report preserves the distinction between visible definitions, theorems stated without proofs, and intended interpretations of omitted dependencies. Requested model and reasoning effort in the receipt record the assignment request, not an independently verified runtime attestation. No old run or receipt was read or modified.
