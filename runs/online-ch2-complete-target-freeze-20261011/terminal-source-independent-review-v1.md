# Independent source audit: terminal iterate in Theorems 7.47 and 15.31

## Verdict and scope

The counterexample is valid **under the repeat-last-loss terminal extension used in the proof of7.47**. All printed substantive hypotheses are satisfied by the one-dimensional quadratic instance. The sharp printed RHS is -1/36 while regret is0. This is not a claim that every possible completion of the undefined terminal convention is false: the literal finite-horizon algorithms define only x1,...,xT, whereas the theorem displays use x_(T+1). A different, explicit terminal convention repairs this defect.

I independently inspected original v10 pixels and layout text on PDF141–143 and277–279, not just the route proposal. PDF142 explicitly says predicted loss tilde ell_(T+1)=tilde ell_T; its proof also sets psi_(T+1)=psi_T. Algorithm15.9 on PDF278 has exactly T rounds, no ghost-round rule. Theorem15.31 spans PDF278–279 and invokes7.47 via tilde ell_t=ell_t. This review concerns source semantics and ordinary mathematics; it accepts no Lean proof, package or chapter.

## Literal source contracts

Algorithm7.8 (PDF141/printed129): psi_1,...,psi_T:X->R; V subset X subset R^d closed, nonempty and convex. For t=1,...,T, predict a real-valued loss h_t:V->R; output x_t in argmin over V of psi_t(x)+h_t(x)+sum_(i<t)ell_i(x); receive ell_t:R^d->(-infinity,+infinity] with x_t in its domain; pay ell_t(x_t).

Theorem7.47 (PDF141–142/printed129–130): F_t=psi_t+sum_(i<t)ell_i. For t=1,...,T, F_t+h_t is closed, subdifferentiable and strongly convex on V, giving existence/uniqueness of x_t. Also partial(ell_t-h_t)(x_t) is nonempty, and F_t+ell_t is closed, subdifferentiable and lambda_t-strongly convex in the chosen norm on V. For every u in V and every ghat_t in that difference subdifferential, the displayed chain is

R_T(u) <= psi_T(u)-psi_1(x_1)
 + sum_(t=1)^T [<ghat_t,x_t-x_(t+1)> - lambda_t ||x_t-x_(t+1)||^2/2]
 + sum_(t=1)^(T-1) [psi_t(x_(t+1))-psi_(t+1)(x_(t+1))]
 <= psi_T(u)-psi_1(x_1) + sum_(t=1)^T ||ghat_t||_*^2/(2 lambda_t)
 + sum_(t=1)^(T-1) [psi_t(x_(t+1))-psi_(t+1)(x_(t+1))].

The printed proof says h_(T+1)=h_T and psi_(T+1)=psi_T. It claims to discard a nonpositive terminal term from Lemma7.1, then to telescope prediction terms away. The original extracted page files retain the exact full statement/proof and original page images retain all indices and layout.

Algorithm15.9 (PDF278/printed266): V subset X subset R^d nonempty closed convex, regularizers psi_1,...,psi_T; for each t=1,...,T receive ell_t with V subset dom ell_t, choose x_t in argmin over V of psi_t+sum_(i<=t)ell_i, and pay ell_t(x_t). No x_(T+1) is defined.

Theorem15.31 (PDF278–279/printed266–267): V convex, closed, nonempty; each G_t=psi_t+sum_(i<=t)ell_i is proper, closed and lambda_t-strongly convex in the chosen norm. For every u in V, it displays

R_T(u) <= psi_T(u)-psi_1(x_1)
 - sum_(t=1)^T lambda_t ||x_t-x_(t+1)||^2/2
 + sum_(t=1)^(T-1) [psi_t(x_(t+1))-psi_(t+1)(x_(t+1))].

The argument immediately preceding it is the specialization of7.47 with h_t=ell_t. Remark15.32 then says zero regularizers give nonpositive BTL regret. That qualitative conclusion is compatible with the repaired terminal-free form; it does not validate the disputed last negative term.

## Complete quadratic hypothesis audit

Set d=1, V=X=R, norm=absolute value, T=1, psi_1(x)=x^2/2, ell_1(x)=(x-1)^2/2, and h_1=ell_1. All functions are finite everywhere, continuous/closed, proper and differentiable, hence subdifferentiable. V is nonempty, closed and convex. The real-valued hint is legal in Algorithm7.8; exact-current hints are allowed by this prescient interpretation and no hypothesis forbids them.

F_1=psi_1. Both F_1+h_1 and F_1+ell_1 equal G_1=x^2-x+1/2=(x-1/2)^2+1/4, which is2-strongly convex in absolute value. Thus lambda_1=2 is valid, and the unique prescribed x_1 is1/2. The difference ell_1-h_1 is identically0, so its subdifferential is {0}; choose ghat_1=0. The entire feasible set is within the loss domain, satisfying Algorithm15.9 as well. Let u=x_1=1/2.

Now add the proof's terminal extension: psi_2=psi_1, h_2=h_1. The extended optimistic rule gives x_2=argmin(psi_2+ell_1+h_2)=argmin(psi+2ell)=2/3. This extended objective is itself3-strongly convex, so even an extra terminal existence/uniqueness requirement is satisfied. Equivalently, continuing BTRL with ell_2=ell_1 gives the same x_2, though Algorithm15.9 never mandates that continuation.

The regularizer difference is0 and the T-1 sum is empty. Regret against u=x_1 is0. The sharp RHS is -(2/2)(1/2-2/3)^2=-1/36. The second, norm-only RHS of7.47 is0 in this instance, so this example refutes the **first sharp inequality under the repeated terminal rule**, not the coarser inequality independently.

The JSON rational receipt checks every displayed value exactly with Fraction arithmetic. No floating-point approximation, simulation or Lean compilation is involved.

## Where the endpoint is lost

Write G_t=F_t+ell_t and set psi_(T+1)=psi_T, so F_(T+1)=G_T. For any feasible terminal z=x_(T+1) for which the displayed quantities are finite, direct telescoping gives the exact identity

R_T(u) = psi_T(u)-psi_1(x_1)
 + sum_(t=1)^T [G_t(x_t)-G_t(x_(t+1))]
 + sum_(t=1)^(T-1)[psi_t(x_(t+1))-psi_(t+1)(x_(t+1))]
 + G_T(z)-G_T(u).

The last term is nonpositive if z minimizes **unhinted** G_T. A minimizer of G_T+h_T need not minimize G_T. In the quadratic example G_T(2/3)-G_T(1/2)=1/36, exactly the amount needed to restore the missing inequality.

If one instead applies the FTRL identity to hinted objectives, the terminal optimality controls G_T+h_(T+1). After telescoping a prediction correction h_(T+1)(u)-h_(T+1)(z) remains. Repeating the final hint does not make this correction zero. Here it equals5/72. Adding it to the printed sharp RHS gives1/24, a valid (looser) bound.

There is also an explicit indexing/cancellation defect visible in the printed proof: its prediction-difference sum is t=1,...,T-1, while the unhinted F-difference sum runs through T, and the following equality erases the surviving h_T(u)-h_T(x_T) quantity. Starting with the correct full hinted identity yields the endpoint correction above. The counterexample avoids relying on any interpretation of that algebraic line: it directly evaluates the stated sharp bound under the proof's specified terminal completion.

## Repair candidates, all pending separate approval and proofs

1. **Zero final prediction for optimistic FTRL.** Define psi_(T+1)=psi_T and h_(T+1)=0, then define the ghost x_(T+1) as a minimizer of G_T. This affects no played round. Under the original strong-convexity/closedness and appropriate feasibility/attainment conditions it supports the printed sharp7.47 shape. Required obligations: precise effective-domain/nonempty feasibility; existence/uniqueness of the ghost minimizer; the exact finite telescoping identity; transfer of the difference subgradient to G_t plus the indicator; the strong-convexity inequality; terminal nonpositivity; the dual-norm/Young step with lambda_t>0. Preserve the original repeat-hint source text as a correction record.

2. **Explicit BTRL endpoint convention.** Define x_(T+1)=x_T for analysis. Then the last negative term is0 and15.31 reduces to the same formula with the stability sum only through T-1. This is justified because x_T already minimizes G_T. One may implement it as a ghost round with psi_(T+1)=psi_T and zero new loss, but should not pretend Algorithm15.9 originally stated it. Required obligations: actual BTRL minimizers and feasibility; strong-convex minimizer inequality on V; exact telescoping; T=1/empty-sum and comparator-domain cases. No extra played loss is introduced.

3. **Keep an arbitrary/repeated terminal and retain its residual.** Add G_T(x_(T+1))-G_T(u) to the sharp RHS. The algebra then has no terminal-minimizer assumption. If the terminal minimizes G_T+h_(T+1), replace that residual by the upper bound h_(T+1)(u)-h_(T+1)(x_(T+1)). Neither correction is automatically nonpositive. Required obligations include finite/extended-real arithmetic conditions and the terminal hinted-minimizer inequality. This preserves the repeated-loss interpretation but changes the displayed guarantee transparently.

4. **Sharper terminal-free BTRL alternative.** After truncating the stability sum to T-1, retain the comparator residual G_T(x_T)-G_T(u), or bound it by -lambda_T||u-x_T||^2/2. This is a useful separately derived theorem, not the literal printed formula. It requires a strong-convexity minimizer inequality at x_T.

No source claim is dropped. No route is declared accepted. In particular, these findings do not invalidate the distinct prescient-OMD theorem15.30; its proof and extended-real optimality assumptions need their own review. The whole-lookahead branch and terminal-adjudication obligation remain open.
