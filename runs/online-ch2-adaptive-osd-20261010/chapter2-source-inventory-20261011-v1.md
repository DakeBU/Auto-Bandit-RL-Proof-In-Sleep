# Chapter 2 source inventory candidate

Source: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`; SHA-256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, unchanged before/after.

Chapter2 spans printed8-23/PDF20-35. Mathematical claims in History Bits are retained; Section2.5 Problems are separate. This is a candidate for independent source review, not a chapter freeze, source-to-Lean acceptance, or completion certificate.

Actor `/root/adaptive_decoder`, requested GPT-6 Astra/medium, without runtime attestation. This source-reading phase follows and is separate from the completed restricted-input canary decoding. Repository snapshot: `codex/research-online-ch2-adaptive-osd` at `0283616c8439b09fc49d5e35373ff74aa11371cc`, dirty content preserved. No canonical metadata, proofs, builds or commits modified.

Navigation check:32 consecutively numbered entries2.1-2.32,2 algorithm boxes,73 inventory rows including overlapping dependencies, forward claims and five separate Problems. Counts are not independent proof counts; mandatory denominator is unknown.

All mathematical statements concern real Euclidean spaces unless specified otherwise. Dependencies are source-reading links, not verified Lean proof-term edges. Source time is1-based; Lean0-based translations need terminal alignment. JSON records exact excerpt fingerprints and page-text hashes.

Visual checks:PDF25-31 and PDF35. The factor1/2 in the weighted-distance identity is printed correctly. Theorem2.23 uses ordinary interior on first m-1 domains and full last domain; Theorem2.26 includes continuity at x.

## Remaining beyond the adaptive package

- Reconcile every mandatory local numbered/unnumbered source branch with exact current declarations and BODY/FINAL evidence. This inventory does not label already implemented mathematics missing.
- Beyond adaptive forward work: Chapter5 oracle-distance-energy impossibility and DLsqrt(T) minimax lower bounds, Chapter3 unbounded varying-step SGD, Chapter4 square-loss OGD improvement, and Chapter13 parameter-free guarantees.
- Prescient/lookahead Section15.5.1 and Chapter5 unbounded-variable-step OGD have ledger candidate packages but still require source-container reconciliation according to the consulted ledger.
- Printed23 FTRL/unbounded-domain and offline-no-minimizer claims need explicit reconciliation with Chapter7/Chapter3 ownership; navigation alone does not discharge them.
- Keep definitions, full example branches, exercise-deferred main claims, extended-real/causal/degenerate cases. Independent mandatory proof denominator remains unknown.

## Review issues

- No chapter freeze/completion. All numbered navigation entries and two algorithms checked; row counts include overlapping dependencies and are not proof counts.
- Norm convexity and four closure bullets remain mandatory despite proofs left as exercises. Standalone Problems2.1-2.5 remain separate.
- Both sharp Theorem2.13 branches, terminal residuals, unbounded fixed-step validity and actual OSD transfer must survive reconciliation.
- Visual PDF26 confirms printed factor1/2 in weighted-distance identity; no missing-half correction justified.
- Zero-distance/energy/D/L cases in learning-rate displays require explicit admissibility and min/infimum review.
- Huber threshold sign, hinge zero-normal exception, finite-max family nonemptiness, Lipschitz L convention need explicit source qualification.
- History Bits printed23 includes FTRL/unbounded-domain and offline-no-minimizer mathematics; do not exclude by section heading.
- Source literally points no-minimizer claim to Example3.2; later-chapter correctness of that pointer is outside this task and not repaired here.
- Hausdorff generality and relative-interior footnote retained for independent branch-scope adjudication.
- Adaptive Eq4.4/Theorem4.14 are Chapter4 forward material, not new numbered Chapter2 results. Their completion does not discharge all other required claims.
- No compiler, source-to-Lean equivalence, acceptance receipt, merge, main/live update or publication verified.

## Ledger boundary

Consulted `E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/qualified-source-reconciliation-draft-v4.json` (SHA-256 `7ef4eae2a9a26720445e4399ed23e24146b5f478c4b051b875ff7674995bfdb2`). Stage: "qualified local-content reconciliation candidate; not chapter acceptance"; source-container acceptance false. Its65 historical overlapping containers are not an independent theorem denominator. Its8 required/open forward containers include6 with pending precise future enumeration. These are ledger states, not newly checked acceptance receipts.

The adaptive source card was read only for source ownership and sharp-potential context; this earlier card does not establish the current package completion state.

## Inventory

### Remark 2.1

Kind:Remark. Printed pages [9]; PDF pages [21]. Required main text:False.

Pedagogical motivation for convex analysis and proofs for adversarial guarantees.

Dependencies: primitive context.

Boundary: Preserved navigation; no standalone theorem claim.

Exact extraction anchor:`Remark 2.1`. Excerpt SHA-256:`fd28979492085b8ec6750f6c3a11b165df14c25ba4afca71fc9faf385ee39c0c`.

### Definition 2.2

Kind:Definition. Printed pages [9]; PDF pages [21]. Required main text:True.

V subset R^d is convex iff lambda*x+(1-lambda)*y is in V for every x,y in V and 0<lambda<1.

Dependencies: primitive context.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Definition 2.2`. Excerpt SHA-256:`230c25b57c43c1c23db8364a5b00a786a7687093af3969ca98e73ba5d7aaaefa`.

### Definition 2.3

Kind:Definition. Printed pages [10]; PDF pages [22]. Required main text:True.

f:R^d -> [-infinity,+infinity] is convex iff {(x,y) in R^(d+1): y>=f(x)} is convex; epigraph heights y are real.

Dependencies: Definition 2.2; unnumbered:extended-domain-indicator.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Definition 2.3`. Excerpt SHA-256:`911fdd58e387273d959f1cfd39644a8f7f020c3df3cd931710e0624ccdc26558`.

### Theorem 2.4

Kind:Theorem. Printed pages [10]; PDF pages [22]. Required main text:True.

Let f:R^d -> (-infinity,+infinity] with convex dom f. Then f is convex iff f(lambda*x+(1-lambda)*y)<=lambda*f(x)+(1-lambda)*f(y) for every x,y in dom f and 0<lambda<1.

Dependencies: Definition 2.3; unnumbered:extended-domain-indicator.

Boundary: No minus infinity; explicit convex-domain hypothesis. Rockafellar Theorem4.1.

Exact extraction anchor:`Theorem 2.4`. Excerpt SHA-256:`ef77adc55414cb2e5dff72ea5e551857325d9dc4745036665c20d3d484f5dea8`.

### Example 2.5

Kind:Example. Printed pages [10]; PDF pages [22]. Required main text:True.

Every affine function f(x)=<z,x>+b is convex.

Dependencies: Theorem 2.4.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Example 2.5`. Excerpt SHA-256:`f21d35ed0c629a55faff17b681e1a3cf7de0861cee7519d41f5e4578d953085b`.

### Example 2.6

Kind:Example. Printed pages [10]; PDF pages [22]. Required main text:True.

Every norm is convex.

Dependencies: Theorem 2.4.

Boundary: proof left as exercise; still mandatory main text.

Exact extraction anchor:`Example 2.6`. Excerpt SHA-256:`1929849371571fff1da2a3fd36e089cb79c6e65fd0327464ada3540aee96bc97`.

### Theorem 2.7

Kind:Theorem. Printed pages [11]; PDF pages [23]. Required main text:True.

For convex f:R^d -> (-infinity,+infinity], x in interior(dom f), and f differentiable at x, f(y)>=f(x)+<gradient f(x),y-x> for all y in R^d.

Dependencies: Definition 2.3.

Boundary: Global support, including outside-domain y. Rockafellar Theorem25.1/Corollary25.1.1.

Exact extraction anchor:`Theorem 2.7`. Excerpt SHA-256:`d834485f2467f42af78fe35ad72afcf02122cc80562df8962a812746fcfafa98`.

### Theorem 2.8

Kind:Theorem. Printed pages [11]; PDF pages [23]. Required main text:True.

Let V be nonempty convex, x_star in V, and f convex and differentiable on an open set containing V. Then x_star minimizes f on V iff <gradient f(x_star),y-x_star>>=0 for every y in V.

Dependencies: Theorem 2.7.

Boundary: Does not assert minimizer existence or require closed V.

Exact extraction anchor:`Theorem 2.8`. Excerpt SHA-256:`e871d55be64006d37ea050ec5d551688d2c670c1dd549e0ab430f925746f65d8`.

### Theorem 2.9

Kind:Theorem. Printed pages [11]; PDF pages [23]. Required main text:True.

For measurable convex f:R^d -> (-infinity,+infinity] and R^d-valued random X on a probability space with E[X] existing and X in dom f almost surely, E[f(X)]>=f(E[X]).

Dependencies: Definition 2.3.

Boundary: Jensen; no separately printed finite E[f(X)] premise.

Exact extraction anchor:`Theorem 2.9`. Excerpt SHA-256:`29808fa28b4f9966aee17e1d48375c9282f4f0f971b942c58e0be486812c98df`.

### Algorithm 2.1

Kind:Algorithm. Printed pages [12]; PDF pages [24]. Required main text:True.

Given nonempty closed convex V subset R^d, x_1 in V, positive eta_1,...,eta_T: for t=1,...,T output x_t, pay ell_t(x_t), where ell_t is convex and differentiable on an open set containing V; set g_t=gradient ell_t(x_t); set x_(t+1)=Pi_V(x_t-eta_t*g_t)=argmin_{y in V}||x_t-eta_t*g_t-y||_2.

Dependencies: unnumbered:game-regret; Proposition 2.11.

Boundary: Output before current feedback; need actual causal algorithm, not assumed regret.

Exact extraction anchor:`Algorithm 2.1`. Excerpt SHA-256:`c2196e797113a86367e003ca039bc13cebf9e0a03fdde277e6c5a17cf2d2f833`.

### Example 2.10

Kind:Example. Printed pages [12]; PDF pages [24]. Required main text:True.

FTL on [-1,1], ell_t(x)=z_t*x, with z_1=-1/2, z_t=1 for even t and z_t=-1 for odd t>=3: arbitrary first x_1 in [-1,1], then x_t=1 for even t and -1 for odd t>=3. For T>=1 cumulative loss and regret against 0 equal T-1-x_1/2 >= T-3/2.

Dependencies: unnumbered:strict-past-FTL; Example 2.5.

Boundary: First prediction excluded from odd-time formula; empty horizon not covered by displayed identity.

Exact extraction anchor:`Example 2.10`. Excerpt SHA-256:`c129cca091f807fa94e512498d0270d854e4a9c6183e789f8d33d31fa61f1302`.

### Proposition 2.11

Kind:Proposition. Printed pages [12, 13]; PDF pages [24, 25]. Required main text:True.

For x in R^d, y in nonempty closed convex V, and unique Euclidean projection Pi_V(x)=argmin_{v in V}||x-v||_2, ||Pi_V(x)-y||_2<=||x-y||_2.

Dependencies: Theorem 2.8.

Boundary: Subscript2 denotes norm; proof uses squared norms.

Exact extraction anchor:`Proposition 2.11`. Excerpt SHA-256:`e97ddc99d4b0e91f41f0131e6cd684000c7d4b7d5176e5ed075150f78ddb00c0`.

### Lemma 2.12

Kind:Lemma. Printed pages [13]; PDF pages [25]. Required main text:True.

For nonempty closed convex V, ell_t convex and differentiable on an open set containing V, eta_t>0, g_t=gradient ell_t(x_t), x_(t+1)=Pi_V(x_t-eta_t*g_t), every u in V satisfies eta_t*(ell_t(x_t)-ell_t(u)) <= eta_t*<g_t,x_t-u> <= (||x_t-u||_2^2-||x_(t+1)-u||_2^2)/2 + eta_t^2*||g_t||_2^2/2.

Dependencies: Theorem 2.7; Proposition 2.11; Algorithm 2.1.

Boundary: Feasibility of x_t inherited from algorithm context.

Exact extraction anchor:`Lemma 2.12`. Excerpt SHA-256:`7753bf251386fe271d6ec6b6716a6c509a2c2299127674548e81e7274c9f34c7`.

### Theorem 2.13

Kind:Theorem. Printed pages [13, 14]; PDF pages [25, 26]. Required main text:True.

Let V be nonempty closed convex with diameter D=sup_{x,y in V}||x-y||_2, arbitrary ell_1,...,ell_T convex and differentiable on an open set containing V, x_1 in V, and 0<eta_(t+1)<=eta_t for t=1,...,T-1. Algorithm2.1 with its positive steps satisfies for all u in V: Regret_T(u)<=D^2/(2*eta_T)+sum_{t=1}^T eta_t*||g_t||_2^2/2-||x_(T+1)-u||_2^2/(2*eta_T). Moreover, for constant eta_t=eta>0: Regret_T(u)<=||u-x_1||_2^2/(2*eta)+(eta/2)*sum_{t=1}^T||g_t||_2^2-||x_(T+1)-u||_2^2/(2*eta).

Dependencies: Algorithm 2.1; Lemma 2.12; unnumbered:weighted-distance-identity.

Boundary: Both sharp branches mandatory; fixed branch valid for unbounded domains as printed14 states. Finite D needed for nonvacuous variable bound.

Exact extraction anchor:`Theorem 2.13`. Excerpt SHA-256:`77b57378a04785f0036c87a61a4af9e3833a333825bdb41178082d9b1e2a7dee`.

### Example 2.14

Kind:Example. Printed pages [15]; PDF pages [27]. Required main text:True.

Chapter1 square guessing: x_t,y_t in [0,1], ell_t(x)=(x-y_t)^2, derivative2*(x-y_t) bounded on [0,1], Pi_[0,1](x)=min(max(x,0),1). OGD with optimal constant step gives O(sqrt(T)) regret, worse than earlier Chapter1 guarantee; Chapter4 promises optimal tuning.

Dependencies: Algorithm 2.1; unnumbered:diameter-gradient-coarse-tuning; Chapter1:guessing-game.

Boundary: D=1,L=2 gives eta=1/(2 sqrt(T)), bound2 sqrt(T) as deduction. Upper bound alone is not an algorithmic lower bound proving suboptimality.

Exact extraction anchor:`Example 2.14`. Excerpt SHA-256:`fb360a288892e8d82df3702f3ee30f10f20bd853e8c161d380381fbdf71bf1a6`.

### Example 2.15

Kind:Example. Printed pages [15, 16]; PDF pages [27, 28]. Required main text:True.

Linear prediction <z_t,x>, V=R^d, residual e=<z_t,x>-y_t: ell_t(x)=e^2/2 if |e|<=delta, and delta*(|e|-delta/2) otherwise. Gradient is e*z_t if |e|<=delta, and delta*sign(e)*z_t otherwise. Bounded ||z_t||_2 gives bounded gradients; constant horizon-dependent eta proportional to1/sqrt(T) makes average OGD loss approach that of every fixed linear predictor.

Dependencies: Theorem 2.13; Algorithm 2.1; unnumbered:fixed-unbounded-domain-residual.

Boundary: Source calls delta a threshold without explicit sign. Qualify nonnegative threshold, including delta=0, rather than adding bounded V. Derived bound for delta>=0 and ||z_t||<=R is ||g_t||<=delta R.

Exact extraction anchor:`Example 2.15`. Excerpt SHA-256:`46376e978d33fff495f4fe0f4a1c16e4a18627efc93cd786aaa4364370362305`.

### Definition 2.16

Kind:Definition. Printed pages [16]; PDF pages [28]. Required main text:True.

f:R^d -> [-infinity,+infinity] is closed iff {x:f(x)<=alpha} is closed for every real alpha.

Dependencies: primitive context.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Definition 2.16`. Excerpt SHA-256:`ce5d2e08d1885725b4f37f278d3d9e10949e303bb406c4a2e3d36a9766107d98`.

### Example 2.17

Kind:Example. Printed pages [16]; PDF pages [28]. Required main text:True.

Indicator iota_V is closed iff V is closed.

Dependencies: Definition 2.16; unnumbered:extended-domain-indicator.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Example 2.17`. Excerpt SHA-256:`ff1cf4a01d26b58e1cea9c752fc25c9812dc5fd69fd8504fd221b6dbbfe3f500`.

### Definition 2.18

Kind:Definition. Printed pages [16]; PDF pages [28]. Required main text:True.

A function is proper iff nowhere -infinity and finite somewhere.

Dependencies: primitive context.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Definition 2.18`. Excerpt SHA-256:`74c2058201d3be38f0ace56c67a227b1c185e84b91c1d49f9cdb10260145b029`.

### Example 2.19

Kind:Example. Printed pages [16]; PDF pages [28]. Required main text:True.

Indicator iota_V is proper iff V is nonempty.

Dependencies: Definition 2.18; unnumbered:extended-domain-indicator.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Example 2.19`. Excerpt SHA-256:`28eb5c5a2c38ba7ece83a33311b5a68eff5c5b8d7374caa38eaf903b6847014e`.

### Definition 2.20

Kind:Definition. Printed pages [16, 17]; PDF pages [28, 29]. Required main text:True.

For proper f:R^d -> (-infinity,+infinity], g in R^d is a subgradient at x iff f(y)>=f(x)+<g,y-x> for every y in R^d. Its set is partial f(x); f is subdifferentiable at x iff this set is nonempty.

Dependencies: Definition 2.18.

Boundary: Global support; convexity not required by definition.

Exact extraction anchor:`Definition 2.20`. Excerpt SHA-256:`78bdeddc92ed7f2de8178a0e5aad2b0f24bde7b441ff45974f2b632717087a49`.

### Theorem 2.21

Kind:Theorem. Printed pages [17]; PDF pages [29]. Required main text:True.

For f:R^d->R and convex V subset R^d, if partial f(x) is nonempty for every x in V, then f restricted to V is convex.

Dependencies: Definition 2.20; Theorem 2.4.

Boundary: Real-valued f; no prior convexity or closedness of f.

Exact extraction anchor:`Theorem 2.21`. Excerpt SHA-256:`43c055e4bd7b53791d0a02f8477314264bd157943f7d283c143a34f85d3ecab2`.

### Theorem 2.22

Kind:Theorem. Printed pages [17]; PDF pages [29]. Required main text:True.

For convex f:R^d -> [-infinity,+infinity] finite at x, f is differentiable at x iff partial f(x) is a singleton, consisting of gradient f(x).

Dependencies: Definition 2.20; Definition 2.3.

Boundary: Literal source does not separately state interior-domain or global properness premise. Any qualification needs review. Rockafellar Theorem25.1.

Exact extraction anchor:`Theorem 2.22`. Excerpt SHA-256:`dc9bb88eb6077a4a45e8f855a4c7f3470944b8e2baff1517707a16b77999eb85`.

### Theorem 2.23

Kind:Theorem. Printed pages [17, 18]; PDF pages [29, 30]. Required main text:True.

For proper f_1,...,f_m on R^d and F=sum_i f_i, partial F(x) contains the Minkowski sum of partial f_i(x), for every x; empty constituent makes inclusion vacuous. If also each f_i is convex and closed and dom f_m intersects intersection_{i=1}^{m-1} interior(dom f_i) nontrivially, equality holds for every x.

Dependencies: Definition 2.20; Definition 2.16; Definition 2.18.

Boundary: Both branches; ordinary interior on first m-1 domains and full last domain, not relative-interior replacement.

Exact extraction anchor:`Theorem 2.23`. Excerpt SHA-256:`260fa7dabebe6b560a54243753910f7375b0f501118a4cf16dc2ea998606cd41`.

### Example 2.24

Kind:Example. Printed pages [18]; PDF pages [30]. Required main text:True.

For f(x)=|x|, partial f(x)={1} at x>0, [-1,1] at x=0, {-1} at x<0.

Dependencies: Definition 2.20.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Example 2.24`. Excerpt SHA-256:`422a3066ffcfcb5f57b48832c3f9fded83c3fc762ac04a60043721be7a139299`.

### Example 2.25

Kind:Example. Printed pages [18]; PDF pages [30]. Required main text:True.

For nonempty convex V, g in partial iota_V(x) iff x in V and <g,y-x><=0 for all y in V; this is normal cone N_V(x). At x in interior(V), N_V(x)={0}. For unit Euclidean ball V and ||x||_2=1, N_V(x)={alpha*x:alpha>=0}.

Dependencies: Definition 2.20; unnumbered:extended-domain-indicator.

Boundary: All three branches required; no closedness added to general identification.

Exact extraction anchor:`Example 2.25`. Excerpt SHA-256:`1ba41d5050f644cf867b4cafa791f59a1c1dbf6f10ceee20909178334538b917`.

### Theorem 2.26

Kind:Theorem. Printed pages [18]; PDF pages [30]. Required main text:True.

Finite family (f_i)_(i in I) of proper convex functions R^d->(-infinity,+infinity]; x in every dom f_i and every f_i continuous at x. For F=max_i f_i, active set A(x)={i:f_i(x)=F(x)}, partial F(x)=conv(union_{i in A(x)} partial f_i(x)).

Dependencies: Definition 2.20; Definition 2.18; unnumbered:pointwise-supremum.

Boundary: Finite maximum implicitly needs nonempty I, not separately printed. Equality required. Bauschke-Combettes Theorem18.5.

Exact extraction anchor:`Theorem 2.26`. Excerpt SHA-256:`c08e0bb046b82bcce92ed2f5470796e799b2982403f1d17a8bfce62e8ade54fb`.

### Example 2.27

Kind:Example. Printed pages [18]; PDF pages [30]. Required main text:True.

For z in R^d, ell(x)=max(1-<z,x>,0): partial ell(x)={0} when1-<z,x><0; {-alpha*z:alpha in [0,1]} at equality; {-z} otherwise.

Dependencies: Theorem 2.26; Example 2.5; Theorem 2.22.

Boundary: Closed seam interval; zero normal retained.

Exact extraction anchor:`Example 2.27`. Excerpt SHA-256:`07a963a7cdfc6181a8bfbbeb4086c4482070cb2fd8773791b87d83df9f169008`.

### Theorem 2.28

Kind:Theorem. Printed pages [18]; PDF pages [30]. Required main text:True.

For proper f:R^m->(-infinity,+infinity], A in R^(m by d), b in R^m, h(x)=f(Ax+b), one has A^T partial f(Ax+b) subset partial h(x) for all x.

Dependencies: Definition 2.20.

Boundary: Inclusion only; no convexity/closedness premise. h may be identically +infinity if affine image misses domain; define support convention explicitly.

Exact extraction anchor:`Theorem 2.28`. Excerpt SHA-256:`dca7773714cb639abacb01a326011ba8a2384c5534ab8bee9dc065fd9e07170c`.

### Definition 2.29

Kind:Definition. Printed pages [19]; PDF pages [31]. Required main text:True.

f:R^d->(-infinity,+infinity] is L-Lipschitz on V subset dom f in norm ||.|| iff |f(x)-f(y)|<=L||x-y|| for every x,y in V.

Dependencies: unnumbered:extended-domain-indicator.

Boundary: Nonnegative L conventional but not separately printed.

Exact extraction anchor:`Definition 2.29`. Excerpt SHA-256:`d0ea8cfa779028c74f32b569ddbfea7d2580b566ce4618aa9f0b781db96fbebb`.

### Theorem 2.30

Kind:Theorem. Printed pages [19]; PDF pages [31]. Required main text:True.

For convex proper f:R^d->(-infinity,+infinity], L-Lipschitzness on interior(dom f) in Euclidean norm is equivalent to ||g||_2<=L for every x in interior(dom f) and every g in partial f(x).

Dependencies: Definition 2.29; Definition 2.20; unnumbered:interior-subgradient-existence.

Boundary: Both directions, every subgradient, interior-domain and empty-interior cases retained.

Exact extraction anchor:`Theorem 2.30`. Excerpt SHA-256:`58139eb174df31baa096a8a6c17b9e7dea312f17550ab4d60a93a3105f01736e`.

### Lemma 2.31

Kind:Lemma. Printed pages [19]; PDF pages [31]. Required main text:True.

For nonempty closed convex V, ell_t:R^d->(-infinity,+infinity] subdifferentiable on V, eta_t>0, g_t in partial ell_t(x_t), x_(t+1)=Pi_V(x_t-eta_t*g_t), every u in V satisfies eta_t*(ell_t(x_t)-ell_t(u)) <= eta_t*<g_t,x_t-u> <= (||x_t-u||_2^2-||x_(t+1)-u||_2^2)/2 + eta_t^2*||g_t||_2^2/2.

Dependencies: Definition 2.20; Proposition 2.11; Algorithm 2.2.

Boundary: No extra convexity premise printed; properness through source subgradient convention, feasibility through algorithm context.

Exact extraction anchor:`Lemma 2.31`. Excerpt SHA-256:`9087cace3ded9f1d47f0591618f83a4a8ee246f8353991b75e0c9c4e54274011`.

### Algorithm 2.2

Kind:Algorithm. Printed pages [20]; PDF pages [32]. Required main text:True.

Input nonempty closed convex V subset R^d, x_1 in V, positive eta_1,...,eta_T. For t=1,...,T output x_t, pay ell_t(x_t) with ell_t subdifferentiable on V, choose g_t in partial ell_t(x_t), update x_(t+1)=Pi_V(x_t-eta_t*g_t)=argmin_{y in V}||x_t-eta_t*g_t-y||_2.

Dependencies: Definition 2.20; Proposition 2.11; unnumbered:game-regret.

Boundary: Actual legal selected feedback and causal output order required.

Exact extraction anchor:`Algorithm 2.2`. Excerpt SHA-256:`ada9d563f4e62577414ad86c39814adad1a9ae2f1a5df158ec34c43b2b61b763`.

### Example 2.32

Kind:Example. Printed pages [20]; PDF pages [32]. Required main text:True.

Guessing with ell_t(x)=|x-y_t|: partial ell_t(x)={1} if x>y_t, [-1,1] if x=y_t, {-1} if x<y_t. OSD with optimal learning rate gives O(sqrt(T)) regret as T grows.

Dependencies: Example 2.24; Algorithm 2.2; unnumbered:actual-OSD-performance-transfer; unnumbered:diameter-gradient-coarse-tuning; Chapter1:guessing-game.

Boundary: Inherited [0,1] setting yields D=L=1, eta=1/sqrt(T), bound sqrt(T) as deduction; all seam choices legal.

Exact extraction anchor:`Example 2.32`. Excerpt SHA-256:`015991ac786c7c0c771398fd50d0cb6e86eb89dd191d6625a627814ecaa1c7ce`.

### unnumbered:game-regret

Kind:Definition/protocol. Printed pages [8]; PDF pages [20]. Required main text:True.

For t=1,...,T output x_t in V subset R^d, pay ell_t(x_t) for ell_t:V->R, receive feedback; losses adversarial. Regret_T(u)=sum_t ell_t(x_t)-sum_t ell_t(u) for every fixed u in V. OCO restricts losses to convex functions.

Dependencies: primitive context.

Boundary: No minimizer or stochastic assumption; output before feedback.

Exact extraction anchor:`To summarize`. Excerpt SHA-256:`3c8398dfb645899e24cb2a6ea0579a30d3506ff82698322fc9de3155ab701653`.

### unnumbered:extended-domain-indicator

Kind:Definition. Printed pages [9]; PDF pages [21]. Required main text:True.

Extended-real values allow both infinities. dom f={x:f(x)<+infinity}. Indicator iota_V is0 on V and +infinity otherwise; adding it enforces feasible finite-loss decisions and comparators.

Dependencies: primitive context.

Boundary: Domain includes minus-infinity values for unrestricted f; respect properness/no-minus-infinity when adding indicators.

Exact extraction anchor:`We will make use`. Excerpt SHA-256:`19e0be447e06c37cdc55ec38f75e3194c654f688878adb4408d26eff5e43acac`.

### unnumbered:epigraph-domain-indicator-closure

Kind:Unnumbered result. Printed pages [10]; PDF pages [22]. Required main text:True.

Convex f has convex dom f. Indicator iota_V is convex iff V is convex. Convex f:R^d->(-infinity,+infinity] plus iota_V for convex V is convex.

Dependencies: Definition 2.3; unnumbered:extended-domain-indicator.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Note that the definition implies`. Excerpt SHA-256:`eb22704a40d4584d0448dfdd276b00e84f06bccc01f48b2b91f30bfe215e4842`.

### unnumbered:nonnegative-combination

Kind:Unnumbered result. Printed pages [10, 11]; PDF pages [22, 23]. Required main text:True.

Nonnegative linear combinations of convex functions are convex.

Dependencies: Definition 2.3.

Boundary: proof left as exercise; mandatory. Extended-real arithmetic/domain conventions need explicit qualification.

Exact extraction anchor:`Iffandgare convex`. Excerpt SHA-256:`11d79be28e7bff51ecde331d01fcfca6e27c104d8b5304289060450960f8eba9`.

### unnumbered:affine-composition

Kind:Unnumbered result. Printed pages [10, 11]; PDF pages [22, 23]. Required main text:True.

Composition with an affine transformation preserves convexity.

Dependencies: Definition 2.3.

Boundary: proof left as exercise; mandatory.

Exact extraction anchor:`The composition with an affine`. Excerpt SHA-256:`db4409c657083bcfd7c7b3cbf13e60927b4aa2c97a3d2373ceb183ea0c558822`.

### unnumbered:monotone-convex-composition

Kind:Unnumbered result. Printed pages [10, 11]; PDF pages [22, 23]. Required main text:True.

For convex f:R^d->R and convex nondecreasing g:R->R, g composed with f is convex.

Dependencies: Theorem 2.4.

Boundary: proof left as exercise; mandatory, explicitly real-valued.

Exact extraction anchor:`Iff:R`. Excerpt SHA-256:`9426ed755d158b2c6254936829de7bc4be4a2196780f40ea96a88e1ad91ea53c`.

### unnumbered:pointwise-supremum

Kind:Unnumbered result. Printed pages [10, 11]; PDF pages [22, 23]. Required main text:True.

Pointwise supremum of convex functions is convex.

Dependencies: Definition 2.3.

Boundary: proof left as exercise; mandatory. Source sentence leaves family indexing/empty-family conventions implicit.

Exact extraction anchor:`The pointwise supremum`. Excerpt SHA-256:`f2c909345ae824c8780f230a0f8dc6b700930989903abecffcf986cd084f9de4`.

### unnumbered:interior-first-order-optimality

Kind:Unnumbered result. Printed pages [11]; PDF pages [23]. Required main text:True.

Under Theorem2.8 assumptions and x_star in interior(V), x_star is a minimum iff gradient f(x_star)=0.

Dependencies: Theorem 2.8.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Moreover, if`. Excerpt SHA-256:`71777f8e75bf8e4b072da4cc76fcb1346c1828aef8541244e10b99d8e4fe223b`.

### unnumbered:strict-past-FTL

Kind:Algorithm definition. Printed pages [11, 12]; PDF pages [23, 24]. Required main text:True.

FTL chooses x_t from argmin_{x in V}sum_{i=1}^{t-1}ell_i(x); first point arbitrary admissible.

Dependencies: unnumbered:game-regret.

Boundary: Argmin can be empty or tied. Printed rule does not supply universal attainment, executability, or regret guarantee.

Exact extraction anchor:`In formulas`. Excerpt SHA-256:`b864ab57508a04cba74fe336c5cf7e1533db53bf98b6a195da96f3fd9b5d059c`.

### unnumbered:weighted-distance-identity

Kind:Proof dependency. Printed pages [14]; PDF pages [26]. Required main text:True.

Sum_t[||x_t-u||^2/(2 eta_t)-||x_(t+1)-u||^2/(2 eta_t)] = ||x_1-u||^2/(2 eta_1)-||x_(T+1)-u||^2/(2 eta_T)+(1/2)sum_{t=1}^{T-1}(1/eta_(t+1)-1/eta_t)||x_(t+1)-u||^2.

Dependencies: Lemma 2.12.

Boundary: Visual check: factor1/2 already printed outside parentheses in distance fraction; no source typo claim. Proof dependency, not additional numbered result.

Exact extraction anchor:`have`. Excerpt SHA-256:`68b124b09e247333ca11a7dec51cd4bfe7e352b3c54e4a75a9588a467394d781`.

### unnumbered:fixed-unbounded-domain-residual

Kind:Unnumbered result. Printed pages [14]; PDF pages [26]. Required main text:True.

The constant-step Theorem2.13 bound holds even for D=infinity and depends on initial comparator distance. Both terminal residual terms are nonpositive and can be discarded; advanced uses keep them.

Dependencies: Theorem 2.13.

Boundary: Bounded-domain-only treatment would omit source scope.

Exact extraction anchor:`In the case of constant`. Excerpt SHA-256:`acf31834dcfd9e8d4ab919e7642c8728ee2785ca46dc4afb5f7cb5231856a801`.

### unnumbered:step-size-algebraic-minimization

Kind:Unnumbered main bound. Printed pages [15]; PDF pages [27]. Required main text:True.

For a=||u-x_1|| and S=sum||g_t||^2, source minimizes a^2/(2 eta)+eta S/2 and displays eta=a/sqrt(S), bound a sqrt(S). This unavailable oracle choice depends on future gradients (which themselves depend on eta) and unknown competitor distance.

Dependencies: Theorem 2.13.

Boundary: Positive a,S yield attained optimum over eta>0. Zero cases require separate infimum/attainment handling; source leaves positivity implicit. Hindsight minimization is not a causal algorithm.

Exact extraction anchor:`have to consider the expression`. Excerpt SHA-256:`497b143183c71ba285bf3991893af8fe05c15066a33786ebd856e9d73eb217ad`.

### unnumbered:diameter-gradient-coarse-tuning

Kind:Unnumbered main bound. Printed pages [15]; PDF pages [27]. Required main text:True.

If ||g_t||<=L and bounded diameter gives ||u-x_1||<=D, constant eta=D/(L sqrt(T)) minimizes D^2/(2 eta)+eta L^2 T/2 and gives Regret_T(u)<=D L sqrt(T), Eq2.1.

Dependencies: Theorem 2.13; unnumbered:step-size-algebraic-minimization.

Boundary: Positive horizon and nonzero D,L implicit in admissible positive step; zero cases need qualification. Distinct from decreasing-step standalone exercises.

Exact extraction anchor:`For the moment`. Excerpt SHA-256:`561d6117fa5573c468a580353269f854725f8243d95fbffc1226d728e5396807`.

### unnumbered:absolute-hinge-introduction

Kind:Unnumbered example. Printed pages [16]; PDF pages [28]. Required main text:True.

Convex nondifferentiable loss examples |x-10| and max(1-y_t<z_t,x>,0) motivate subgradients.

Dependencies: Example 2.24; Example 2.27.

Boundary: Generic hinge nondifferentiability sentence has zero-normal exception: y_t*z_t=0 gives constant differentiable loss.

Exact extraction anchor:`What happens when`. Excerpt SHA-256:`9ba42e26978b9ecb88ddb3622e5bf6305df84b27fdb7584701939dfd4a33a06e`.

### unnumbered:closed-iff-lsc

Kind:Unnumbered result. Printed pages [16]; PDF pages [28]. Required main text:True.

Closed function iff lower semicontinuous in Euclidean space; source also states general Hausdorff-space version.

Dependencies: Definition 2.16.

Boundary: Retain broader source branch for scope review. Bauschke-Combettes Lemma1.24.

Exact extraction anchor:`Note that in any Euclidean`. Excerpt SHA-256:`74d4dfc22c7c562eb90efe308aa262c8aa2c8e922c54b996f8dd22efef94b910`.

### unnumbered:subdifferential-domain

Kind:Unnumbered result. Printed pages [17]; PDF pages [29]. Required main text:True.

Proper convex f has empty partial f(x) outside dom f. Define dom(partial f)={x:partial f(x) nonempty}; it is a subset of dom f.

Dependencies: Definition 2.20; Definition 2.18; unnumbered:extended-domain-indicator.

Boundary: No further qualification identified in this reading.

Exact extraction anchor:`Observe that if`. Excerpt SHA-256:`8fa6b22c82fac34f49adf55bb56e453dba8aa1aeaccba55c29c48848c1d21b31`.

### unnumbered:interior-subgradient-existence

Kind:Unnumbered result. Printed pages [17]; PDF pages [29]. Required main text:True.

Every proper convex function has a nonempty subdifferential throughout interior(dom f).

Dependencies: Definition 2.20; Definition 2.18; Definition 2.3.

Boundary: Rockafellar Theorem23.4; not merely converse Theorem2.21.

Exact extraction anchor:`A proper convex function`. Excerpt SHA-256:`3194a3752e607297ffdd899d8772dd13a98e195c1bd5f2728e22b0f90a55facd`.

### unnumbered:relative-interior-footnote

Kind:Mathematical footnote. Printed pages [17]; PDF pages [29]. Required main text:True.

A stronger existence theorem uses relative interior(dom f); source says this book never needs it.

Dependencies: unnumbered:interior-subgradient-existence.

Boundary: Preserved mathematical source/dependency note. Independent scope review must decide strengthened-variant obligation; do not silently omit or count as numbered theorem.

Exact extraction anchor:`The stronger version`. Excerpt SHA-256:`f4921f24cf744acfa2598e6f03132e210e33e65fba7b5706c2cdf2835f3af6e6`.

### unnumbered:uncountable-nondifferentiability

Kind:Unnumbered example. Printed pages [19]; PDF pages [31]. Required main text:True.

Convex f:R^2->R, f(x)=|x_1|, is nondifferentiable along the whole segment [(0,0),(0,1)], refuting countable-only nondifferentiability.

Dependencies: Example 2.24; unnumbered:affine-composition.

Boundary: Ambient differentiability and full uncountable family; scalar isolated kink insufficient.

Exact extraction anchor:`Finally, let’s dispel`. Excerpt SHA-256:`7fae7128145f97051b190a49fec114afcb0284e0e59f1eea73914b79db22e57e`.

### unnumbered:actual-OSD-performance-transfer

Kind:Unnumbered main bound. Printed pages [19, 20]; PDF pages [31, 32]. Required main text:True.

Replacing differentiability by subdifferentiability and gradients by legal chosen subgradients preserves the OGD analysis and both sharp Theorem2.13 bounds for actual OSD. Variable decreasing steps: Regret_T(u)<=D^2/(2*eta_T)+sum_{t=1}^T eta_t*||g_t||_2^2/2-||x_(T+1)-u||_2^2/(2*eta_T). Fixed steps: Regret_T(u)<=||u-x_1||_2^2/(2*eta)+(eta/2)*sum_{t=1}^T||g_t||_2^2-||x_(T+1)-u||_2^2/(2*eta).

Dependencies: Theorem 2.13; Lemma 2.31; Algorithm 2.2.

Boundary: Need causal producer, feasibility, lawful feedback and accumulated guarantee; conditional one-step algebra alone insufficient.

Exact extraction anchor:`our analysis of`. Excerpt SHA-256:`3b48c3366ecb20fedda377a8af5eaeb96ba8b39d84a3684e02877173433a45dd`.

### unnumbered:unit-exponents

Kind:Mathematical consistency example. Printed pages [20, 21]; PDF pages [32, 33]. Required main text:True.

[g]=[ell]/[x]; OSD requires [eta]=[x]^2/[ell]; both fixed-regret terms have units [ell]. Transcendental arguments dimensionless, probabilities dimensionless, probability densities reciprocal-variable units.

Dependencies: Algorithm 2.2; Theorem 2.13.

Boundary: Dimensional algebra recorded separately from rhetoric about applications.

Exact extraction anchor:`Let’s assign a symbolic unit`. Excerpt SHA-256:`ca1df93e8a354c82ac47cfc9e96a8674153b673ed9735a0920d690a1c530ba6d`.

### unnumbered:coordinate-rescaling

Kind:Unnumbered example. Printed pages [21, 22]; PDF pages [33, 34]. Required main text:True.

For x_prime=x/1000, g_prime=1000*g. Keeping eta=1/sqrt(T) gives x_next=x-10^6*g/sqrt(T) after conversion back. Trajectory invariance requires eta_prime=eta/10^6.

Dependencies: Algorithm 2.2; unnumbered:unit-exponents.

Boundary: Exact one-million factor retained.

Exact extraction anchor:`Let me stress`. Excerpt SHA-256:`07e630635db44f1adc6286646848c114ebf44aa40c2778b5aecba201ca40a5ad`.

### unnumbered:convex-to-linear-reduction

Kind:Unnumbered main bound. Printed pages [22]; PDF pages [34]. Required main text:True.

For actual decisions and legal g_t in partial ell_t(x_t), for every u in V, sum_t(ell_t(x_t)-ell_t(u))<=sum_t<g_t,x_t-u>=sum_t(tilde ell_t(x_t)-tilde ell_t(u)), tilde ell_t(x)=<g_t,x>. Feeding these vectors to an arbitrary-linear-loss online algorithm yields OCO guarantee. OLO minimizes linear regret for arbitrary vector sequences.

Dependencies: Definition 2.20; Example 2.5; unnumbered:game-regret.

Boundary: Same actual iterates/feedback order required; reduction not always optimal, Example2.14.

Exact extraction anchor:`2.3 Linear Regret`. Excerpt SHA-256:`f8ef282d613a9ee2ddff583a40121976d5986a68549a7f7bc1f489c5d4f85d61`.

### unnumbered:minimizer-free-regret

Kind:Definition/limitation. Printed pages [23]; PDF pages [35]. Required main text:True.

Alternative sum_t ell_t(x_t)-min_{u in V}sum_t ell_t(u) requires minimizer attainment; comparator-relative regret avoids it. Fixed-step bounds can handle unbounded domains; variable-step diameter bound is vacuous at infinite diameter.

Dependencies: unnumbered:game-regret; Theorem 2.13.

Boundary: Mathematical History Bits assertions retained; historical attributions/speculation not proof obligations.

Exact extraction anchor:`the less general definition`. Excerpt SHA-256:`59a787ee14148e4198650a1459f77c66e10d9d2b547fab16a3802818e582411b`.

### forward:prescient-lookahead

Kind:Forward mathematical claim. Printed pages [14]; PDF pages [26]. Required main text:True.

Observing ell_t before output can make stability/gradient-square terms nonpositive; Section15.5.1.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`these terms become non-positive`. Excerpt SHA-256:`76eda1d8d1c97ff83f9937489bf8921f564a53627124d77755c51e991bb53c81`.

### forward:unbounded-variable-OGD-failure

Kind:Forward mathematical claim. Printed pages [14]; PDF pages [26]. Required main text:True.

OGD can fail on unbounded domains with varying steps; Section5.2.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`OGD can fail`. Excerpt SHA-256:`78ab6cf65d91bc910e501e4229ed120df39590be9a0cf3ec23b888b22c6ed4ab`.

### forward:unbounded-SGD

Kind:Forward mathematical claim. Printed pages [14]; PDF pages [26]. Required main text:True.

Stochastic SGD may use varying steps on unbounded domains; Chapter3.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`in the stochastic setting`. Excerpt SHA-256:`6add4309b975f2cd9a336b1003776ca4fc252fcf767c5fb0b361ad3d4f8dd861`.

### forward:oracle-rate-impossibility

Kind:Forward mathematical claim. Printed pages [15]; PDF pages [27]. Required main text:True.

General oracle-distance-times-energy rate ruled out by a Chapter5 lower bound.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`this kind of rate is completely impossible`. Excerpt SHA-256:`5413d9df9421ffe645cc8ff8e256193064f478c82496e10dd31c4ded0ccc60c0`.

### forward:adaptive-oracle-like

Kind:Forward mathematical claim. Printed pages [15]; PDF pages [27]. Required main text:True.

Adaptive algorithms achieve similar rates under their actual guarantees; Section4.2.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`very similar rates using`. Excerpt SHA-256:`cd7a307f3dd90a96a36c32e74286cb329be085aabe9eb355f8c4d682bc937e17`.

### forward:parameter-free

Kind:Forward mathematical claim. Printed pages [15]; PDF pages [27]. Required main text:True.

Parameter-free algorithms achieve related rates; Chapter13.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`parameter-freealgorithms`. Excerpt SHA-256:`514c5c3a4ed54486e2c1245c124bcf097e705ee546fccfcac8082e132a9bb6f2`.

### forward:minimax-DLsqrtT

Kind:Forward mathematical claim. Printed pages [15]; PDF pages [27]. Required main text:True.

DL sqrt(T) upper bound optimal up to constant factors; Chapter5.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`upper bound is optimal`. Excerpt SHA-256:`3d8b595ad8aaa05c0f1168ac8501d43bf01d94b293ec4721444c8021563823b2`.

### forward:square-OGD-improvement

Kind:Forward mathematical claim. Printed pages [15]; PDF pages [27]. Required main text:True.

Chapter4 improves OGD tuning for square guessing to optimal rate.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`make it optimal in Chapter 4`. Excerpt SHA-256:`183adbaabb9fc5e5ee8cc69a89e844d6f8c95665edc6e96b0f5757cc8fc71c26`.

### forward:FTRL-unbounded

Kind:Forward mathematical claim. Printed pages [23]; PDF pages [35]. Required main text:True.

FTRL and other algorithms can address unbounded-domain varying-step issues; Chapter7.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`using different algorithms`. Excerpt SHA-256:`e8b47f7a98181b1b0d4a52f55261905d003d5dbe073d41180acf445848aee1bf`.

### forward:offline-no-minimizer

Kind:Forward mathematical claim. Printed pages [23]; PDF pages [35]. Required main text:True.

Offline suboptimality gap can tend to zero without minimizer attainment; source points to Example3.2.

Dependencies: Theorem 2.13; unnumbered:game-regret.

Boundary: Required ownership/reconciliation edge. Exact later theorem and qualifying hypotheses not enumerated from later chapters in this Chapter2-only task; no discharge claimed.

Exact extraction anchor:`the existence of a minimizer is not required`. Excerpt SHA-256:`e42c374714b80db5e536c54b0a72ba5f7158e7215dcbfd82f51ee2cfb78ee25e`.

### Problem 2.1

Kind:Standalone exercise. Printed pages [23]; PDF pages [35]. Required main text:False.

Prove sum_{t=1}^T1/sqrt(t)<=2 sqrt(T)-1.

Dependencies: primitive context.

Boundary: Separate exercise inventory, not default main-text obligation.

Exact extraction anchor:`Problem 2.1`. Excerpt SHA-256:`bedb7463e1984710cce6c47ffe09d0bb77b7c51289deee4e3ebb6350306cdd22`.

### Problem 2.2

Kind:Standalone exercise. Printed pages [23]; PDF pages [35]. Required main text:False.

Using Problem2.1, prove eta_t=D/(L sqrt(t)) gives regret within a constant factor of Eq2.1.

Dependencies: Problem 2.1; Theorem 2.13.

Boundary: Separate exercise inventory, not default main-text obligation.

Exact extraction anchor:`Problem 2.2`. Excerpt SHA-256:`9409ed07356cf637e2156c6c53c3c8d4577c0b33ade869f1965122ac79257092`.

### Problem 2.3

Kind:Standalone exercise. Printed pages [23]; PDF pages [35]. Required main text:False.

Calculate subdifferential of epsilon-insensitive f(x)=max(|x-y|-epsilon,0).

Dependencies: Definition 2.20; Theorem 2.26; Example 2.24.

Boundary: Separate exercise inventory, not default main-text obligation.

Exact extraction anchor:`Problem 2.3`. Excerpt SHA-256:`0bab378d68c50a06f4dd75b1b673f95a2938d6f2e9ab932244aaef0b02010463`.

### Problem 2.4

Kind:Standalone exercise. Printed pages [23]; PDF pages [35]. Required main text:False.

Calculate subdifferential of f(x)=||x||_2 on R^d from definition.

Dependencies: Definition 2.20.

Boundary: Separate exercise inventory, not default main-text obligation.

Exact extraction anchor:`Problem 2.4`. Excerpt SHA-256:`df6ba7fd11ae107c3bb2504f3fe49771b0f82f5871230a569f225995739336ab`.

### Problem 2.5

Kind:Standalone exercise. Printed pages [23]; PDF pages [35]. Required main text:False.

Analyze OSD applicability, sublinear regret, and behavior versus FTL on Example2.10.

Dependencies: Algorithm 2.2; Example 2.10.

Boundary: Separate exercise inventory, not default main-text obligation.

Exact extraction anchor:`Problem 2.5`. Excerpt SHA-256:`57ab7bf1d53f29abb74227d907cef906046ff27ece7525781784da6688f3db44`.

## Preservation and validation

Raw PDF hash rechecked unchanged. Consecutive numbered-entry set and two algorithm boxes checked programmatically; formula-sensitive pages inspected visually. JSON and Markdown are append-only outputs. PNG reading evidence and generation script remain in the named tmp directory. No worktree retirement performed.

Historical memory search oriented the initial lookup only; no old implementation or completion claim adopted as current evidence.
