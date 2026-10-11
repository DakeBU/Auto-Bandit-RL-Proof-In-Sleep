# Chapter2 forward precise source candidates

Frozen v10 PDF: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, SHA-256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, unchanged.

Scope: narrow the remaining Chapter2 forward contracts and their dependencies. This is not proof advancement in later chapters or acceptance/freeze of Chapter2. Actor `/root/adaptive_decoder`, requested Astra/medium; no runtime attestation. All8 consulted ledger containers map to exact later anchors;2 additional History Bits claims are retained. Counts are ownership containers, not proof counts.

## Review findings

- All8 existing required/open ledger containers mapped;2 additional History Bits claims receive candidates. These10 ownership rows are not independent theorem/proof counts.
- No-minimizer pointer repair: Chapter2 points Example3.2 (attainment assumed); proposed target Example3.5 (logistic, unattained infimum). Independent repair review required.
- Square Example4.11 should bind directly through Theorem4.7 and gradient bound2, avoiding false open-neighborhood2-Lipschitz assertion.
- Oracle impossibility needs positive-budget5.8 plus translation, zero-padding and asymptotic contradiction; cannot simply set epsilon=0.
- Theorem3.1 probability/expectation well-definedness, Corollary7.6 attainment/closedness, and Eq13.2 direction constant remain contract-review obligations.
- Theorem15.30 constant-step proof-left-as-exercise is mandatory. Its negative stability term does not imply total regret always nonpositive.
- Appendix dependencies are explicit required specializations, not whole-appendix completion. No difficult result removed by relegating it to dependencies.
- All missing labels mean no matching source endpoint found in scoped shared-library/current-contract name/content search, not a proof that no equivalent theorem exists anywhere in mathlib.
- Shared library and candidate contract presence are not fresh source/BODY/FINAL acceptance. No compiler, proof edit, build, commit, canonical metadata change, or chapter freeze performed.

## Existing ledger mapping

- `additional:prescient-lookahead-nonpositive-stability` -> `lookahead`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter5-unbounded-variable-OGD-failure` -> `unbounded-failure`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter5-oracle-distance-energy-rate-impossibility` -> `oracle-impossibility`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter5-DLsqrtT-minimax-optimality` -> `minimax`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter3-unbounded-SGD` -> `SGD-varying`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter4-adaptive-oracle-like-rates` -> `adaptive`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter4-square-OGD-improvement` -> `square-improvement`; ledger says required/open; now source-enumerated candidate only.
- `forward:chapter13-parameter-free-oracle-like-rates` -> `parameter-free`; ledger says required/open; now source-enumerated candidate only.

## Precise target candidates

### SGD-varying

Owner: `forward:chapter3-unbounded-SGD`. Printed [24, 25]; PDF [36, 37].

- Theorem3.1: V nonempty closed convex in R^d; F(x)=E_rho[f(x,xi)], f:R^d x D->(-infinity,+infinity] convex and subdifferentiable in x on V. Draw T iid samples, deterministic alpha_t>0, ell_t(x)=alpha_t f(x,xi_t). Any causal OCO algorithm, whose internal randomness is independent of samples, gives E[F(sum alpha_t x_t/sum alpha_t)]<=F(u)+E[Regret_T(u)]/sum alpha_t for every u in V.
- Example3.2 context: finite N>=1 training pairs z_i in R^d, y_i in {-1,1}, R=max_i||z_i||_2, uniform iid training-point sampling, F(x)=N^(-1)sum max(1-y_i<z_i,x>,0), V=R^d, x_1=0. It explicitly assumes argmin F nonempty and, for eta=1/(R sqrt(T)), gives E[F(T^(-1)sum x_t)]-F(x_star)<=R(||x_star||_2^2+1)/(2 sqrt(T)), every minimizer x_star.
- Example3.3: same setting, weighted losses ell_t(x)=max(1-y_t<z_t,x>,0)/(R sqrt(t)), constant OSD eta=1. Thus update is SGD with effective unweighted step1/(R sqrt(t)). For every minimizer x_star, E[F((sum x_t/sqrt(t))/(sum1/sqrt(t)))]-F(x_star) <= (||x_star||^2+sum1/t)/(2 sum1/(R sqrt(t))) <= R(||x_star||^2+1+ln T)/(4 sqrt(T+1)-4).

Required dependencies: C2 fixed OSD bound; Jensen2.9; conditional expectation/independence; hinge2.27; harmonic and inverse-square-root sums.

Reuse: jensen, expectation, hinge, policy-fixed.

- Review: This is stochastic iid weighted averaging on an unbounded domain, not adversarial varying-step OGD. Require T>=1,N>=1,R>0 for printed denominators; R=0 needs separate branch.
- Review: Theorem3.1 leaves measurability/integrability details implicit. Exact conditional-expectation contract and independent algorithm randomness must be frozen; do not replace with supplied expected-regret assumptions alone.

Anchor `Theorem 3.1`; excerpt SHA-256 `390b4c125a8e28d2cbae7b170d76386a460c9844829ed73ac9e9c19c840161c6`.

### no-minimizer

Owner: `extra-history:offline-no-minimizer`. Printed [26]; PDF [38].

- Chapter2 printed23/PDF35 literally points to Example3.2, but Example3.2 assumes argmin F nonempty. Proposed corrected target is Example3.5, printed26/PDF38; change is not accepted here.
- Example3.5: finite training pairs z_i in R^d,y_i in {-1,1}, ||z_i||<=R, F(x)=N^(-1)sum ln(1+exp(-y_i<z_i,x>)). Uniform iid sample each round, OSD on R^d, x_1=0, eta=1/(R sqrt(T)): E[F(T^(-1)sum x_t)] <= R/(2 sqrt(T))+min_{u in R^d}(F(u)+R||u||^2/(2 sqrt(T))).
- For linearly separable data, inf F=0 and F has no finite minimizer; the comparator/regularized bound remains meaningful. The Chapter2 suboptimality-to-infimum convergence claim requires a derived epsilon-comparator limit argument; no extra finite-T convergence constant is printed.

Required dependencies: SGD-varying:Theorem3.1; logistic convexity and gradient bound; C2 fixed OSD bound; regularized minimizer attainment; epsilon-comparator limit.

Reuse: jensen, expectation, policy-fixed.

- Review: Literal wrong pointer versus proposed correction must receive independent review. No silent substitution.
- Review: R>0,N>=1,T>=1 denominator conditions; preserve no assumption argmin F nonempty. Logistic-specific terminal not found.

Anchor `Example 3.5`; excerpt SHA-256 `4c1612f6c86f88fbe0d3cfa51a8f872b86f4ad393a59f46364a80657331a215d`.

### square-improvement

Owner: `forward:chapter4-square-OGD-improvement`. Printed [37, 38]; PDF [49, 50].

- Theorem4.7: V nonempty closed convex in R^d; ell_t:R^d->(-infinity,+infinity] mu_t-strongly convex in Euclidean norm and subdifferentiable on V, mu_t>0. Algorithm2.2 with eta_t=1/(sum_{i=1}^t mu_i) gives Regret_T(u)<=1/2 sum_{t=1}^T ||g_t||_2^2/(sum_{i=1}^t mu_i) for every u in V.
- Corollary4.8: same setting, mu_t=mu>0 and each loss L-Lipschitz on an open set containing V, gives Regret_T(u)<=L^2/(2mu)*(1+ln T).
- Example4.11: square guessing on [0,1], ell_t(x)=(x-y_t)^2, y_t in [0,1], curvature2 and derivative2(x-y_t); eta_t=1/(2t) gives Regret_T(u)<=1+ln T for every u in [0,1], T>=1.

Required dependencies: strong-convexity4.1-4.2; Lemma2.31; actual Algorithm2.2; harmonic upper bound; square curvature2 and gradient<=2.

Reuse: square, mean, policy-step.

- Review: Bind Example4.11 directly through Theorem4.7 and on-domain gradient bound. Square losses are not2-Lipschitz on any open neighborhood of [0,1] when labels hit endpoints, so plugging L=2 directly into Corollary4.8 changes its premise.
- Review: Existing mean-predictor theorem has4+4 ln T, not the printed1+ln T. Need actual eta_t=1/(2t) trajectory identity and sharp guarantee; name reuse alone insufficient.

Anchor `Theorem 4.7`; excerpt SHA-256 `a87a1552d3ececf25a0d02abbc8b71c2fb16ef4902f6c3a7f9fdb7ef279c803c`.

### minimax

Owner: `forward:chapter5-DLsqrtT-minimax-optimality`. Printed [50, 51]; PDF [62, 63].

- Theorem5.1: for any nonempty bounded closed convex V subset R^d with diameter D=max_{v,w in V}||v-w||_2>0, any deterministic causal OLO algorithm on V, and every integer T>=1, there exist g_1,...,g_T with ||g_t||_2<=L and u in V such that sum_t<g_t,x_t-u> >= sqrt(2)*L*D*sqrt(T)/4.
- No symmetry of V is required (Remark5.2). Remark5.3 extends to randomized algorithms with expected regret over internal randomness; this is a separate quantifier branch, not a pathwise randomized conclusion.

Required dependencies: A.14-p1; finite-horizon causal Rademacher independence; diameter attainment; finite probabilistic method.

Reuse: No source endpoint located in scoped search.

- Review: L nonnegative/positive is implicit in norm bound and construction; freeze convention. Preserve exists sequence and comparator after arbitrary algorithm, every positive horizon.
- Review: No dedicated Theorem5.1 terminal found in scoped library/contracts search; unrelated bandit lower bounds do not establish this source statement.

Anchor `Theorem 5.1`; excerpt SHA-256 `c5f02ca2241db39e55fd49e0f4b567fcf453c83599091b2ad945b1e5f60257e1`.

### oracle-impossibility

Owner: `forward:chapter5-oracle-distance-energy-rate-impossibility`. Printed [56, 57, 58]; PDF [68, 69, 70].

- Theorem5.8: even T and a one-dimensional OLO algorithm guaranteeing Regret_T(0)<=epsilon_T>0 for every T-sequence of linear L-Lipschitz losses. Let U>0 with1<=W(sqrt(e*T)*U*L/(8 epsilon_T))<=sqrt(T)/2. Then there exist |g_t|<=L and |u|=U such that Regret_T(u)>=R_T(U):=U L sqrt(T)*(sqrt(2 W(sqrt(T)*U*L/(5 epsilon_T)))-1)-2UL+epsilon_T.
- If0<K1<=epsilon_T<=K2<infinity for all T, the source further states lim_{T->infinity} R_T(U)/(U L sqrt(T ln T))=1. For applicability use sufficiently large even horizons satisfying the displayed regime.
- Bridge to Chapter2: a universal regret bound C||u-x_1||sqrt(sum||g||^2) would give zero budget at u=x_1 and O(U L sqrt(T)) elsewhere. Translating x_1 to0 and relaxing the origin guarantee to any fixed positive epsilon allows Theorem5.8 to contradict the claimed rate at sufficiently large even T. This bridge is a required derived contract, not a numbered theorem with epsilon=0.

Required dependencies: Theorem5.5; Theorem5.7; Lambert-definition-A.1; A.4; A.17; KL-quartic; translation and asymptotic contradiction.

Reuse: No source endpoint located in scoped search.

- Review: Theorem5.8 is not a zero-budget theorem; epsilon_T is strictly positive. No blanket impossibility without its online/adversary/comparator quantifiers.
- Review: Theorem5.7 uses all-prefix nondecreasing budgets while5.8 states a fixed-horizon guarantee. A prefix guarantee can be obtained by zero-padding later losses; freeze that bridge rather than assuming it.
- Review: The displayed lower bound has sqrt(2 W(...)) minus1 outside the square root, and denominator5 epsilon_T inside W. Visually checked.

Anchor `Theorem 5.8`; excerpt SHA-256 `6f23970da65bd64c51d1d814b1ead1feb3b8bca9a76be15a4dbf5fd49b4faa0c`.

### unbounded-failure

Owner: `forward:chapter5-unbounded-variable-OGD-failure`. Printed [52]; PDF [64].

- For alpha in(0,1), phi(alpha)=1/(2-alpha)+((1/2)^(1-alpha)-1)/(1-alpha), phi maps into(0,1-ln2). For integer T>=2/((1-alpha)phi(alpha)), unprojected OSD with eta_t=t^(-alpha), x_1=0 has a sequence of T convex1-Lipschitz losses with Regret_T(0)>=phi(alpha)*T^(2-alpha)/2.
- lim_{alpha->1 from below}phi(alpha)=1-ln2>=0.3. Witness: first ceil(T/2) losses -x, remaining floor(T/2) losses+x, embedded into first coordinate for higher dimensions.

Required dependencies: explicit causal power-step trajectory; finite-sum/integral bounds; phi positivity and limit.

Reuse: unbounded.

- Review: Existing same-project terminal is a reuse candidate, not fresh BODY/FINAL acceptance. Nontrivial ambient dimension is necessary for stated positive lower bound.

Anchor `Theorem 5.4`; excerpt SHA-256 `5b00f49a4ff7b86812ad3e9b51b1a2a62ea24edc401f85487a729faea8b19759`.

### adaptive

Owner: `forward:chapter4-adaptive-oracle-like-rates`. Printed [39, 40]; PDF [51, 52].

- Eq4.3: eta_t=D/sqrt(sum_{i<=t}||g_i||^2), skip zero-feedback rounds. Eq4.4 gives Regret_T(u)<=(3/2)D sqrt(sum||g_t||^2).
- Theorem4.14: nonempty closed convex V with all pairwise distances<=D, convex extended-real losses subdifferentiable on V, x_1 in V. Use eta_t=sqrt(2)D/(2 sqrt(sum_{i<=t}||g_i||^2)), skip updates when g_t=0. For every u in V, regret<=D sqrt(2 sum||g_t||^2)=sqrt(2) min_{eta>0}(D^2/(2eta)+(eta/2)sum||g_t||^2).

Required dependencies: C2 actual OSD transfer; Lemma4.13; inverse-root limiting specialization; weighted potential; positive benchmark and degenerate infimum split.

Reuse: adaptive.

- Review: The min identity has unattained degenerate cases when exactly one of D and energy is zero. Existing infimum candidate must retain source-repair review, not silently relabel min.
- Review: This is the current adaptive package ownership edge; do not duplicate its proof or count it as a new Chapter2 theorem.

Anchor `4.2.1 Adaptive Learning Rates`; excerpt SHA-256 `243c7bd327218547ff55f77d5d1560dcd0504b3c16fc0170ee3a538cf3f256e3`.

### FTRL-unbounded

Owner: `extra-history:chapter7-FTRL-unbounded`. Printed [99, 102]; PDF [111, 114].

- Algorithm7.1: closed nonempty V subset X subset R^d; regularizers psi_t:X->R; output x_t in argmin_{x in V}(psi_t(x)+sum_{i<t}ell_i(x)) before receiving ell_t. This is strict-past cumulative loss, not OSD recursion.
- Corollary7.6: V nonempty closed convex, psi:V->R closed and mu-strongly convex in norm||.||, psi_t=(psi-min_V psi)/eta_(t-1), psi_(T+1)=psi_T, each ell_t subdifferentiable on V. For all u in V and all g_t in partial ell_t(x_t): regret <= (psi(u)-min_V psi)/eta_(T-1)+sum eta_(t-1)||g_t||_*^2/(2mu)+sum_{t=1}^{T-1}(1/eta_(t-1)-1/eta_t)(psi(x_(t+1))-min_V psi).
- If losses are L-Lipschitz on an open set containing V, choose eta_(t-1)=alpha sqrt(mu)/(L sqrt(t)), alpha>0; then regret <= ((psi(u)-min_V psi)/alpha+alpha)*L sqrt(T)/sqrt(mu). Domain need not be bounded; rates chosen before current loss.
- Concrete Euclidean unbounded specialization (also printed216/PDF228): psi_t(x)=L sqrt(t)||x||_2^2/(2alpha), V=R^d gives regret<=L sqrt(T)(||u||^2/(2alpha)+alpha).

Required dependencies: Lemma7.1; Lemma7.5; Theorem6.9; Lemma4.2; Theorem6.27; sum-rule2.23; dual Cauchy-Schwarz; inverse-root sum.

Reuse: ftl-selector.

- Review: Existing generic FTL selector is not FTRL regularization/existence/stability. Need proper/closed/subdifferentiable sum and attainment conditions reconciled from Lemma7.5; Corollary7.6 compact statement does not spell all of them out.
- Review: Positive eta,mu,L and alpha conventions explicit in candidate; monotonicity is guaranteed by displayed schedule for the simplified bound. Do not silently drop the correction sum for arbitrary schedules.

Anchor `Algorithm 7.1`; excerpt SHA-256 `3e811011cbc445b98f2c65e0c5a6e396cfb11ae5e88e4f318d9e4fea3b7b7b92`.

### parameter-free

Owner: `forward:chapter13-parameter-free-oracle-like-rates`. Printed [213, 214, 215, 216]; PDF [225, 226, 227, 228].

- Algorithm13.2: epsilon>0,L>0; predict x_t=-(sum_{i<t}g_i)/(tL)*(epsilon-sum_{i<t}(g_i/L)x_i), receive subdifferentiable loss on R and choose |g_t|<=L in its subdifferential. Unnumbered printed214/PDF226 guarantee: for every u in R, regret<=|u|L sqrt(2T ln(1+e|u|T/epsilon))+epsilon L.
- Definition13.7: parameter-free means optimal dependence on T and all feasible comparators up to polylogarithmic factors; knowledge of Lipschitz constant is allowed. This is not literal no input parameters, since epsilon,L remain.
- For arbitrary-dimensional Euclidean comparator dependence, Eq13.2: use Algorithm12.3 with KT scalar learner and OSD direction learner on Euclidean unit ball, x_1=0, eta_t=sqrt(2)/(2L sqrt(t)). For every u in R^d, regret<=L||u||_2*(sqrt(ln(1+e||u||_2*T/epsilon))+1)*sqrt(2T)+L epsilon.
- Theorem13.9 is a separate coordinatewise variant: Algorithm13.3 with epsilon>0,L_infinity>0 and ||g_t||_infinity<=L_infinity yields regret<=L_infinity sum_i |u_i|sqrt(2T ln(1+e|u_i|T/epsilon))+d epsilon L_infinity <=||u||_1 L_infinity sqrt(2T ln(1+e||u||_infinity*T/epsilon))+d epsilon L_infinity.
- Printed216 also states an Lp variant,1<p<=2,1/p+1/q=1: regret<=L_q*(||u||_p sqrt(ln(1+e||u||_p*T/epsilon))+||u||_p/sqrt(p-1))*sqrt(2T)+L_q epsilon, with OMD direction rate sqrt(p-1)/(L_q sqrt(2t)).

Required dependencies: KT13.4; duality13.5; conjugate13.6; magnitude-direction12.16; C2 linearization; Euclidean directional learner sharp bound; A.1; A.6-upper; A.8-10; A.11-12; A.13; entropy6.33.

Reuse: No source endpoint located in scoped search.

- Review: Minimal proposed Chapter2 Euclidean edge is scalar KT plus magnitude/direction Eq13.2. Coordinatewise and Lp variants are recorded, not automatically claimed necessary for this narrower edge; later whole-Chapter13 obligations remain untouched.
- Review: Exact directional learner constant in Eq13.2 needs its own audit; cannot infer it merely by substituting diameter2 into the generic C2 bound.
- Review: Primitive gamma/Lambert infrastructure and these source-specific terminals were not located in the scoped shared-library search.

Anchor `Algorithm 13.2`; excerpt SHA-256 `06a0a2823a345cbad22b75900c17e8b7da4b69423f04a09065d6707a0ef22f7c`.

### lookahead

Owner: `additional:prescient-lookahead-nonpositive-stability`. Printed [265, 266]; PDF [277, 278].

- Algorithm15.8: nonempty closed convex V subset X, strictly convex psi:X->R differentiable on int X, x_0 in int X, positive eta_t. Receive whole loss ell_t with V subset dom ell_t before choosing x_t in argmin_{x in V}(ell_t(x)+B_psi(x;x_(t-1))/eta_t), then pay ell_t(x_t).
- Theorem15.30: additionally psi closed, iterates x_t in int X, losses subdifferentiable on V, nonincreasing steps. For every u in V: regret<=max_{0<=t<=T-1}B_psi(u;x_t)/eta_T-sum_{t=1}^T B_psi(x_t;x_(t-1))/eta_t. Constant eta: regret<=B_psi(u;x_0)/eta-sum B_psi(x_t;x_(t-1))/eta. The constant-step proof is explicitly left as an exercise and remains mandatory.
- Euclidean psi(x)=||x||^2/2 specializes the negative stability term to -sum||x_t-x_(t-1)||^2/(2eta_t), with no positive gradient-square term. The total bound need not be nonpositive because the initial comparator potential is positive.
- Section15.5.1 also has Algorithm15.9 BTRL: after seeing ell_t choose x_t in argmin(psi_t+sum_{i<=t}ell_i). Theorem15.31 (printed266-267/PDF278-279) assumes these sums proper, closed and lambda_t-strongly convex; regret<=psi_T(u)-psi_1(x_1)-sum_{t=1}^T lambda_t||x_t-x_(t+1)||^2/2+sum_{t=1}^{T-1}(psi_t(x_(t+1))-psi_(t+1)(x_(t+1))). This is an alternate section route, not the same algorithm as15.8.

Required dependencies: Bregman6.4; three-point6.7; extended proximal optimality; sum-rule2.23; nonnegative Bregman; weighted potential; alternate BTRL:7.47.

Reuse: prescient.

- Review: Source proof invokes differentiable Theorem2.8 while ell_t is merely subdifferentiable; the existing extended proximal source package is a candidate repair/qualification route requiring its receipts.
- Review: Whole-function current lookahead must be explicit; this cannot be branded an ordinary causal output-before-current-loss algorithm.
- Review: 15.31 terminal x_(T+1) and its hypotheses need separate source audit if alternative BTRL route is adopted. No automatic requirement to prove entire15.5.1 to satisfy narrower negative-stability edge.

Anchor `Algorithm 15.8`; excerpt SHA-256 `fd74bb527b82b529cefe9258768e11c463cbaf9d8a38435b750da4836eca0cb0`.

## Required dependency candidates

### strong-convexity4.1-4.2

Printed [34, 35]; PDF [46, 47]. Proper f, lambda>=0, convex V subset dom f: f(a x+(1-a)y)<=a f(x)+(1-a)f(y)-lambda*a*(1-a)||x-y||^2/2. For convex V subset dom partial f, equivalent to f(x)>=f(y)+<g,x-y>+lambda||x-y||^2/2 for all x,y in V and g in partial f(y).

Depends on: primitive context. 

Anchor `Definition 4.1`; excerpt SHA-256 `9e6c9ff890263f773cfbd347de13be275897129998f2899ab6b89abc0fc10cda`.

### Theorem5.5

Printed [54, 55]; PDF [66, 67]. Even T>=1, integer0<q<=T/2, L>0; any causal coin bettor starting epsilon and maintaining nonnegative wealth on all {+-L}^T sequences has a sequence with |sum c_t|>=2qL and wealth<=(3epsilon/2)(2q/sqrt(T)+1)exp(T KL_Bern(1/2+q/T;1/2)) <=same prefactor*exp(2q^2/T+3.1q^4/T^3).

Depends on: A.17; KL-quartic. 

Anchor `Theorem 5.5`; excerpt SHA-256 `9d7a0cfaa39829ff87b0ffc8cbfad9580417630465ed8e6f9b500632f742f6ba`.

### Theorem5.7

Printed [56]; PDF [68]. Nonnegative nondecreasing epsilon_t, OLO algorithm with Regret_t(0)<=epsilon_t for every bounded-gradient prefix. For every T>=0 there are beta_t with x_t=beta_t(epsilon_T-sum_{i<t}<g_i,x_i>) and ||beta_t||<=1/L, t=1..T.

Depends on: causal adversary. L>0 implicit; zero wealth needs zero bet branch.

Anchor `Theorem 5.7`; excerpt SHA-256 `8d5d0450d7616a2722e8135cd1ba25a0e9ffa815b7b349761b4b7200a01bb391`.

### KL-quartic

Printed [55]; PDF [67]. KL_Bern(1/2+x;1/2)<=2x^2+3.1x^4 for |x|<=1/2. Endpoint0 log0 convention retained.

Depends on: primitive context. Unnumbered main proof inequality, required for5.5 and5.8 constants.

Anchor `For the second upper bound`; excerpt SHA-256 `3bac36914b24f575cf9c44dabb01d27a5b3cac7e09ab91ef2dfb9fcdcfeb6189`.

### Lambert-definition-A.1

Printed [291]; PDF [303]. W:[0,infinity)->[0,infinity], x=W(x)exp(W(x)); for x>0 exp(W(x)/2)=sqrt(x/W(x)).

Depends on: primitive context. 

Anchor `The Lambert function`; excerpt SHA-256 `8a6b63f1fae24f6a1e54c5400cc4c78fdc2e95a19803f2ef9e1feea56d2390cf`.

### A.4

Printed [291]; PDF [303]. lim_{x->infinity}W(x)/ln x=1.

Depends on: Lambert-definition-A.1. Stated without proof in source; required for5.8 asymptotic, not dispensable.

Anchor `Theorem A.4`; excerpt SHA-256 `e59e58f31602b5092e9666bf523b34d276c9edc6f5e9d619a32d2ed1f6d0223b`.

### A.6-upper

Printed [292]; PDF [304]. For all x>=0,0.6321 ln(1+x)<=W(x)<=ln(1+x). Only upper inequality is needed by Lemma13.6; source labels it Theorem A.6 although13.6 calls it Lemma A.6.

Depends on: Lambert-definition-A.1; A.5. Full lower constant not required by selected KT upper-bound route; remains a later appendix obligation.

Anchor `Theorem A.6`; excerpt SHA-256 `45c4c9fd386678b9596b4f27cf5f80275ca1824b34aab3f854ba56e60f73bd26`.

### A.5

Printed [291]; PDF [303]. W(x)<=ln((x+C)/(1+ln C)) for x>=0 and C>1/e; C=1 yields A.6 upper bound.

Depends on: Lambert-definition-A.1. Fraction is inside logarithm; rendering/extraction must be checked if this exact route is formalized.

Anchor `Theorem A.5`; excerpt SHA-256 `85da1886f59368da5672b141500a96c56e693f6e388e499c6dcb42654ddee9d7`.

### A.14-p1

Printed [296]; PDF [308]. Required specialization: iid Rademacher epsilon_1,...,epsilon_N, real coefficients a_i, E|sum epsilon_i a_i| >= (1/sqrt(2))*sqrt(sum a_i^2). For all a_i=1: E|sum epsilon_i|>=sqrt(N/2).

Depends on: primitive context. Full printed theorem is complex-coefficient p in(0,infinity) Khintchine with A_p/B_p; p=1 lower half is exact sufficient dependency for5.1, not whole appendix completion.

Anchor `Theorem A.14`; excerpt SHA-256 `2da346759130cd1fd55692c14d2f9acbf00640f6aad1c3107505c87bd4c2c274`.

### A.15

Printed [296, 297]; PDF [308, 309]. Integers n>=1,n/2<=k<=n; phi(k,n)=sqrt(4k^2-4kn+(n+2)^2)/2-k-n/2-1. Sum_{i=k}^n binom(n,i)>=binom(n,k)*k/(2k+phi(k,n)); phi nonincreasing in k.

Depends on: primitive context. Needed by binomial-tail lemma; exact radical visually inspected.

Anchor `Lemma A.15`; excerpt SHA-256 `f7507553b46ed6ef2e830ab9c2b7dc01ca0273947a7cf6aebb3c2c27064d45a4`.

### A.17

Printed [297, 298]; PDF [309, 310]. Even integer n>=1 and integer0<=q<=n/2-1, X~Binomial(n,1/2): P(X>=n/2+q)>=(1/[3(2q+sqrt(n))])*sqrt(n*(n/2+q)/(n/2-q))*exp(-n KL_Bern(1/2+q/n;1/2)) >= exp(-n KL_Bern(...))/(3(2q/sqrt(n)+1)). Second bound also holds q=n/2.

Depends on: A.15; Robbins-factorial. Endpoint separate;0 log0=0.

Anchor `Lemma A.17`; excerpt SHA-256 `fff5a75a857258bdf97aa08a4dc87f5000e9a6de4c7252badd77be99e9944a32`.

### Robbins-factorial

Printed [298]; PDF [310]. For integer n>=1: sqrt(2 pi n)(n/e)^n<n!<exp(1/12)sqrt(2 pi n)(n/e)^n.

Depends on: factorial and exponential. External attribution Robbins1955; exact displayed weakening is needed, not outside paper lookup.

Anchor `Stirling’s formula`; excerpt SHA-256 `12647c0f6cdb851eafe8531c9bab4396e496b347045233d2fccf850da91d978f`.

### Lemma7.1

Printed [100]; PDF [112]. Regularizers psi_1..psi_(T+1):X->R; closed nonempty V subset X; F_t=psi_t+sum_{i<t}ell_i, each argmin_V F_t nonempty, x_t chosen in it. For every u in X, regret=psi_(T+1)(u)-min_V psi_1+sum_t[F_t(x_t)-F_(t+1)(x_(t+1))+ell_t(x_t)]+F_(T+1)(x_(T+1))-F_(T+1)(u). psi_(T+1) does not affect first T iterates.

Depends on: primitive context. Extended-real finite/arithmetic conditions require reconciliation; do not erase sharp identity.

Anchor `Lemma 7.1`; excerpt SHA-256 `cc45ee4a232be44135ed806987eb85feec6fed494f77dd318bacf5a7f83734fc`.

### Lemma7.5

Printed [101, 102]; PDF [113, 114]. For nonempty closed convex V, F_t closed/subdifferentiable/strongly convex gives unique x_t. If partial ell_t(x_t) nonempty and F_t+ell_t closed/subdifferentiable/lambda_t-strongly convex, stability<=<g_t,x_t-x_(t+1)>-lambda_t||x_t-x_(t+1)||^2/2+psi_t(x_(t+1))-psi_(t+1)(x_(t+1))<=||g_t||_*^2/(2lambda_t)+same regularizer difference, every g_t in partial ell_t(x_t).

Depends on: Theorem6.9; strong-convexity4.1-4.2; Theorem6.27; C2 sum-rule2.23. 

Anchor `Lemma 7.5`; excerpt SHA-256 `8634f446d9873c3c4b79dee2f537903a2c82d7c3bdc31a84f9687515a1ca85c3`.

### Theorem6.9

Printed [66]; PDF [78]. lambda>0; proper closed lambda-strongly convex f:R^d->(-infinity,+infinity] on its domain with dom partial f nonempty has exactly one minimizer.

Depends on: strong-convexity4.1-4.2; A.3. 

Anchor `Theorem 6.9`; excerpt SHA-256 `4f1f105611f218746222467059ebc85bb0bba3711424688dc739832d5d64ce5a`.

### A.3

Printed [291]; PDF [303]. Hausdorff X, lower-semicontinuous f:X->[-infinity,+infinity], compact V with V intersect dom f nonempty: f attains infimum over V.

Depends on: primitive context. For selected Euclidean FTRL route finite-dimensional compact sublevel specialization sufficient; full Hausdorff theorem not inferred.

Anchor `Theorem A.3`; excerpt SHA-256 `92f00a665ee2707c5e27cb20f0c3a1b8d6576255aae0e38f172e40fa0d4d11de`.

### Theorem6.27

Printed [74]; PDF [86]. Proper f:R^d->(-infinity,+infinity]: x_star is a global minimizer iff0 in partial f(x_star).

Depends on: primitive context. 

Anchor `Theorem 6.27`; excerpt SHA-256 `f885747f922d721632d3ab18340424bf46efee7f5805d3d059399964e203437d`.

### KT13.4

Printed [210, 211]; PDF [222, 223]. For arbitrary c_t in[-1,1], initial epsilon>0, KT beta_t=sum_{i<t}c_i/t and wealth update W_t=W_(t-1)(1+beta_t c_t) satisfy W_T>=epsilon*2^T*Gamma((T+1+sum c)/2)*Gamma((T+1-sum c)/2)/(pi Gamma(T+1))>=epsilon exp((sum c)^2/(2T)-(ln T)/2-1).

Depends on: A.8-10; A.11-12; A.13; entropy6.33. T>=1 for displayed exponent. Gamma recurrence at c=+-1 is referred to standalone Problem13.1 but is a mandatory proof dependency when using this main theorem; not excluded as an exercise.

Anchor `Theorem 13.4`; excerpt SHA-256 `0b9de0f44f2dbf8583cc65ba2335e5184d261d1ce178f660d33660f5f72bfbed`.

### duality13.5

Printed [211, 212]; PDF [223, 224]. Proper closed convex phi:R^d->(-infinity,+infinity], arbitrary finite x_t,g_t: -sum<g_t,x_t>>=phi(-sum g_t) iff for every u in R^d sum<g_t,x_t-u><=phi_star(u).

Depends on: Fenchel6.12-6.13. Convex conjugate and biconjugacy, not merely scalar algebra.

Anchor `Theorem 13.5`; excerpt SHA-256 `545eb94b7fd87d01f7809d4d7869272fdd99b9f2c89da10410e99ec41bf9081f`.

### conjugate13.6

Printed [213]; PDF [225]. alpha,beta>0, f(x)=beta exp(x^2/(2alpha)); f_star(y)=|y|sqrt(alpha W(alpha y^2/beta^2))-beta exp(W(alpha y^2/beta^2)/2) <=|y|sqrt(alpha W(...))-beta <=|y|sqrt(alpha ln(1+alpha y^2/beta^2))-beta <=|y|sqrt(2alpha ln(1+sqrt(alpha)|y|/beta))-beta.

Depends on: Lambert-definition-A.1; A.6-upper; Fenchel6.12-6.13. At y=0 exact value -beta retained. AppendixA.7 duplicates related conjugate formula and has division-by-zero representation at zero; not needed as additional dependency for this route.

Anchor `Lemma 13.6`; excerpt SHA-256 `61167f6b6089c09b72d536d38f0843bc5221a9f61f12e55e827bdf40069ab4d8`.

### magnitude-direction12.16

Printed [203, 204]; PDF [215, 216]. Algorithm12.3 receives z_t from scalar learner and v_t in unit ball from direction learner, plays x_t=z_t v_t, selects g_t, sends scalar loss s_t z with s_t=<g_t,v_t> and vector loss<g_t,v>. For u!=0: regret_OCO(u)<=linear_regret(u)=Regret_scalar(||u||)+||u||Regret_ball(u/||u||). At u=0 regret<=Regret_scalar(0); |s_t|<=||g_t||_*.

Depends on: C2 global support; dual norm inequality. The zero comparator is a distinct branch, no division by zero.

Anchor `Theorem 12.16`; excerpt SHA-256 `aaff7fc1865ad330e042dbf2820212214454e54d9f933c282daf6c416ae6a9c6`.

### Fenchel6.12-6.13

Printed [68, 69]; PDF [80, 81]. f_star(theta)=sup_x(<theta,x>-f(x)); Fenchel-Young for proper f; for closed proper convex f, f_star is closed proper convex and f_star_star=f.

Depends on: C2 closed/proper/convex. Use exact proper specialization required by13.5; not all statements of Chapter6 advanced.

Anchor `Definition 6.12`; excerpt SHA-256 `61586432fcbb9a80b8e9cc3c5847f795208c9c23c2775b63dd5cfa38e11c2238`.

### entropy6.33

Printed [80]; PDF [92]. c_i>0, psi(x)=sum c_i x_i ln x_i is1-strongly convex in L1 on {x_i>0,sum x_i/c_i=1}. c_i=1 yields KL(p;q)>=||p-q||_1^2/2 via Eq6.4; endpoint extension separately supplies Bernoulli quadratic lower bound.

Depends on: strong-convexity4.1-4.2; Jensen2.9. Needed for exponent in13.4; alternate direct Bernoulli inequality could replace only with proved equivalent dependency.

Anchor `Lemma 6.33`; excerpt SHA-256 `9c9f787f3b7fd2d96b21b497c44e71a75a81ba8ea918b30ea1647b65d9251064`.

### A.8-10

Printed [294]; PDF [306]. Gamma(z)=integral_0^infinity t^(z-1)e^(-t)dt for Re z>0; digamma psi=(ln Gamma)prime. Required A.10 properties: log-convexity; (x/(x+s))^(1-s)<=Gamma(x+s)/(x^s Gamma(x))<=1 for0<s<1,x>0; Gamma(x)>=((x-1/2)/e)^(x-1/2)sqrt(2e) for x>=1; digamma increasing/concave, ln x-1/x<=psi(x)<=ln x-1/(2x); psi_prime(x)=sum_{k>=0}(x+k)^(-2).

Depends on: primitive context. Gamma recurrence and Gamma(1/2)=sqrt(pi) also used in KT proof; no blanket assertion all primitive API missing.

Anchor `Definition A.8`; excerpt SHA-256 `5b4ba7922d15d2e7186647b39423a05b1d047e4675869a3e009277fb80154ea6`.

### A.11-12

Printed [294, 295]; PDF [306, 307]. Integers T>=1,d>=2: Gamma(T+d/2)/Gamma(T+1/2)<=(T+d/2-1/2)^((d-1)/2). LemmaA.12: ln(sqrt(pi) Gamma(T+d/2)/(Gamma(d/2)Gamma(T+1/2))) <=(d-1)/2 ln(T/((d-1)/2)+1)+d/2-1+(1/2)ln(pi/2). For d=2, <=(ln T)/2+1.

Depends on: A.8-10. Only d=2 final ratio bound required by selected KT route; full general result remains outside proof advancement.

Anchor `Lemma A.11`; excerpt SHA-256 `38541339604760560c314dc3bfc384225d166f478ebc8692ffbd9d59c067223c`.

### A.13

Printed [295, 296]; PDF [307, 308]. For real T>=1, integer n>=1, product_i a_i^(a_i)/Gamma(a_i+1/2), with0^0=1, is maximized on nonnegative simplex sum a_i=T at extreme points (one coordinate T, rest0).

Depends on: A.8-10; Jensen2.9. n=2 specialization required by13.4; proof uses trigamma series and convex midpoint-integral bound.

Anchor `Lemma A.13`; excerpt SHA-256 `9d78f23c02bc76a5accdcd1ceaae3065f1feb1c14dad46bce73482f5ff48ff35`.

### Bregman6.4

Printed [63]; PDF [75]. Strictly convex psi:X->R differentiable on nonempty int X; B_psi(x;y)=psi(x)-psi(y)-<gradient psi(y),x-y>, x in X,y in int X.

Depends on: C2 first-order support. Nonnegative under stated convexity; second slot interior matters.

Anchor `Definition 6.4`; excerpt SHA-256 `14e499236f01b3f4ea94ea8b9071c9236cad11f749476a45eddbea02a02f2d25`.

### three-point6.7

Printed [64]; PDF [76]. For x,y in int X,z in X: B(z;x)+B(x;y)-B(z;y)=<gradient psi(y)-gradient psi(x),z-x>.

Depends on: Bregman6.4. 

Anchor `Lemma 6.7`; excerpt SHA-256 `9b3afe81bb0ff32f56906896d77e95070476201eb493c815e83b0c67e66bbb85`.

## Existing same-project reuse candidates

Header/declaration presence is retrieval evidence only. No compile or semantic-acceptance claim. JSON records file hashes and retrieved header excerpts.

- **jensen**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineJensen.lean` (SHA-256 `cca057991a262fa6bb2a9259bd59aa3468e6a970cc7cc53a508f7a647b327eda`): `BanditRL.OnlineConvex.theorem_2_9` line44.
- **expectation**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineExpectation.lean` (SHA-256 `9642870c76c5001b002671e447bd6f29bc1e3d0c132f784783ce90d5944f8c31`): `BanditRL.OnlineConvex.signedExpectation` line34, `BanditRL.OnlineConvex.signedExpectation_coe_integrable` line58.
- **hinge**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineHinge.lean` (SHA-256 `d3c7ec649a5d231bd30d472ce70bfed20ecdf7069cba30cb630297f99ce16871`): `BanditRL.OnlineConvex.example_2_27` line182.
- **policy-fixed**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineSubgradientPolicy.lean` (SHA-256 `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662`): `BanditRL.OnlineSubgradientPolicy.regret_fixed` line171, `BanditRL.OnlineSubgradientPolicy.regret_fixed_coarse` line198.
- **policy-step**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineSubgradientPolicy.lean` (SHA-256 `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662`): `BanditRL.OnlineSubgradientPolicy.one_step_chain` line135, `BanditRL.OnlineSubgradientPolicy.output_prefix` line108.
- **square**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineGuessingOGD.lean` (SHA-256 `12792af1571fde0fe37796686b044f0df0990ca3d808a89431804605d0ee8d00`): `BanditRL.OnlineGradientDescent.project_unitInterval` line26, `BanditRL.OnlineGradientDescent.gradient_square` line57, `BanditRL.OnlineGradientDescent.gradient_square_bound` line61, `BanditRL.OnlineGradientDescent.square_step_clamp` line66, `BanditRL.OnlineGradientDescent.example_2_14` line74.
- **mean**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningFTL.lean` (SHA-256 `8c3574c657f08e0c5291f0689105f9459e92187502f092f4d36d848e52ab4219`): `BanditRL.OnlineLearning.theorem_1_3` line81, `BanditRL.OnlineLearning.meanPredict_regret_refined` line106.
- **ftl-selector**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineFTLSelector.lean` (SHA-256 `cd1cae5683edaa40fde18466f1efbca8ad34b295d8dfc3b173a35e0d459405df`): `BanditRL.OnlineFTLSelector.select` line16, `BanditRL.OnlineFTLSelector.predict` line20, `BanditRL.OnlineFTLSelector.predict_prefix` line120.
- **unbounded**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineUnboundedOSD.lean` (SHA-256 `a026fb7d45e5844d163664e75c562273dc835f1daa485ba9289f3a76d946ece8`): `BanditRL.OnlineUnboundedOSD.theorem_5_4` line516, `BanditRL.OnlineUnboundedOSD.phi_limit` line92.
- **adaptive**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineAdaptiveOSD.lean` (SHA-256 `197f1f6460168daafe23f4a8017f2c11b54566e0f7749da77bd031d4ab7babef`): `BanditRL.OnlineAdaptiveOSD.source_eq4_4` line320, `BanditRL.OnlineAdaptiveOSD.source_theorem4_14` line335, `BanditRL.OnlineAdaptiveOSD.canonical_theorem4_14` line369.
- **prescient**: `E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlinePrescientBregmanSource.lean` (SHA-256 `57832c9dfb4e915f9a0578ffb122792b0aac2b3404da4f6c00f2aa9fcd36bc02`): `BanditRL.OnlineConvex.source_fixed_regret` line130, `BanditRL.OnlineConvex.source_variable_regret` line160.

Contract locators, with hashes in JSON:

- `E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/qualified-source-reconciliation-draft-v4.json`
- `E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-prescient-source-v1/stabilized-v1.json`
- `E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-unbounded-osd-v1/stabilized-v1.json`
- `E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-adaptive-osd-v1/specialization-stabilized-v1.json`

## Validation and preservation

PDF hash rechecked; formula-sensitive pages visually inspected; exact source snippets and all read page text fingerprints retained in JSON. No source, proof, canonical metadata, build or commit changed. Append-only reports and tmp rendering/script evidence preserved. Independent source review is the next gate.
