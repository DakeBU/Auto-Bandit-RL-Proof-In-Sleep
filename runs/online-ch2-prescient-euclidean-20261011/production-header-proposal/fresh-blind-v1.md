# Fresh blind decoder v1

Role: fresh blind decoder. Requested model: Astra; requested effort: medium. Runtime attestation: false.

Only the three supplied UTF-8 files were read. Their raw SHA-256 hashes matched the assigned values:
- `neutral-complete-headers-v1.txt`: `1d6cda54b46476323dccaeae6fc3b33e8d1494bb655b99045ea2cde569b8e20a`
- `neutral-imported-definitions-v1.txt`: `dff55f4b3262afa2869e8dce05cf27bde92b8ef94945f31c7a198a0c8f39c9a1`
- `neutral-standard-definitions-v1.txt`: `a5bf043f78dca8dc95e501b13ee41c9bfef17638ba2ecd2145edb833c5a0e06e`

## Decoded mathematical meaning

### shared_definitions

- E is a real inner product space with its normed additive commutative group structure. quadratic_geometry additionally assumes completeness, allowing arbitrary Hilbert spaces. The regret headers instead assume finite dimensionality over R; completeness follows mathematically from finite dimensionality.
- effectiveDomain(f) = {z | f(z) < +infinity}; by itself this includes -infinity. The separate hbot assumption excludes -infinity everywhere for each active round. Together hbot and hdom make active-round losses finite real values on V.
- SourceSubdifferential(f,z) consists of vectors g with f(z) + <g,y-z> <= f(y) for EVERY y in E, using extended-real addition and order. Nonemptiness at each z in V is a global supporting-hyperplane condition, not merely an inequality against y in V. No differentiability of losses is stated.
- divergence(psi,x,y) = psi(x)-psi(y)-Dpsi(y)[x-y], using the total Lean fderiv operation. It does not itself assert differentiability, convexity, or nonnegativity. For the quadratic psi the first header identifies it as squared distance divided by two.
- HasGradientAt(f,g,y) means Frechet differentiability at y with derivative represented by the continuous dual image of g, namely h -> <g,h> in the real case. The provided filter definition uses the neighborhood filter of y paired with pure y.
- IsMinOn(F,V,p) means F(p) <= F(z) for every z in V through the principal filter definition. It alone does not require p in V; hmin and advance explicitly add membership.
- advance(V,psi,eta,f,x) returns some classically chosen p in V attaining the global minimum of f(z)+eta^(-1)*divergence(psi,z,x) over V if such a p exists. Otherwise it returns none. It does not select approximate minimizers and supplies no numerical algorithm or tie-breaking rule.
- iterate(0)=some x0. iterate(t+1) binds iterate(t) to advance with eta(t) and loss(t). Once none is returned, subsequent iterates stay none. Initialization is unconditional, even when x0 is outside V.

### quadratic_geometry

**quantifiers:** For every real complete inner product space E and every x,y in E.

**premises:** Only the stated space structures; no membership constraints or additional pointwise assumptions.

**conclusion:** For psi(z)=||z||^2/2, HasGradientAt(psi,y,y) AND divergence(psi,x,y)=||x-y||^2/2.

**interpretation:** The gradient vector at y is y; divergence evaluates its first argument x relative to its base point y. Both conclusions are exact identities/properties, not bounds.

### regret_shared

**quantifiers:** Universally quantified finite-dimensional real inner product space E; V subset E; extended-real losses indexed by every natural number; x0 in E; trajectory x:N->E; horizon T:N; and comparator u in V. There is no existentially constructed trajectory in either conclusion.

**set_premises:** V is convex, nonempty, and closed. It need not be bounded or compact. x0 and x(0) are not required to belong to V.

**initialization:** x(0)=x0.

**loss_premises:** For each t<T, loss(t,z) is never -infinity for ANY z in E; V is contained in its effective domain; and at each z in V its SourceSubdifferential is nonempty. +infinity outside V is permitted. No restrictions apply to losses at t>=T.

**minimizer_premises:** For each t<T, x(t+1) belongs to V and globally minimizes loss(t,z)+||z-x(t)||^2/(2*eta_t) over z in V. Exact attainment is assumed for the supplied trajectory at every active round.

**run_conclusion:** For EVERY natural t<=T, the Option-valued iterate with quadratic regularizer equals some x(t). This includes initialization and the terminal point x(T), rules out selector failure through T, and identifies the supplied minimizers with the classically selected ones. Although hmin does not explicitly assert uniqueness, the conclusion requires that identification for every trajectory satisfying the premises; the supporting-plane hypotheses and positive quadratic penalty supply the mathematical strict-convexity mechanism on convex V.

**scoring:** The left side is sum over t=0,...,T-1 of [toReal(loss(t,x(t+1)))-toReal(loss(t,u))]. Scoring uses the UPDATED point x(t+1) with the SAME round loss used in its minimization, not the pre-update point x(t). This is a fixed-comparator cumulative loss difference, with no averaging, expectation, supremum over comparators, or additional gradient term.

**finiteness:** Every scored loss is finite because x(t+1) and u lie in V and the active-round domain/no-bottom assumptions hold. Thus EReal.toReal here really equals the corresponding finite real value, rather than relying on its behavior at infinities.

**beyond_horizon:** No run-validity or regret claim beyond T. Values of x after T and eta/loss outside the mentioned round ranges are unconstrained.

### euclidean_variable_regret

**additional_quantifiers:** eta:N->R and T>0.

**additional_premises:** eta(t)>0 for each t<T; eta(t+1)<=eta(t) whenever t+1<T. Thus eta is nonincreasing on 0,...,T-1 only.

**definitions:** Let D_t=||u-x(t)||^2/2 and S_t=||x(t+1)-x(t)||^2. Let M=max_{0<=t<T} D_t, a finite maximum over the nonempty Finset.range T.

**bound:** sum_{t=0}^{T-1} [loss(t,x(t+1))-loss(t,u)] <= M/eta(T-1) - sum_{t=0}^{T-1} S_t/(2*eta(t)), with scored losses interpreted through toReal.

**bound_terms:** The maximum includes x(0)=x0 through x(T-1), and excludes x(T). It depends on this comparator and this finite supplied trajectory, not a diameter or a uniform supremum over V. Its denominator is the LAST ACTIVE rate eta(T-1), the smallest active rate under hmono. Each movement penalty has its own positive active rate.

**terminal_handling:** x(T) is included in the final score and final movement penalty and in the run conclusion. No negative terminal comparator-distance term -D_T/eta(T-1) appears. Natural subtraction T-1 is unambiguous here because T>0.

**edge_cases:** T=0 is excluded. For T=1 monotonicity is vacuous; M=D_0 and the bound has only the first movement penalty. Behavior of eta(T) is irrelevant.

### euclidean_fixed_regret

**additional_quantifiers:** A single real eta>0; T is any natural number, including zero. The iterate uses the constant sequence t -> eta.

**bound:** sum_{t=0}^{T-1} [loss(t,x(t+1))-loss(t,u)] <= ||u-x0||^2/(2*eta) - [sum_{t=0}^{T-1} ||x(t+1)-x(t)||^2]/(2*eta), with scored losses interpreted through toReal.

**bound_terms:** The initial comparator-distance term uses x0, equal to x(0). The complete squared-movement sum is subtracted with one common denominator 2*eta. There is no trajectory maximum, varying-rate adjustment, or comparator optimum on the right.

**terminal_handling:** x(T) contributes to the final score and movement when T>0 and is included in run validity. The bound omits any negative terminal comparator-distance correction -||u-x(T)||^2/(2*eta).

**edge_cases:** At T=0, hbot/hdom/hs/hmin are vacuous; sums are zero, and the inequality reduces to 0<=||u-x0||^2/(2*eta). Run validity only identifies some x0 with some x(0), by hinit. eta positivity, convexity, nonemptiness, closedness and u in V are still premises.

### intrinsic_narrowing_and_vacuity

- Regret results are limited to finite-dimensional real inner product spaces, while the geometry identity allows complete infinite-dimensional ones.
- Results are conditional on a supplied exact minimizer trajectory; they do not explicitly assert existence of such a trajectory from the other premises alone.
- Global supporting vectors at every feasible point exclude losses/feasible boundary behavior for which such vectors do not exist. This is stronger than merely asking for convexity restricted to V, and includes comparison against infeasible points as well.
- Nonemptiness and comparator membership prevent the intended feasible-set situation from being empty, although hVn is redundant once hu is supplied.
- No premise requires the initial point to be feasible or its round-zero loss finite; its score is never used. The quadratic distance is defined everywhere.
- Variable-rate maximum is automatically finite on its finite nonempty index set; no bounded-set assumption is encoded.
- Selector matching is stronger than just existence of some successful run; arbitrary minimizer tie-breaking cannot generally identify an externally supplied trajectory without a uniqueness argument. That argument is a proof obligation here, not an additional header premise.
- No uniform result for a best comparator, non-prescient scoring at x(t), or positive-part regret is stated. The cumulative quantity and bound may be negative.

## Uncertainty and blockers

- No semantic blocker in the provided headers. No proof bodies were supplied, so theorem provability and successful Lean elaboration/compilation are unverified.
- The imported definitions were treated as reading context only, not candidate redeclarations; equality between this neutral extract and any canonical source was not inspected.
- Source fidelity, intended paper theorem, and adequacy relative to an external contract were deliberately not assessed.
- Requested model metadata is recorded as requested; actual runtime identity is not independently attested.

## Exposure log

- raw SHA256 hash and UTF8 text read: `E:/ABRL/worktrees/research-online-book/tmp/online-ch2-prescient-euclidean-proposal-20261011/neutral-complete-headers-v1.txt`
- raw SHA256 hash and UTF8 text read: `E:/ABRL/worktrees/research-online-book/tmp/online-ch2-prescient-euclidean-proposal-20261011/neutral-imported-definitions-v1.txt`
- raw SHA256 hash and UTF8 text read: `E:/ABRL/worktrees/research-online-book/tmp/online-ch2-prescient-euclidean-proposal-20261011/neutral-standard-definitions-v1.txt`

No other file/source/paper/prospectus/review/body/AGENTS/memory was read. No compilation or source-fidelity evaluation was performed. Only fresh-blind-v1.json and fresh-blind-v1.md were created in the designated proposal directory.
