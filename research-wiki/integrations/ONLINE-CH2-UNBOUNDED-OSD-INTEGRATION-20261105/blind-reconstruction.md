# Blind mathematical reconstruction

**Status:** textual reconstruction only. These are the supplied assertions, not independently proved results or source-fidelity approvals.

Input SHA-256: `d2c9388d6e4248a2d76e3353d765c0eced4b454e368d111285744fae35ed7fe4`. It matches the expected hash.

## Scope and notation

The input contains four definitions and eleven typed target statements. All eleven target headers and their contexts are preserved verbatim in `semantic-slots.json`. The supporting API entries below cover every supplied definition, including the Domain alias.

Write C(alpha)=coefficient(alpha), m=(T+1) div 2=ceil(T/2), and n=T div 2=floor(T/2). Natural times begin at zero. All power expressions in the targets are real powers, with natural arguments cast to reals where indicated. Scalar multiplication is written eta*a.

All statements are deterministic. No probability space, random variable, expectation, confidence level, or observation protocol appears. The API namespace and the imports do not supply unstated probabilistic or feedback guarantees.

The key regret quantity uses the full space, starts at zero, and compares against the fixed zero point. It is not an optimization over comparators. The horizon-dependent sign construction has m initial negative rounds and n subsequent positive rounds within the horizon.

## Four definitions

### definition_schedule: Power schedule

- **Objects and spaces:** schedule : R -> N -> R.
- **Quantifiers:** For every real alpha and natural t.
- **Assumptions:** No restriction on alpha.
- **Conclusion or definition:** schedule(alpha,t) = (t+1)^(-alpha), with real exponentiation after casting t+1 from N to R.
- **Constants and indexing:** t is zero-based; schedule(alpha,0)=1. The power base is always strictly positive.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** Defined for every real alpha and every natural t. Decay is not asserted for arbitrary alpha.

### definition_coefficient: Coefficient

- **Objects and spaces:** coefficient : R -> R.
- **Quantifiers:** For every real alpha.
- **Assumptions:** No restriction in the definition.
- **Conclusion or definition:** C(alpha) = 1/(2-alpha) + ((1/2)^(1-alpha)-1)/(1-alpha).
- **Constants and indexing:** The constants 1, 2, and 1/2 and the exponent 1-alpha are real.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The Lean expression uses total real division. Positivity and the stated upper bound are asserted only for 0<alpha<1. The left limit at 1 is not a value assertion at 1; under Lean division-by-zero convention C(1)=1.

### definition_signPattern: Horizon-dependent sign sequence

- **Objects and spaces:** signPattern : N -> N -> R.
- **Quantifiers:** For every natural horizon T and every natural t.
- **Assumptions:** No horizon restriction.
- **Conclusion or definition:** With m=(T+1) div 2, signPattern(T,t)=-1 if t<m and +1 otherwise.
- **Constants and indexing:** div is natural-number division. m=ceil(T/2), and n=T div 2=floor(T/2). Over t=0,...,T-1 there are m negative signs and n positive signs.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The sequence is defined beyond the horizon. T=0 gives m=0 and signPattern(0,t)=+1 for every natural t. The switch index t=m has sign +1.

### definition_payoff: Signed linear payoff

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. payoff : N -> E -> N -> E -> R.
- **Quantifiers:** For every T, v, t, and z of the indicated types.
- **Assumptions:** No unit-norm or finite-dimensional assumption in the definition.
- **Conclusion or definition:** payoff(T,v,t,z)=signPattern(T,t) * <v,z>_R.
- **Constants and indexing:** The scalar sign multiplies the real inner product. T determines the switch and t selects the round.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** Globally real-valued on E. The name payoff does not assert a maximization objective; the regret API subtracts comparator loss from played loss.

## Eleven typed target statements

### claim1: Selected subgradient of an affine function

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. a,x in E; b in R; f(z)=<a,z>+b embedded into EReal.
- **Quantifiers:** For every a, x, and b.
- **Assumptions:** No finite-dimensional assumption in this target header.
- **Conclusion or definition:** currentSubgradient(f,x)=a.
- **Constants and indexing:** The constant offset b and evaluation point x do not affect the selected subgradient.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** An exact identity for this finite affine function. It is not a theorem that arbitrary functions have nonempty subdifferentials.

### claim2: Full-space affine update

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. eta,b in R and a,x in E.
- **Quantifiers:** For every eta, a, x, b.
- **Assumptions:** Finite dimensionality; no sign restriction on eta.
- **Conclusion or definition:** step(fullSpace,eta,z |-> EReal(<a,z>+b),x)=x-eta*a.
- **Constants and indexing:** eta*a denotes real scalar multiplication. fullSpace has carrier all of E.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** No bounded feasible set and no step-size positivity assumption. This specializes the supplied step API to affine finite losses.

### claim3: Closed-form affine iterates

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. eta:N->R, a:N->E, b:N->R, x0 in E, t in N.
- **Quantifiers:** For every sequence eta, a, b, every initial x0, and every natural t.
- **Assumptions:** Finite dimensionality; no regularity or sign restriction on the sequences.
- **Conclusion or definition:** iterate(fullSpace,eta,(s,z) |-> EReal(<a(s),z>+b(s)),x0,t)=x0-sum_{s=0}^{t-1} eta(s)*a(s).
- **Constants and indexing:** The time-t point includes exactly t updates. range t contains 0,...,t-1. The affine offsets b(s) do not enter the expression.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** At t=0 the sum is empty and the point is x0. No dependence on a(s) for s>=t.

### claim4: Strict positivity of the schedule

- **Objects and spaces:** alpha in R; t in N; real schedule.
- **Quantifiers:** For every real alpha and every natural t.
- **Assumptions:** No restriction on alpha or t.
- **Conclusion or definition:** 0<schedule(alpha,t).
- **Constants and indexing:** Uses the base t+1, never t; strict positivity includes t=0.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** This asserts positivity only, not monotonicity, summability, or an upper bound.

### claim5: Convexity and unit Lipschitz bound

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. T,t in N; v in E.
- **Quantifiers:** For every T, every v satisfying ||v||=1, and every natural t.
- **Assumptions:** Finite dimensionality and hv: ||v||=1.
- **Conclusion or definition:** payoff(T,v,t,.) is convex on all E and is Lipschitz with bound 1 on E.
- **Constants and indexing:** ConvexOn R univ and LipschitzWith 1 are conjoined. Lipschitz means |f(x)-f(y)|<=||x-y|| for all x,y in E.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** There is no t<T restriction here. The Lipschitz constant is at most 1, not a separate claim that 1 is the optimal constant. No boundedness of the loss values is asserted.

### claim6: Exact scalar finite-horizon regret

- **Objects and spaces:** The space is R; alpha in R; T in N. Loss at t is EReal(payoff(T,1,t,z)).
- **Quantifiers:** For every real alpha and natural T.
- **Assumptions:** No alpha interval or minimum-horizon hypothesis.
- **Conclusion or definition:** R_T = -(m-n)*sum_{i=0}^{m-1} schedule(alpha,i) + sum_{i=0}^{T-1}(i+1)^(1-alpha) - T*sum_{i=m}^{T-1} schedule(alpha,i), where R_T=regret(fullSpace,schedule(alpha),payoff(T,1) embedded into EReal,0,0,T).
- **Constants and indexing:** m=(T+1) div 2 and n=T div 2, both cast to R before subtraction; T and i+1 are likewise cast where needed. The last sum is over Finset.Ico m T. m-n is 0 for even T and 1 for odd T.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** Initial point 0 and fixed comparator 0 are separate regret arguments. All sums are empty at T=0. The equality includes the parity-dependent boundary term; it is not merely an asymptotic formula.

### claim7: Coefficient range

- **Objects and spaces:** alpha in R and C(alpha) in R.
- **Quantifiers:** For every alpha with 0<alpha<1.
- **Assumptions:** h_alpha0: 0<alpha; h_alpha1: alpha<1.
- **Conclusion or definition:** 0<C(alpha) and C(alpha)<1-log(2).
- **Constants and indexing:** log is the real natural logarithm. Both inequalities are strict.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** No endpoint alpha=0 or alpha=1 is included. No monotonicity assertion is present.

### claim8: Left endpoint limit and numerical bound

- **Objects and spaces:** coefficient:R->R; real neighborhood filters.
- **Quantifiers:** A parameter-free assertion about coefficient and log(2).
- **Assumptions:** No extra hypotheses.
- **Conclusion or definition:** lim_{alpha->1 from below} C(alpha)=1-log(2), and 3/10<=1-log(2).
- **Constants and indexing:** The input filter is nhdsWithin 1 {alpha | alpha<1}; the output filter is the ordinary real neighborhood of 1-log(2). The fraction 3/10 is exactly real 0.3.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The limit is one-sided from below. It does not assert a two-sided limit, continuity at 1, C(1)=1-log(2), or a strict lower inequality for the numerical constant.

### claim9: Scalar regret lower bound

- **Objects and spaces:** The space is R; alpha in R; T in N; C=coefficient(alpha).
- **Quantifiers:** For every alpha and T satisfying the stated conditions.
- **Assumptions:** 0<alpha<1 and 2/((1-alpha)*C)<=real(T).
- **Conclusion or definition:** (1/2)*C*real(T)^(2-alpha) <= regret(fullSpace,schedule(alpha),(t,z) |-> EReal(payoff(T,1,t,z)),0,0,T).
- **Constants and indexing:** The exact threshold is 2/((1-alpha)*C), with weak <=. The exact leading lower-bound constant is C/2. Exponent 2-alpha lies between 1 and 2 under the assumptions.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** Initial point and comparator both equal 0. Loss construction may depend on T. No bound is asserted here below the stated threshold, for endpoints of the alpha interval, or for other algorithms.

### claim10: Unit-direction regret lower bound

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. alpha in R; T in N; v in E.
- **Quantifiers:** For every eligible alpha and T, and every v with ||v||=1.
- **Assumptions:** 0<alpha<1; 2/((1-alpha)*coefficient(alpha))<=real(T); ||v||=1.
- **Conclusion or definition:** (1/2)*coefficient(alpha)*real(T)^(2-alpha) <= regret(fullSpace,schedule(alpha),(t,z) |-> EReal(payoff(T,v,t,z)),0,0,T).
- **Constants and indexing:** Same threshold, coefficient, exponent and horizon indexing as claim9; zeros now denote the zero vector in E.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** This is universal over supplied unit vectors. There is no explicit Nontrivial E assumption, since a unit vector is given. No dependence on the dimension appears in the lower-bound constant.

### claim11: Existence of regular losses with large regret

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. Additionally Nontrivial E; alpha in R; T in N; loss:N->E->R.
- **Quantifiers:** For every eligible E, alpha and T, there exists a loss sequence such that both the regularity and regret properties hold.
- **Assumptions:** Nontrivial E; 0<alpha<1; 2/((1-alpha)*coefficient(alpha))<=real(T).
- **Conclusion or definition:** There exists loss such that (for every natural t<T, loss(t,.) is convex on E and LipschitzWith 1) and (1/2)*coefficient(alpha)*real(T)^(2-alpha) <= regret(fullSpace,schedule(alpha),(t,z) |-> EReal(loss(t,z)),0,0,T).
- **Constants and indexing:** The same one witness loss sequence must satisfy both conjuncts. It is defined for all natural t; regularity is required only for t<T. The algorithm uses losses at t=0,...,T-1.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The existential witness may depend on alpha, T, and E. This does not assert a single loss sequence working for all horizons, a lower bound for every convex Lipschitz sequence, or a lower bound for arbitrary algorithms. The target does not specify its witness.

## Supporting API meanings

### api_SourceSubdifferential: Global subdifferential

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. f:E->EReal, x in E; a subset of E.
- **Quantifiers:** For every f,x, membership of every candidate g is tested against every y in E.
- **Assumptions:** No convexity, finiteness or nonemptiness assumption in the definition.
- **Conclusion or definition:** g belongs iff f(x)+EReal(<g,y-x>)<=f(y) for every y in E.
- **Constants and indexing:** The inequality has coefficient 1 on the inner product and uses y-x. Comparison and addition are in EReal.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The definition permits extended-real functions. Their arithmetic conventions are not further specified in the packet. This is a global supporting inequality, not an explicitly restricted-domain subdifferential.

### api_Domain: Domain structure and alias

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. Domain E is a structure.
- **Quantifiers:** Each Domain packages one carrier set and certificates.
- **Assumptions:** Carrier is nonempty, closed, and convex over R.
- **Conclusion or definition:** Domain E has carrier:Set E, nonempty:carrier.Nonempty, closed:IsClosed carrier, convex:Convex R carrier. OnlineSubgradientDescent.Domain abbreviates this same structure.
- **Constants and indexing:** No radius, diameter, dimension, or boundedness field exists.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** Completeness is not a structure field. Defining this structure itself does not need finite dimensionality.

### api_project: Choice-defined projection operation

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. Additionally CompleteSpace E; V:Domain E and z in E.
- **Quantifiers:** For each V,z.
- **Assumptions:** V supplies nonempty, closed, convex; the surrounding space is complete.
- **Conclusion or definition:** project(V,z) is Classical.choose applied to exists_norm_eq_iInf_of_complete_convex(V.nonempty,V.closed.isComplete,V.convex,z).
- **Constants and indexing:** It chooses an existence witness using classical choice; no computable search routine is supplied.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The exact type and conclusion of the named existence theorem are missing. Its name suggests a nearest-point witness, but the packet alone does not expose its membership, minimization, or uniqueness statement. Those properties are not independently certified here.

### api_fullSpace: Full feasible space

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. The supplied context additionally has CompleteSpace E.
- **Quantifiers:** For each eligible E.
- **Assumptions:** No boundedness restriction.
- **Conclusion or definition:** fullSpace is a Domain with carrier univ, certified nonempty, closed, and convex.
- **Constants and indexing:** The carrier is all of E.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The explicit definition constructs the carrier and its three certificates. The header of an elaborated declaration is not supplied, so unused section variables should not automatically be treated as retained arguments.

### api_currentSubgradient: Selected subgradient with fallback

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. f:E->EReal and x in E. Its supplied enclosing block also declares FiniteDimensional R E.
- **Quantifiers:** For every f,x.
- **Assumptions:** No hypothesis ensures a nonempty subdifferential.
- **Conclusion or definition:** If SourceSubdifferential(f,x) is nonempty, choose one of its elements by Classical.choose; otherwise return the zero vector.
- **Constants and indexing:** The fallback value is exactly 0. No unique selector or numerical procedure is specified.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** A fallback zero need not be a subgradient when the set is empty. The finite-dimensional section variable is unused in this body and claim1 explicitly invokes the operation without it; textual section context must not be strengthened into an extra hypothesis of claim1.

### api_step: One update

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. V:Domain E, eta in R, f:E->EReal, x in E.
- **Quantifiers:** For every V,eta,f,x.
- **Assumptions:** Domain certificates and supplied finite-dimensional context; no eta>0 assumption in the definition.
- **Conclusion or definition:** step(V,eta,f,x)=project(V,x-eta*currentSubgradient(f,x)).
- **Constants and indexing:** Subtract before projection; scalar multiplication is by eta.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** The operation references the whole current function through currentSubgradient. No observational oracle, query budget or implementability claim is included.

### api_iterate: Zero-based recursion

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. V:Domain E, eta:N->R, loss:N->E->EReal, initial point x_init in E.
- **Quantifiers:** For every natural t.
- **Assumptions:** No regularity assumptions on loss or eta in the definition.
- **Conclusion or definition:** x(0)=x_init; x(t+1)=step(V,eta(t),loss(t),x(t)).
- **Constants and indexing:** The code names the initial argument x1, but its time index is 0. Loss t is evaluated at x(t) in regret and is used to produce x(t+1).
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** No claim of randomization, adaptive observations or an online information restriction follows merely from this recursion.

### api_regret: Fixed-comparator regret

- **Objects and spaces:** E is a real inner-product space with NormedAddCommGroup E and InnerProductSpace R E. FiniteDimensional R E is additionally assumed. V,eta,loss as above; initial point x_init and comparator u in E; horizon T in N; result in R.
- **Quantifiers:** For every initial point, comparator and natural T.
- **Assumptions:** No minimization or comparator-membership hypothesis appears in the definition.
- **Conclusion or definition:** regret = sum_{t=0}^{T-1} [toReal(loss(t,x(t)))-toReal(loss(t,u))], with x defined by iterate.
- **Constants and indexing:** Initial point and comparator are distinct arguments. The sum contains T terms; T=0 gives 0. The subtraction is between two separately converted real values.
- **Probability and feedback:** Deterministic statement. No probability space, expectation, high-probability event, sampling law, or feedback protocol is supplied.
- **Boundaries:** This is regret against one supplied comparator, not an infimum over E. No expectation is taken. EReal.toReal behavior at infinities is not supplied, but all target losses are finite real values embedded into EReal, so no infinite-value convention is needed for these targets.

## Missing context and limits

1. The precise statement of exists_norm_eq_iInf_of_complete_convex is absent. The projection expression can be reconstructed syntactically, but its full witness contract cannot be independently recovered from a theorem name.
2. The bodies and proof terms of all target theorems are absent. This review reconstructs assertions and supplies no proof-checking or mathematical-validity certificate.
3. Elaborated declaration signatures for supporting APIs are absent. Some declared section instances can be unused; the explicit target contexts govern reconstructed target assumptions.
4. General EReal arithmetic and toReal definitions are not included. The target affine and signed-linear losses have finite real values, so this gap does not prevent reading their target regret statements.
5. No source identity, original prose, correspondence map to external theorems, or source-specific interpretation is supplied. Source fidelity cannot be evaluated.
6. No probability model or feedback protocol is supplied. The deterministic definitions do not establish a bandit-feedback, stochastic, expected-regret, or high-probability claim.

## Actor and access disclosure

The visible context contained generic Codex tool and workflow instructions, the ABRL workspace AGENTS.md instructions, a generic memory-summary block naming prior ABRL work, environment paths, and the parent task assignment. No parent mathematical discussion, original source identity, target proof, or historical verdict was supplied in this task. I did not open or search memory files, README, repository sources, imports, other maintenance files, or the internet. The only pre-existing file read was the authorized packet.json. Names already present inside that packet were retained as identifiers only.

This is an independent reconstruction using the supplied packet; contextual source blindness is limited by the generic ABRL instructions and memory-summary text already visible in the agent environment. It is not a claim that the environment contained no project metadata.

No compilation, proof inspection, source search, source edit, or repository edit was performed. Only these create-only review artifacts were written.
