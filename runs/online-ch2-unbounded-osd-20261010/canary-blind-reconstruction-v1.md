# Two exact neutral canary types

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no independent runtime model or effort attestation. This reused automated decoder has related staged history. This is source-withheld reconstruction, not absolute blindness, a human/external review or fresh-history independence. Only this canary packet was read in the current task. No other inputs, live declarations, source identities, prior verdicts or proof bodies were consulted.

## Complete definitions and actual scoring

The four provided definitions mean
\[
\eta_\alpha(t)=(t+1)^{-\alpha},\quad
\phi(\alpha)=\frac1{2-\alpha}
+\frac{(1/2)^{1-\alpha}-1}{1-\alpha},
\]
\[
\sigma_T(t)=\begin{cases}-1&t<\lfloor(T+1)/2\rfloor\\1&\text{otherwise},\end{cases}
\qquad \ell_{T,v,t}(z)=\sigma_T(t)\langle v,z\rangle.
\]
Natural arithmetic occurs in the switching index, with ceil(T/2) negative rounds and floor(T/2) positive rounds inside the horizon. Real powers use the positive base t+1. In these canaries α is fixed at 1/2, so both coefficient denominators are nonzero.

The exact selector chooses a global supporting vector if the supporting set is nonempty, otherwise returns zero. step projects x−ηg onto its Domain. The actual recursion is X0=x0 and X_(t+1)=step(V,η_t,loss_t,X_t). Regret scores X_t, not X_(t+1):
\[
R_T(u)=\sum_{t<T}[(\mathrm{loss}_t(X_t)).\mathrm{toReal}
-(\mathrm{loss}_t(u)).\mathrm{toReal}].
\]
Current feedback loss_t is used after the state being scored, to determine the next state. The run is specified by the actual selector, not an arbitrary admissible subgradient policy.

The imported fullSpace denotes the whole ambient space (retained authorized shared API meaning from prior staged context; not reread here). The displayed real losses are embedded into EReal, hence finite. Their toReal values are the original real values. Scalar aliases use E=R,v=1, steps η_(1/2), initial state 0, fixed comparator 0. Vector aliases use E=EuclideanSpace R (Fin 2) and direction=PiLp.single 2 0 1, the first coordinate unit vector (1,0), with the same steps and zero initialization/comparator. Both regret aliases use their own horizon-dependent loss family.

## claim1: two-round scalar test

There are seven top-level conjuncts. The first step is 1; the second is positive and smaller. For the T=2 sign-switch run, the states at times 0,1,2 are respectively 0,1,1−2^(−1/2), and its two-round regret against zero is 1.
\[
\begin{aligned}
&\eta_{1/2}(0)=1
\land 0<\eta_{1/2}(1)
\land \eta_{1/2}(1)<\eta_{1/2}(0)\\
&\land X^{(2)}_0=0
\land X^{(2)}_1=1
\land X^{(2)}_2=1-2^{-1/2}
\land R^{\mathrm{scalar}}_2(0)=1.
\end{aligned}
\]

1. **Objects:** Actual scalar full-space learner with step exponent 1/2 and horizon-specific linear loss sequence; aliases scalarRun 2 t and scalarRegret 2.
2. **Quantifiers/order:** Closed seven-part conjunction. There is no free exponent, horizon, initial point, comparator or selected subgradient parameter.
3. **Assumptions:** No external premises. Step positivity, strict decrease and state/regret equalities are conclusions of the proposed type, not already proved facts supplied to it.
4. **Conclusion:** All seven assertions above. In particular regret is exactly 1, not a value evaluated at the terminal updated state.
5. **Constants/indices/boundaries:** T=2 has switching index (2+1)/2=1 in natural division: loss0(z)=−z and loss1(z)=z. The scored states are X0=0 and X1=1; X2 is the state after both updates and is not scored in range 2. The second step is 2^(−1/2), not 1/2 or a step indexed by 2. No zero-horizon test is asserted.
6. **Information:** Empty-history state X0 is zero; current loss0 yields the next state 1, and current loss1 yields the next state 1−2^(−1/2). The type therefore tests both update direction and pre-update scoring.
7. **Excluded scope:** No large-horizon lower-bound threshold is claimed satisfied at T=2. No asymptotic bound, all-horizon equality, arbitrary initial point, universal learner result or proof evidence follows from this closed canary type.

## claim2: nondegenerate plane and horizon 64

This type has nine top-level conjuncts; the played-time regularity clause contains two predicates, and the final existential contains two predicates. Let d=(1,0) and c=φ(1/2). The claims are: d has unit norm; the actual time-1 state of the T=64 run is d; all 64 played linear losses are globally convex and 1-Lipschitz; c≥1/15; the specified horizon threshold is at most 64; the explicit coefficient lower bound holds for vectorRegret 64; that regret is at least 256/15 and strictly greater than 17; and there exists a real-valued loss stream with played-time regularity and the same coefficient lower bound for the actual learner.

\[
\begin{aligned}
&\|d\|=1
\land X^{(64)}_1=d\\
&\land[\forall t<64,\ \operatorname{ConvexOn}_{\mathbb R}(E,\ell_{64,d,t})
\land\operatorname{LipschitzWith}(1,\ell_{64,d,t})]\\
&\land 1/15\le c\\
&\land \frac{2}{(1-1/2)c}\le64\\
&\land \tfrac12 c\,64^{\,2-1/2}\le R^{\mathrm{vector}}_{64}(0)\\
&\land 256/15\le R^{\mathrm{vector}}_{64}(0)
\land17<R^{\mathrm{vector}}_{64}(0)\\
&\land\exists L:\mathbb N\to E\to\mathbb R,\
[\forall t<64,\operatorname{ConvexOn}_{\mathbb R}(E,L_t)
\land\operatorname{LipschitzWith}(1,L_t)]\\
&\hspace{5em}\land
\tfrac12 c\,64^{\,2-1/2}
\le R_{64}(\mathrm{fullSpace},\eta_{1/2},\iota\circ L,0,0),
\qquad E=\mathbb R^2.
\end{aligned}
\]

1. **Objects:** Fixed two-dimensional Euclidean space, concrete nonzero direction d, actual full-space vector run with horizon-dependent sign losses, coefficient c and an existential alternative loss stream L. No generic dimension variable remains.
2. **Quantifiers/order:** Nine closed top-level conjuncts. The third quantifies natural t with t<64. The last existential chooses a whole stream L, then asserts regularity for played t and its actual cumulative-regret lower bound. This last clause does not syntactically identify its witness with the earlier switchLoss stream.
3. **Assumptions:** No external hypotheses. Unit norm, regularity, coefficient comparison, threshold and lower bounds are all proposed conclusions. Nontriviality is realized by the concrete plane and unit-vector clause, rather than a missing Nontrivial premise.
4. **Conclusion:** Exact first-state identity, not a full trajectory formula; ambient convexity/Lipschitz regularity; one threshold statement; three lower comparisons for the explicit run; and a genuine existential statement for some stream. The final existential lower bound uses the same actual canonical algorithm and zero initial point/comparator.
5. **Constants/indices/boundaries:** T=64 gives switching index 32, so rounds 0–31 have negative slope and 32–63 positive slope. η0=1; X1 is after processing round 0. The scalar exponent is 2−1/2=3/2, so the coefficient expression is 256c; the threshold is 4/c≤64. The type separately asserts c≥1/15, a nonzero positive lower value, and 256/15≤regret with strict 17<regret. No equality to those bounds is claimed. Only t<64 regularity is required of the existential stream; no condition at t=64 or later is stated.
6. **Information:** Constructed explicit losses depend on the fixed horizon 64 and d. Scoring uses the current state before current feedback updates it. There is no seed, expectation, randomized averaging or adaptive adversary premise. A Lipschitz function on the whole plane need not be bounded in value.
7. **Excluded scope:** Not a statement for all nontrivial dimensions, all horizons, all learners, all loss streams or all comparators. No threshold premise is imported into claim1 at horizon 2. The existential statement does not prove algorithmic computation of its witness, and declaration typing would not establish these lower bounds.

## Boundaries, completeness and evidentiary limits

All four producer definitions, the actual selector/step/iterate/regret bodies, five aliases and both full conjunctions are reconstructed. The conjunction counts are seven and nine (counting nested quantifier bodies separately as described). The two horizon-specific runs are different loss streams, not prefixes of a single common switched stream: their switching indices are 1 and 32. These types therefore cannot support a claim that the T=2 terminal run extends unchanged to the T=64 example.

No unresolved semantic issue was found using the supplied definitions and disclosed retained fullSpace meaning. No claim of truth, proof passage, compilation, source fidelity or lifecycle acceptance is made. Only the current packet is recorded as an actually read input; no canary-input index or live code was read.
