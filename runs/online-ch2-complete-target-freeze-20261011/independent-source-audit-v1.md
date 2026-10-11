# Chapter2 independent source-audit recommendations

Verdict: **repair before target freeze**. All73 original rows,32 numbered navigation entries,two algorithms,five main-text exercise-deferred claims,10 forward containers and28 dependency rows remain. Eight historical containers stay open and six future claims stay pending. Denominator null; no chapter acceptance.

Independence: distinct from the formalizer proposal, but this actor authored the H0 drafts. This is a source-exposed automated re-audit, not a human or absolute external review.

## Twenty-one decisions

### R01 — repair

unnumbered:game-regret; PDF[20, 21].

Retain child, but write eventual-upper-bound/epsilon form or extended-real limsup, since normalized regret can diverge to minus infinity. Ordinary real-valued limit-to-zero is stronger than one-sided no-regret. No equality of losses follows.

### R02 — accept

Proposition 2.11; PDF[24, 25].

Retain existence, uniqueness, feasibility, norm/squared norm equivalence and variational inequality as definition/proof dependencies. Do not count each as a new independent numbered theorem.

### R03 — accept

unnumbered:relative-interior-footnote; PDF[29].

Retain relative-interior mathematical side branch. It is source-stated despite not needed later. Required ambient extension must be specified, with finite-dimensional proper convex assumptions.

### R04 — accept

unnumbered:closed-iff-lsc; PDF[28].

Retain Hausdorff branch. General topological lower semicontinuity versus closed real sublevels actually holds more broadly; source Hausdorff statement is sufficient and must not be weakened to Euclidean-only.

### R05 — accept

unnumbered:weighted-distance-identity; PDF[26].

Pixels PDF26 confirm factor1/2. Exact algebraic identity has no diameter/monotonicity requirement. Keep exact equality, followed by distinct monotone bound.

### R06 — accept

unnumbered:step-size-algebraic-minimization; PDF[27].

Positive a,S unique minimizer; both zero all positive steps minimize; exactly one zero infimum0 unattained. Distinguish fixed-coefficient optimization from eta-dependent actual trajectory.

### R07 — repair

unnumbered:diameter-gradient-coarse-tuning; PDF[27].

Keep positive D,L,T source formula. For degeneracy do not evaluate D/(L sqrt T) or set illegal eta0: state separate valid arbitrary-positive-step bound when D=0 or realized gradients vanish, and empty regret at T=0. Mark these well-formedness extensions, not additional printed branches.

### R08 — repair

Example 2.15; PDF[27, 28].

Retain delta>=0 qualification and explicit horizon-dependent family. State one-sided average-excess upper convergence, not equality of average performance. Quantify bounded z_t along each horizon family; no unsupported single unbounded varying-step run.

### R09 — repair

Theorem 2.22; PDF[29].

Retain literal finite-at-x and convex assumptions. Freeze exact ambient extended-real differentiability definition, including finite neighborhood requirement, and source-equivalence proof obligation. No predicate-name-based acceptance.

### R10 — accept

Theorem 2.23; PDF[29, 30].

Retain both inclusion/equality and m>=1 interpretation. Proper constituents can have disjoint domains, making F improper; inclusion must handle empty supports without silently assuming F proper. Ordinary interiors remain source equality condition.

### R11 — accept

Theorem 2.26; PDF[30].

Retain I finite nonempty and continuity at common-domain point, whole active subgradient union and convex hull. Nonempty qualification is explicit source well-formedness clarification.

### R12 — accept

Theorem 2.28; PDF[30].

Retain proper outer f only, arbitrary affine map, no extra convexity. Empty affine image-domain branch needs clear support convention and vacuity, not hidden proper composition premise.

### R13 — accept

Theorem 2.30; PDF[31].

Use declared L>=0 convention, every subgradient on ordinary interior, Euclidean norm and empty-interior vacuity. Negative L/dimension-zero quirks must not be silently read into conventional Lipschitz constant.

### R14 — repair

unnumbered:unit-exponents; PDF[32, 33].

Retain all four branches but label dimensional transcendental/probability/density parts typed modeling conventions, not untyped real-analysis theorems. Density units require a reference measure/coordinate and change-of-variable rule; inverse variable means inverse volume in multiple dimensions. Freeze concrete representation before proof denominator.

### R15 — accept

unnumbered:coordinate-rescaling; PDF[33, 34].

Retain unprojected change of coordinates with xprime=x/1000,gprime=1000g, wrong update factor10^6, corrected eta/10^6 and actual trajectory. Projected extension is a separate optional generalization.

### R16 — repair

unnumbered:minimizer-free-regret; PDF[35].

Retain literal min requires attainment and comparator definition avoids it; explicitly distinguish optional infimum/supremum representation extension from printed source. Infinite diameter vacuity is about the diameter bound, not every varying-step trajectory failing.

### R17 — accept

forward:offline-no-minimizer; PDF[35, 37, 38].

Accept diagnosis and recommend explicit pointer correction3.2->3.5; this report does not approve rewriting source/canonical contracts. Retain literal pointer and counterevidence. Expected infimum convergence is a derived epsilon-comparator branch; strict separability, finite nonempty sample, positive denominators and regularized attainment retained.

### R18 — repair

forward:square-OGD-improvement; PDF[27].

Retain sharp Example4.11 and actual schedule eta1/(2t), plus separately mandatory generic Theorem4.7. Cor4.8 open-neighborhood L-Lipschitz with L2 is not satisfied by endpoint square losses; use on-domain gradient bound2 in4.7. A sqrt T upper bound alone is no lower bound.

### R19 — accept

unnumbered:actual-OSD-performance-transfer; PDF[31, 32].

Retain all legal selected subgradients, causal output, feasibility, both sharp residual bounds and tuning. Policy law must be premise about lawful feedback with existence producer, never assumed desired regret.

### R20 — accept

unnumbered:extended-domain-indicator; PDF[21, 22].

Retain full epigraph scope including minus infinity separately from no-minus-infinity characterization. Indicator finite-loss claim needs finite losses/proper arithmetic, not arbitrary addition of opposite infinities.

### R21 — accept

Example 2.6; PDF[22, 23].

Retain arbitrary norm, not merely Euclidean; four closure bullets mandatory despite proof-left-as-exercise. Freeze 0*infinity/opposite infinities and empty supremum conventions. Do not narrow them silently to real-valued functions except the explicitly real-valued monotone-composition bullet.

## Additional forward-chain repairs

### F01-entropy-gradient-monotonicity

parameter-free -> KT13.4 -> entropy6.33; PDF[47, 92, 223].

Add explicit Theorem4.3 first branch: proper convex f is lambda-strongly convex on dom partial f iff <g_x-g_y,x-y> >=lambda||x-y||^2 for every x,y in dom partial f and their subgradients. Lemma6.33 proof explicitly invokes4.3; current28 dependency rows omit that edge. Need appropriate restricted-domain entropy specialization and Eq6.4/Bernoulli endpoint continuation.

Source dependency missing from enumerated graph; no claim entire4.3 second Hessian branch required by this route.

### F02-pnorm-route

parameter-free retained Lp branch; PDF[94, 95, 96, 228].

If retained Lp bound remains in Chapter2 target scope, add Lemma6.35: psi=||x||_p^2/2 is(p-1)-strongly convex for1<=p<=2, plus actual constrained p-ball OMD and variable-step bound at eta=sqrt(p-1)/(Lq sqrt(2t)). Section6.7 displayed fixed-step whole-space bound alone is insufficient.

Retain branch pending ownership decision; do not silently delete it or mark28 rows exhaustive.

### F03-adaptive-summation

adaptive -> Lemma4.13; PDF[51, 52].

Lemma4.13 is named in target dependencies but absent as its own28-row dependency contract. Bind a0..aT>=0, continuous nonnegative nonincreasing f on[0,infinity), sum a_t f(a0+sum_{i<=t}a_i)<=integral_a0^(sum a_i)f; inverse-sqrt singular-at0 specialization requires offset/limit and zero-energy handling.

Existing adaptive package may supply it, but this audit does not reaccept that package.

### F04-omd-direction-constant

parameter-free Eq13.2; PDF[228].

Keep exact sqrt(2T) direction contribution and printed schedule. Diameter2 substitution into generic C2 bound does not supply this constant. Require a source-qualified sharp directional producer or explicit source correction review.

No counterexample or correction proven in this audit.

### F05-ftrl-finiteness

FTRL-unbounded; PDF[112, 113, 114].

Lemma7.1 printed extended-real losses make cancellation and infinity-minus-infinity nontrivial; freeze finite-loss specialization or lawful extended equality. Cor7.6 needs explicit positive eta,mu and minimizer/existence/closedness route. Preserve sharp correction term without imposing monotonicity where not mathematically needed.

Do not infer general algorithm existence from argmin notation.

### F06-lookahead-alternate

lookahead alternative BTRL; PDF[277, 278, 279].

Theorem15.30 primary route retained, including fixed-step proof left as exercise. If15.31 alternate route retained as mandatory, resolve x_(T+1) terminal regularizer/loss and bind7.47 exact target; draft merely names7.47. Negative stability does not mean total regret nonpositive.

No independent review of7.47 in this pass, so no certification of alternate chain.

## Pointer adjudication

PDF35 literally references Example3.2; PDF37 assumes nonempty argmin; PDF38 Example3.5 explicitly has separable logistic nonattainment. Recommend labelled correction to3.5 while preserving literal3.2. This report does not authorize silent source/canonical rewriting. Expected infimum convergence requires the epsilon-comparator bridge.

## Freeze boundary

The10/28 packet is retained, not certified exhaustive: Theorem4.3 is an omitted entropy-chain edge; retained Lp and alternate BTRL routes need further explicit dependency contracts. Source page hashes and fresh-read flags are in JSON. Unread later anchors are not certified. No Lean proof, compiler, canonical contract, OSD RUN, or acceptance state changed.

- Incorporate21 row decisions and six forward-chain repair records without deleting original mathematical scope.
- Freeze concrete dimensional-model conventions and extended-real/algorithm well-formedness qualifications, marked separately from literal source.
- Read and adjudicate all still-unreviewed later dependency statements/branches, including alternate7.47 if retained; close graph ownership without equating metadata rows to proof counts.
- Distinct final target-freeze approval must precede next proof; subsequent exact producer/BODY/FINAL evidence is a separate gate.
