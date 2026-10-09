# Full production BODY and canary CONTRACT review

Overall verdict: accepted-with-explicit-delta. Production BODY verdict: accepted-with-explicit-delta for all eleven frozen terminals. Canary CONTRACT verdict: accepted-with-explicit-delta for the two exact v2 types and five aliases. No blocking repair found. This is neither completed canary BODY review nor source-package/chapter acceptance.

The reviewer /root/source_reviewer is the reused staged automated source role, distinct from formalizer and decoder. Requested GPT-6 Astra / medium is not runtime-attested; no external/human/absolute-blind independence is claimed. Prior seven-leaf/source analysis is reused only where exact unchanged bytes were checked; the four new actual bodies were read in full. Original source PDF64/65 and Chapter2 PDF26 views are reused at their unchanged fingerprints, not described as fresh views.

All106 main-index rows and13 supplemental rows were independently RAW checked before/after, as were all33852 baseline rows with common.fixed. Supplemental membership may overlap main membership; these are indexed counts, not119 distinct mathematical artifacts. All77 historical seven-leaf immutable rows match. PUBLIC equals full-body-source-v1 and preserves the complete reviewed seven-leaf RAW prefix. All eleven exact header strings and scoped contexts remain the original contract. The earlier CONTRACT68 live OWN metadata are not falsely asserted unchanged: their historical resolution remains as recorded by the seven-leaf review.

## Actual production findings

### currentSubgradient_affine

Produces nonempty singleton via affine_subdifferential, unfolds actual dependent conditional, then uses Classical.choose_spec and singleton membership. No externally supplied support or conclusion.

- objects: Actual affine EReal selector in a real inner-product space
- quantifiers: All a,x,b; no finite dimension
- assumptions: Only stated normed/inner structures; global finite affine loss
- conclusion: Selected vector equals a, not merely membership
- constants_indices_boundaries: Zero a/intercept and zero-dimensional helper allowed
- information_structure: Current function and point only
- source_scope_delta: Shared singleton subdifferential makes first leaf dependency-ready

### step_affine_fullSpace

Unfolds actual step, uses the new selector equality and existing project_fullSpace. Finite dimension supplies completeness; arbitrary signed eta remains valid.

- objects: Actual full-space projection step
- quantifiers: All real eta,a,x,b in finite-dimensional E
- assumptions: No positivity needed for this algebraic identity
- conclusion: Actual step equals x-eta smul a
- constants_indices_boundaries: Zero/negative eta included
- information_structure: Current loss updates next state
- source_scope_delta: Finite dimension supplies completeness for existing projection API

### iterate_affine_prefix

Induction on actual recursive iterate; zero is the empty sum, successor uses new step equality and sum_range_succ with additive rearrangement. Same run, strict prefix, arbitrary intercepts cancel in update.

- objects: Actual affine recursion
- quantifiers: All schedules, coefficient/intercept streams,x0,t
- assumptions: No boundedness/sign/monotonicity assumption
- conclusion: x0 minus weighted strict-prefix coefficient sum
- constants_indices_boundaries: range t; t=0 empty
- information_structure: Current coefficient excluded from current output
- source_scope_delta: No supplied trajectory; induction must produce identity

### powerSteps_pos

Positive natural successor cast and Real.rpow_pos_of_pos prove positivity for every real exponent, including outside the source interval. No zero base.

- objects: Real power schedule
- quantifiers: All real alpha and natural t
- assumptions: Positive base t+1
- conclusion: Strictly positive schedule
- constants_indices_boundaries: eta0=1; no zero base
- information_structure: Deterministic index-only
- source_scope_delta: Stronger alpha scope than source is harmless auxiliary algebra

### switching_loss_regular

Affine convex combination identity proves ambient convexity. Absolute switching slope equals one; Cauchy-Schwarz and unit v prove global LipschitzWith 1. Finite-dimensional premise retained, though unnecessary for this helper.

- objects: Ambient switching affine loss
- quantifiers: All T,t and unit v in finite-dimensional E
- assumptions: Unit norm one
- conclusion: ConvexOn univ and LipschitzWith 1
- constants_indices_boundaries: Switch at ceil(T/2); even T0 helper meaningful
- information_structure: Fixed horizon-dependent stream, no learner future input
- source_scope_delta: Finite dimension is unnecessarily narrow for regularity alone but covers source endpoint

### switching_scalar_regret_identity

Produces the actual scalar iterate by the affine-prefix theorem. Proves prefix counts of signs by induction and obtains the strict suffix Ico(i+1,T). Reverses the finite double sum, splits at m=ceil(T/2), retains the real ceil-minus-floor term and uses positive-base rpow addition. Works for all real alpha and T=0; no supplied run or regret premise.

- objects: Actual scalar OSD regret
- quantifiers: All real alpha and natural T
- assumptions: No desired-regret or trajectory premise
- conclusion: Exact signed three-sum identity
- constants_indices_boundaries: Separate casts of ceil/floor; Ico ceil T; T0/1 give zero
- information_structure: Scores pre-update iterate t
- source_scope_delta: Derived identity; source odd/even term preserved

### phi_range

Sets beta=1-alpha in (0,1), q(beta)=(1+beta)2^(-beta). Actual two derivatives prove concavity on [0,1]. Strict Bernoulli gives 2^beta<1+beta and q(beta)>1. Exact phi=(q-1)/(beta(1+beta)); positive denominator gives lower strict bound. Concave chord slope at zero is at most 1-log2; the extra factor 1+beta>1 and 1-log2>0 give the strict upper bound. Neither positivity nor the desired range is a premise.

- objects: Exact phi scalar expression
- quantifiers: All alpha strictly between zero and one
- assumptions: Both strict interval assumptions
- conclusion: 0<phi<1-log2
- constants_indices_boundaries: Endpoints excluded; denominators positive
- information_structure: No algorithm premise
- source_scope_delta: Printed supplementary assertion remains required proof

### phi_limit

Computes derivative of (1/2)^(1-z) at z=1 and applies punctured slope convergence restricted to the left filter; negative slope yields log(1/2). Continuous first summand tends to1. log inverse gives 1-log2; explicit log_two_lt_d9 implies3/10. Does not assert continuity of totalized phi at1.

- objects: Total real phi and left-neighborhood filter
- quantifiers: Closed conjunction
- assumptions: No premise
- conclusion: Left limit 1-log2 and 3/10 lower comparison
- constants_indices_boundaries: phi(1)=1 by total division is not claimed equal to limit
- information_structure: Parameter limit, not regret-horizon convergence
- source_scope_delta: Printed assertion; no claim phi(alpha)>=0.3 throughout interval

### switching_scalar_lower_bound

Derives beta=1-alpha in(0,1), phi>0 and T>=2 from the exact threshold. Bounds first decreasing-power block from1 to m with the separate initial1, increasing-power sum by integral0..T, and decreasing suffix by integralm..T. Each exponent-integrability and positive interval premise is explicitly discharged. Bounds m between T/2 and T, retains the odd correction at most1, drops only the nonnegative -1+1/beta, rewrites to -T^beta/beta+phi*T^(beta+1), then absorbs the first term using the exact threshold. No conclusion is assumed.

- objects: Same scalar switching run
- quantifiers: All alpha in (0,1), all natural T meeting exact real threshold
- assumptions: No supplied lower bound or phi positivity premise
- conclusion: Half phi times T^(2-alpha) lower bounds actual regret
- constants_indices_boundaries: Threshold excludes T0; factor and exponent unchanged
- information_structure: Same canonical pre-update OSD/initial0/comparator0
- source_scope_delta: Explicit source witness, not all learners or all horizons for one stream

### switching_vector_lower_bound

Rewrites the actual vector loss as an affine coefficient switchSlope smul v and proves the same canonical iterate equals the scalar prefix coefficient smul v. Separately derives scalar run from the same producer, then termwise norm-one inner-product equality proves equality of actual regrets. The scalar lower bound is applied only after this same-run equality.

- objects: Same run along unit vector
- quantifiers: All finite-dimensional E,alpha,T,v with norm1
- assumptions: Exact scalar threshold plus unit norm
- conclusion: Same coefficient lower bound for actual vector regret
- constants_indices_boundaries: No unit in dimension0
- information_structure: Actual selector and recursion must lift, not a surrogate trajectory
- source_scope_delta: General real finite-dimensional inner spaces represent source Euclidean dimensions

### theorem_5_4

Uses Nontrivial finite-dimensional real E to produce norm-one v via exists_norm_eq, chooses the full switchLoss T v stream, and supplies played-time convexity/Lipschitz and actual vector lower bound. Unit vector, trajectory, regularity and desired regret are not caller premises. Zero-dimensional false positive is excluded.

- objects: Existential real loss stream on nontrivial finite-dimensional E
- quantifiers: For every eligible alpha,T exists one stream
- assumptions: Nontrivial E, exponent interval and threshold only
- conclusion: Played losses convex/1-Lipschitz and actual zero-comparator lower bound
- constants_indices_boundaries: Losses globally finite; regularity required t<T; dimension0 excluded
- information_structure: Witness may depend on horizon; algorithm remains strict past
- source_scope_delta: One source theorem plus coefficient facts, not eleven source results

## Evidence and failure boundaries

The four new successful focused receipts each show actual exit0 and completed3360 cached-inclusive jobs. The complete public audit has actual Lean exit0 and eleven exact named types/standard axiom lists. I parsed the full bracketed lists across line breaks directly from retained stdout; every set is propext, Classical.choice, Quot.sound. The two wrapper parser failures are separate from successful Lean, retained and corrected without pretending to rerun it. Header fence comparisons match the frozen native hashes; these hash comparisons do not independently certify source meaning.

The scalar identity's initial local sum/let rewrite failures and the scalar lower bound's initial interval/inequality arithmetic failures are preserved. Final bodies repair proof steps without weakening any header. Vector lift and final existence succeed in their retained first attempts. The eleven #checks and the partially applied theorem_5_4 at dimension2/alpha1/2/T64 are public type evidence, not a proved T64 threshold or completed canary. No selected numeric canary proof branches exist yet.

Source alignment is substantive: the three integrals use exactly the safe ranges [1,m], [0,T], [m,T], and beta>0 handles the origin integral. T>=2 is derived rather than silently imposed. Actual pre-update losses, coefficient, odd/even split, initial0 and fixed comparator0 are preserved. Full-space projection is eliminated through the actual selector/step proof, not a supplied idealized trajectory. Nontriviality correctly represents positive Euclidean dimension. This is failure of this OSD schedule, not every algorithm; source section5.3 is a different result. Eleven supporting endpoints are not eleven source theorem credits.

## Exact canary CONTRACT

### scalar_actual_two_rounds

- objects: Actual scalar full-space canonical OSD, alpha=1/2, horizon-specific switchLoss2
- quantifiers: Closed seven-conjunct proposition; no premises
- assumptions: Positivity, strict step decrease and trajectory facts must all be proved
- conclusion: eta0=1, eta1 positive and smaller; states0,1,1-2^(-1/2); regret2=1
- constants_indices_boundaries: Switch at1; scored points0 and1; terminal state2 not scored; not a source-threshold instance
- information_structure: Pre-update scoring, current feedback determines next state
- source_scope_delta: Validation instance only; different stream from horizon64

### finiteDim_source_lower_bound

- objects: Actual EuclideanSpace R(Fin2), direction PiLp.single 2 0 1, canonical switchLoss64
- quantifiers: Closed nine-conjunct proposition; played regularity forall t<64 and final existential whole loss stream
- assumptions: No imported threshold, norm, regularity or desired lower bound
- conclusion: Unit direction/first state, all played losses regular, phi>=1/15, threshold<=64, actual coefficient bound, numeric>=256/15 and>17, full existential endpoint
- constants_indices_boundaries: Switch at32; phi(1/2)=sqrt2-4/3>=1/15 gives threshold<=60<64 and 64^(3/2)=512
- information_structure: Same actual algorithm and comparator0; final existential need not syntactically identify its witness with preceding explicit stream
- source_scope_delta: True nondegenerate finite source instance once proved; not arbitrary dimension/all-horizon/all-learner acceptance

The completed distinct neutral reconstruction agrees with all7/9 conjuncts and all five aliases. The v1 PiLp.single omitted the explicit p=2 argument; v2 fixes that draft context and elaborates both Props at actual exit0, without proving either. T2 and T64 have switch points1 and32, hence are different horizon-dependent streams. They must never be presented as the same loss-stream prefix. For alpha1/2, phi=sqrt2-4/3 and sqrt2>7/5 support the planned 1/15 coefficient comparison; 256/15>17 is strict. These arithmetic checks support freeze-readiness, not compiled proofs.

## Permission and required next gates

After exact v2 header/context freeze, permit only NEW Tests/OnlineUnboundedOSDCanary.lean containing the five exact aliases/import setup and the two named bodies, with explicit local arithmetic/trajectory helpers as necessary. Preserve all production declarations/definitions and existing files. Actual scalar state/regret assertions must use the new producer chain; vector explicit lower bounds must retain switching_vector_lower_bound, and the final existential must use theorem_5_4. The numeric bound branches themselves must retain the applicable new endpoint VALUE, not merely an unused invocation elsewhere in the conjunction followed by independent norm_num. Later BODY review must inspect the selected branches and full conjunctions.

No root/Test-root, reader, registry, site or global metadata mutation is approved here. Full canary BODY, actual dependency/axiom/fence evidence, combined roots/Tests/harness, exact publication plan, registry/site/DOM/personal pixels/FINAL/native/post-native/delivery remain required. All eight Chapter2 forward containers remain required/open pending dedicated reconciliation; Chapter2 partial/null and whole Goal ACTIVE. No merge/deploy/main/live or full Chapter5 acceptance.
