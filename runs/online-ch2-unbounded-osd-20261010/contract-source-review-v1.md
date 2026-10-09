# Unbounded OSD source/type contract review

Verdict: accepted-with-explicit-delta. First leaf: accepted for stabilization and subsequent proof lowering only. Canary design: accepted-in-principle, with exact Test headers, independent contract review and bodies still pending. No blocking repair found.

Actor /root/source_reviewer is a reused staged automated source reviewer, distinct from formalizer and neutral decoder. Requested GPT-6 Astra / medium is not runtime-attested. Related history is disclosed; this is not human/external review or absolute blindness.

I personally inspected the original PDF64/65 images (printed52/53) and Chapter2 PDF26 image at original detail, read the source text, all eleven complete proposed headers/four definitions, the neutral reconstruction, shared selector/step/iterate/regret and affine-singleton/project APIs, conversion window and actual type/retrieval receipts. All 68 indexed raw files and all 33852 baseline rows were independently hashed; common.fixed passed before/after. Content inspection is targeted as listed here; hashing the remaining operational baseline is not a claim of reading every file.

The source claims failure of this actual unprojected OSD with eta_t=t^(-alpha), initial x1=0, against comparator0. It does not claim a minimax lower bound for every learner. Lean scores iterate t before loss t updates iterate(t+1). The horizon-dependent loss constructor is an adversarial witness; it does not supply future losses to the learner. The entire real loss stream is finite, so EReal coercion/toReal introduces no default-finiteness loophole.

The affine selector is genuinely determined: the old affine_subdifferential proof gives a singleton, hence nonemptiness and Classical.choose membership force the chosen vector. The first new proof must establish that fact for the actual selector. It must not replace the selector or assume a trajectory. Projection on fullSpace then provides the intended next dependency, with finite dimension supplying completeness. The regularity helper keeps finite dimension although its mathematical statement needs less; this restricts only a supporting helper and does not narrow the finite-dimensional source endpoint.

The odd/even scalar identity retains the ceil-minus-floor correction, the sum of i^(1-alpha), and the suffix from ceil+1 through T in source indexing. The draft uses separate real casts before subtraction and Ico ceil T in zero-based indexing. Direct numerical counterexample searches at six exponents and T=0..30 (186 cases) agree, but are diagnostics, not proofs. T0 and T1 both give zero. The lower-bound theorem separately requires the exact real threshold, so these horizons cannot be passed off as source instances.

The printed coefficient range and left limit are required independent leaves. The total Lean phi at alpha=1 evaluates to1; the left punctured limit is 1-log2, with lower comparison3/10. There is no endpoint continuity claim and no uniform phi>=0.3 assertion. The final existential theorem explicitly excludes the zero-dimensional space: otherwise every regret would be zero while the asserted lower bound is positive. The source proof itself reduces to dimension1 and embeds in dimensions at least2. Unit-vector helper alone cannot replace the existential endpoint.

The prospective short canary alpha=1/2,T2 has states0,1,1-1/sqrt2 and regret1, but fails the source horizon threshold. The full planned T64 canary is plausible: phi(1/2)=sqrt2-4/3>1/15 (equivalently sqrt2>7/5), so the threshold is at most60 and the proposed numeric lower bound is256/15>17. It must prove the actual 2D unit run and retain a new endpoint VALUE in the selected numeric branch. No canary type/body or arithmetic proof is accepted here.

Retained failures are correctly separated: retrieval v1 has three wrong namespace identifiers and v2 succeeds; type probe v1 emits an invalid zero-binder lambda and exits1, whereas v2 checks all11 Props and exits0. Unused-hypothesis lambda warnings are not proof weakening. Neither successful retrieval nor type elaboration is theorem compilation. The actual contemporaneous conversion window exists; no delayed-artifact claim is needed.

## Per-target seven-slot findings

### currentSubgradient_affine

- objects: Actual affine EReal selector in a real inner-product space
- quantifiers: All a,x,b; no finite dimension
- assumptions: Only stated normed/inner structures; global finite affine loss
- conclusion: Selected vector equals a, not merely membership
- constants_indices_boundaries: Zero a/intercept and zero-dimensional helper allowed
- information_structure: Current function and point only
- source_scope_delta: Shared singleton subdifferential makes first leaf dependency-ready

### step_affine_fullSpace

- objects: Actual full-space projection step
- quantifiers: All real eta,a,x,b in finite-dimensional E
- assumptions: No positivity needed for this algebraic identity
- conclusion: Actual step equals x-eta smul a
- constants_indices_boundaries: Zero/negative eta included
- information_structure: Current loss updates next state
- source_scope_delta: Finite dimension supplies completeness for existing projection API

### iterate_affine_prefix

- objects: Actual affine recursion
- quantifiers: All schedules, coefficient/intercept streams,x0,t
- assumptions: No boundedness/sign/monotonicity assumption
- conclusion: x0 minus weighted strict-prefix coefficient sum
- constants_indices_boundaries: range t; t=0 empty
- information_structure: Current coefficient excluded from current output
- source_scope_delta: No supplied trajectory; induction must produce identity

### powerSteps_pos

- objects: Real power schedule
- quantifiers: All real alpha and natural t
- assumptions: Positive base t+1
- conclusion: Strictly positive schedule
- constants_indices_boundaries: eta0=1; no zero base
- information_structure: Deterministic index-only
- source_scope_delta: Stronger alpha scope than source is harmless auxiliary algebra

### switching_loss_regular

- objects: Ambient switching affine loss
- quantifiers: All T,t and unit v in finite-dimensional E
- assumptions: Unit norm one
- conclusion: ConvexOn univ and LipschitzWith 1
- constants_indices_boundaries: Switch at ceil(T/2); even T0 helper meaningful
- information_structure: Fixed horizon-dependent stream, no learner future input
- source_scope_delta: Finite dimension is unnecessarily narrow for regularity alone but covers source endpoint

### switching_scalar_regret_identity

- objects: Actual scalar OSD regret
- quantifiers: All real alpha and natural T
- assumptions: No desired-regret or trajectory premise
- conclusion: Exact signed three-sum identity
- constants_indices_boundaries: Separate casts of ceil/floor; Ico ceil T; T0/1 give zero
- information_structure: Scores pre-update iterate t
- source_scope_delta: Derived identity; source odd/even term preserved

### phi_range

- objects: Exact phi scalar expression
- quantifiers: All alpha strictly between zero and one
- assumptions: Both strict interval assumptions
- conclusion: 0<phi<1-log2
- constants_indices_boundaries: Endpoints excluded; denominators positive
- information_structure: No algorithm premise
- source_scope_delta: Printed supplementary assertion remains required proof

### phi_limit

- objects: Total real phi and left-neighborhood filter
- quantifiers: Closed conjunction
- assumptions: No premise
- conclusion: Left limit 1-log2 and 3/10 lower comparison
- constants_indices_boundaries: phi(1)=1 by total division is not claimed equal to limit
- information_structure: Parameter limit, not regret-horizon convergence
- source_scope_delta: Printed assertion; no claim phi(alpha)>=0.3 throughout interval

### switching_scalar_lower_bound

- objects: Same scalar switching run
- quantifiers: All alpha in (0,1), all natural T meeting exact real threshold
- assumptions: No supplied lower bound or phi positivity premise
- conclusion: Half phi times T^(2-alpha) lower bounds actual regret
- constants_indices_boundaries: Threshold excludes T0; factor and exponent unchanged
- information_structure: Same canonical pre-update OSD/initial0/comparator0
- source_scope_delta: Explicit source witness, not all learners or all horizons for one stream

### switching_vector_lower_bound

- objects: Same run along unit vector
- quantifiers: All finite-dimensional E,alpha,T,v with norm1
- assumptions: Exact scalar threshold plus unit norm
- conclusion: Same coefficient lower bound for actual vector regret
- constants_indices_boundaries: No unit in dimension0
- information_structure: Actual selector and recursion must lift, not a surrogate trajectory
- source_scope_delta: General real finite-dimensional inner spaces represent source Euclidean dimensions

### theorem_5_4

- objects: Existential real loss stream on nontrivial finite-dimensional E
- quantifiers: For every eligible alpha,T exists one stream
- assumptions: Nontrivial E, exponent interval and threshold only
- conclusion: Played losses convex/1-Lipschitz and actual zero-comparator lower bound
- constants_indices_boundaries: Losses globally finite; regularity required t<T; dimension0 excluded
- information_structure: Witness may depend on horizon; algorithm remains strict past
- source_scope_delta: One source theorem plus coefficient facts, not eleven source results

## Exact permission and remaining gates

Freeze all eleven headers with their complete contexts and the four definitions before lowering. Only the first leaf currentSubgradient_affine is immediately authorized in NEW BanditRLProof/OnlineUnboundedOSD.lean with the frozen definitions/import context; preserve every existing baseline file. Its body must use the actual singleton selector semantics. Subsequent step/unroll and analytic/lower-bound leaves require dependency-ready staged progression under the unchanged frozen contract. No permission here for roots, Tests, readers, registry, global stores or publication. Any target change requires a new version and review.

Future readers must retain: source1=Lean0 and pre-update scoring; exact exponent interval/threshold/coefficient and one-sided limit; finite real losses and unbounded domain; explicit positive dimension and actual existential witness; one source theorem versus eleven Lean leaves; short versus threshold-qualified canaries; actual body/kernel/VALUE and combined gate status. All BODY/canary/full root/Tests/harness/fence/registry/site/pixel/FINAL/native/post-native/delivery gates remain pending. All eight Chapter2 forward containers remain required/open pending reconciliation, Chapter2 partial with null denominator, Chapters3-16 unenumerated, whole Goal ACTIVE. No Chapter5-wide, chapter, source-package, merged or live acceptance.
