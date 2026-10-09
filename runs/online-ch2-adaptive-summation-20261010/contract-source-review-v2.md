# Lemma 4.13 source CONTRACT v2 review

Verdict: accepted-with-explicit-delta. No blocking repair. This is source/statement stabilization and a limited proof window, not a compiled BODY or package/chapter acceptance.

I first personally viewed both original pages with view_image detail original. Printed39/PDF51 motivates a current-observation adaptive step size, with zero-gradient skipping, and asks for an integral bound on an energy sum. Printed40/PDF52 states Lemma4.13: for nonnegative a0,...,aT and a continuous nonincreasing function f:[0,infinity)->[0,infinity), the sum from t=1 toT of a_t f(a0+sum_{i=1}^t a_i) is bounded above by the integral from a0 to sum_{t=0}^T a_t of f. Its proof compares the constant right-endpoint value on each nonnegative increment interval, then adds adjacent integrals. I reconstructed this before reading the proposed header and decoder. The source's later inverse-square-root application explicitly invokes a0 tending to zero; that later argument is not this contract.

The exact v2 header faithfully encodes the source. The real ambient extension is only constrained on Set.Ici0; all endpoints and integration intervals stay there. This is an explicit representation delta, not global regularity or a different theorem. Lean a(t) corresponds to source a_(t+1); the initial offset remains separate. The natural stream is used only on its finite prefix. The zero-horizon extension gives0<=0 and is consistent with empty summation. Nonnegativity of f is preserved even though the interval-comparison argument need not use it.

Seven slots:

1. objects_spaces: Source nonnegative offset and finite increments; Lean real offset/stream and total real f restricted to Set.Ici0. Equivalent restricted representation.

2. quantifiers: Universal offset, stream, function, natural horizon followed by five premises. Only played prefix constrained; no existence or desired-bound premise.

3. assumptions: Retains offset/increment nonnegativity, half-line relative continuity, antitonicity and nonnegative values. No global continuity or strict positivity added.

4. conclusion_metric: Weighted right-endpoint finite sum <= real interval integral over the same cumulative interval. Integrability follows from local compact-interval continuity, not a hidden new assumption.

5. constants_indices: Exact coefficient1; Lean t=0..T-1 corresponds to source1..T; inner range(t+1) includes current increment; a0 remains separate; no averaging.

6. information_probability: Deterministic numerical inequality. No causal learner, future-gradient policy, probability or regret guarantee is asserted.

7. boundary: T0 and zero increments/offset included. Only nonnegative arguments used; no direct inverse-sqrt-at-zero invocation or Theorem4.14 minimum equality accepted.

Counterexample-oriented checks found no mismatch: constant functions give the expected equality; zero increments contribute zero without division; increasing functions would reverse the endpoint comparison and are excluded; negative-offset or negative-increment cases are not silently admitted. A decreasing nonconstant continuous function on the half-line supports the intended nondegenerate future canary. f need not have any regularity at negative inputs. ContinuousOn at zero is relative right-sided continuity, so ambient discontinuity from the negative side is allowed.

The distinct neutral reconstruction correctly gives all universal binders, five premises, right endpoints, volume interval integral and zero cases. Its receipt assesses reconstruction only, not source or proof. The v1 actual typecheck exit1 is retained: unqualified Ici was ambiguous between Finset and Set in the membership binder. v2 explicitly qualifies Set.Ici, preserving the mathematical intent and import context. Actual complete source Prop/API and neutral Prop probes exit0; these are type elaborations with no theorem BODY. I verified the raw stdout hashes. The v1 diagnostic's error-recovery sorry display is not an authored admitted theorem.

The pinned API signatures provide a dependency-ready route: ContinuousOn.intervalIntegrable_of_Icc on each nonnegative cumulative interval; intervalIntegral.integral_const and integral_mono_on with antitonicity in the correct direction; sum_integral_adjacent_intervals to telescope. I read the actual relevant pinned Mathlib declarations/bodies. Existing natural-grid sum/integral comparisons have different unit intervals and are not this arbitrary-increment statement. Private cumulative endpoint/integrability helpers are permissible; do not replace source hypotheses by a stronger convenient variant or add desired integral bounds as premises.

The exact permitted new production path is BanditRLProof/OnlineAdaptiveSummation.lean, preserving definition-context-v2 and the single frozen lemma_4_13 header. Only its BODY and necessary private helpers may be written. One lower route is permitted. No other public theorem, root/Test import, reader/registry/coverage edit or old baseline mutation is authorized. Subsequent OWN attempt/lifecycle evidence must preserve historical pre-transition raw bindings rather than claim unchanged live metadata. Any terminal/context change requires a new version and review.

The actual conversion window and DAG retain the correct bounded dependency scope. All eight Chapter2 forward containers remain required/open, six future mathematical claims required/open/unenumerated. This is a Chapter2 prerequisite, not a competing Chapter4 main task; Chapter4 full inventory remains unenumerated/null. Actual causal adaptive OSD, zero-gradient skip, radius/energy edge cases, inverse-square-root summation, (4.4), Theorem4.14 and its min-versus-infimum issue remain separate required work. At zero energy and positive D the displayed positive-eta minimization need not attain its infimum; this review does not repair or close that later claim.

All105 indexed raw inputs passed before/after checks. common.fixed passed all34997 prior baseline files and the actual pinned PDF SHA. Source images were genuinely viewed this round. Semantic contract/context/decoder/director/architect/conversion/DAG and relevant API evidence were content-read; large baseline/reference indexes and unrelated historical cards are hash-bound context, not claimed fully semantically rereviewed. The JSON actually_read list distinguishes this scope. No file other than these two review outputs was changed.

Actor /root/source_reviewer is the reused distinct staged automated source reviewer, separate from formalizer and neutral decoder, following the repository semantic-roundtrip role. Requested GPT-6 Astra/medium is not runtime attestation. No independent human/external/absolute-blind claim. Proof compilation, canary BODY, combined project gates, source-facing publication, FINAL/native/postnative and delivery are all pending; whole Goal remains active.
