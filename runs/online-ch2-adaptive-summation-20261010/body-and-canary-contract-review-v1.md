# Production BODY and separate canary CONTRACT review

Verdict: accepted-with-explicit-delta for both production BODY and canary CONTRACT; no blocking repairs. This is the reused distinct automated source reviewer /root/source_reviewer, requested GPT-6 Astra / medium. Related staged history is disclosed; no human/external review, absolute blindness or runtime model attestation is claimed.

The source is Lemma 4.13, printed40/PDF52: a continuous nonincreasing nonnegative function on the nonnegative half-line is integrated over successive nonnegative increments. Its cumulative right-endpoint weighted sum is bounded by that integral. Source PDF51/52 pixels were personally viewed in the immediately preceding CONTRACT review; their unchanged hashes are checked here, with no fresh-view claim.

## Production BODY: seven slots

1. Objects: the actual real offset, real increment stream and ambient real function; only the nonnegative half-line is used.
2. Quantifiers: all natural T, with increment nonnegativity restricted to t<T. No hidden all-horizon premise.
3. Assumptions: exact offset/prefix nonnegativity, ContinuousOn, AntitoneOn and function nonnegativity are retained. The unused hf warning is real and not suppressed; no premise was removed.
4. Conclusion: exact factor-one sum versus the same cumulative interval integral, not an assumed bound or regret guarantee.
5. Indices/constants: s(n)=a0+sum(i<n)a(i); hs_step proves the interval length a(t), and the sampled endpoint is s(t+1). Source increments 1..T are reindexed 0..T-1.
6. Mechanism: hs_nonneg and hs_le place every interval inside Ici0. Continuity restricted to Icc supplies integrability. Antitone orientation gives f(s(t+1))<=f(x), hence integral_mono_on compares the constant endpoint integral to f. integral_const uses the actual interval length, sum_le_sum and adjacent-integral telescoping finish. No desired comparison is a premise.
7. Boundaries: T=0, zero increments and offset0 remain valid; no global continuity on negative arguments, strict positivity, stochastic model or inverse-square-root-at-zero inference is introduced.

The complete source body, generic application probe, printed proof structure and standard-only axioms were inspected. Focused build actual0/3285 jobs and public probe actual0 are durable evidence; safe-verify and the exact frozen hash pass. Large tactic-generated ring certificates are diagnostic expansion, not separately claimed new results. No recompilation was performed by this reviewer.

## Canary CONTRACTs: separate from unwritten bodies

The first closed eight-conjunct type uses q(x)=max(1-x,0), a=[1/2,0,1/2], offset0, T=3. Its right endpoints are 1/2,1/2,1, the weighted sum is 1/4 and integral is 1/2; strictness is genuine, q(0)!=q(1), and all three increments are explicit. Objects are concrete real functions; quantifiers are only bound sums/integral variables; there are no external assumptions; all eight conclusions are retained; indexing includes the current increment; the information structure is deterministic; the zero middle interval does not erase strictness elsewhere. This is a faithful nondegenerate instance, not a printed source theorem.

The second closed three-conjunct type distinguishes T=0 with unit increments from T=3 with zero increments, both starting at2 with h(x)=max(3-x,0). Both comparisons are 0<=0, while h(2)=1 rules out a zero-integrand explanation. Objects and endpoints are exact; no external assumptions or all-horizon quantifier is present; both non-strict comparisons and the nonzero value are conclusions; empty range and repeated endpoints are different boundaries; no online/probabilistic interpretation is introduced. The full neutral reconstruction agrees with both types and complete-context type probe actual0 is only Prop elaboration. Tests file does not yet exist.

Future bodies MUST instantiate the public lemma in each of the THREE non-strict inequality conjuncts. Later compiled selected-conjunct VALUE inspection is required; arithmetic alone is insufficient for this implementation contract. Presence of a call will not be described as logical proof necessity.

## Binding and permitted scope

All118 current indexed RAW rows were independently checked before and after. common.fixed independently verified all34997 old baseline rows and pinned PDF before and after. The prior105 CONTRACT inputs resolve exactly: only lifecycle sessions and state differ live, with original RAW recovered from the pre-stabilization base64 snapshot. Sessions append stabilized sequence1 and proving sequence2 with matching parents; current state points to sequence2/next3. The artifact journal is unchanged. These are historical resolution, not a claim that old live hashes stayed equal.

Only NEW Tests/OnlineAdaptiveSummationCanary.lean with the frozen two full headers and exact import/scoped context, necessary private arithmetic/integral helpers, and NEW OWN proof evidence is allowed. Any public type/context change requires versioned review. Production is now fixed. No root/Test-root, reader, registry, coverage, old baseline or global/native acceptance edits are authorized. Canary BODY, combined gates, site/pixels, FINAL/native/postnative and delivery remain pending. Eight Chapter2 forwards and six future mathematical obligations stay required/open; Chapter2 partial/null, Chapter4 unenumerated/null, whole Goal ACTIVE.
