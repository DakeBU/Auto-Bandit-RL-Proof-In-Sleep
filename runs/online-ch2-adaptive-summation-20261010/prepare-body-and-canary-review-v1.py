from common import *
fixed()
for name in ['production-focused-build-v1','production-public-value-axioms-v1','production-named-retrieval-v1','production-statement-fence-v2','production-safe-verify-v2','canary-full-context-type-probe-v1']:
    assert load(RUN/(name+'.json'))['actual_exit']==0,name
assert sha(RUN/'neutral-canary-reconstruction-v1.md')=='037d18df7bd60851443bca2d183d4ef19d1b7582dd8fd2fbcef82b02bdf201a0'
assert sha(RUN/'neutral-canary-reconstruction-v1.json')=='b49344ec9bf492b695a8cda28c2ca3f43d247fc05caed4841c190cfeef191e5d'
assert not (ROOT/'Tests/OnlineAdaptiveSummationCanary.lean').exists()
paths=list(CONTRACT.rglob('*'))+[PUBLIC]+list(RUN.glob('*'))+list((RUN/'fences').glob('*'))
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
paths += [ROOT/p for p in ['.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean','.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean','docs/theorem-publication-protocol.md']]
write(RUN/'body-and-canary-contract-review-inputs-v1.json',dict(rows=rows(paths),production_BODY_compiled=True,Test_BODY_absent=True,scope='Two separately stated verdicts: production BODY semantic review and exact two canary CONTRACT review. No package acceptance/integration/native acceptance.',chapter_complete=False,whole_Goal='active'))
write(RUN/'body-and-canary-contract-review-request-v1.md','''# Production BODY and separate canary CONTRACT review

Perform two distinct verdicts, not package acceptance. First independently audit the actual production BODY against the exact stabilized v2 terminal and source. The focused build and full public application/#print axioms/value are actual0; fence and safe-verify pass. Retained f-nonnegativity is unused and produces one honest warning; do not delete the premise or disable linters. Check cumulative endpoints, integrability restriction, antitone orientation, constant integral, sum and telescope, zero cases, exact complete header/context, and absence of hidden desired-bound assumptions. BODY-only semantic acceptance does not close package/canary/integration or chapters.

Second review the exact two canary CONTRACTs in canary-v1, full final import/scoped context and complete successful type probe, and the distinct complete source-blind reconstruction. Root has read the whole reconstruction. No Test BODY exists. First canary includes eight conjuncts: actual production inequality, exactsum1/4, exactintegral1/2, strict gap, nonconstant f and increments[1/2,0,1/2]. Second includes actual production inequalities for horizon0 and all-zeroincrements at horizon3, with offset2 and f(2)=1. The future BODY must directly instantiate the public production theorem for each of three inequality conjuncts; arithmetic alone cannot satisfy the implementation contract. No private/context assumptions or vacuous antecedents. Final compiled VALUE and selected-conjunct audit will separately test actual reuse, with presence not necessity caveat.

If accepted, allow only NEW Tests/OnlineAdaptiveSummationCanary.lean with exactly the two frozen public headers/context and necessary private arithmetic/integral helpers, and NEW OWN proof evidence. No root/Test-root/reader/registry/coverage/global/frontier or 34997 old baseline changes. Any type/context change needs a versioned review. Candidate acceptance, full combined gates, reader/shared graph integration, FINAL/native/postnative and PR remain future separately reviewed work. Chapter2 partial/null, Chapter4 unenumerated/null, eight forward/six future mathematical obligations required/open; whole Goal active. Hash all fixed current input rows before/after. Prior review's live native transition is explicitly explained by pre-stabilization-native-RAW-v2 and subsequent exact native event receipts; no assertion that changed live native files retain their old hashes.

Write only body-and-canary-contract-review-v1.md/json in this RUN, with all actually read inputs, exact source/type/deltas and separate production_BODY_verdict and canary_contract_verdict, required repairs and precise permitted scope. Reused automated source reviewer history/model request disclosed, not external/human or absolute independence. Do not author Test or mathematical proofs.
''')
fixed()
print('Review input SHA',sha(RUN/'body-and-canary-contract-review-inputs-v1.json'),flush=True)
