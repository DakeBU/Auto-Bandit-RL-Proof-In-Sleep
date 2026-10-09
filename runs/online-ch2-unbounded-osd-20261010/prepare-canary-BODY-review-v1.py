from common import *
from canary_driver import canary_guard, TEST
canary_guard()
v=load(RUN/'full-public-values-inspected-v1.json')
assert len(v['selected_canary_branches'])==4 and all(r['required_present'] for r in v['selected_canary_branches'])
paths=[PUBLIC,TEST,RUN/'baseline-v1.json',CONTRACT/'stabilized-v1.json',CONTRACT/'definitions-frozen-v1.json',CONTRACT/'canaries-stabilized-v1.json',CONTRACT/'canary-headers-draft-v2.json',RUN/'canary-neutral-packet-v1.json',RUN/'canary-blind-reconstruction-v1.md',RUN/'canary-blind-reconstruction-v1.json',RUN/'full-body-canary-review-v1.md',RUN/'full-body-canary-review-v1.json',RUN/'full-body-canary-review-inputs-v1.json',RUN/'full-body-canary-review-supplement-v1.json',RUN/'seven-leaf-body-review-v1.md',RUN/'seven-leaf-body-review-v1.json',RUN/'full-body-source-v1.lean',RUN/'full-body-obligations-v1.json',RUN/'FullSourceCanaryPublicV1.lean',RUN/'full-source-canary-public-v1.json',RUN/'full-source-canary-public-inspected-v1.json',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-graph-export-command-v1.json',RUN/'selected-value-graph-v1.json',RUN/'audit-selected-canary-branches-v1.lean',RUN/'selected-canary-branches-command-v1.json',RUN/'selected-canary-branches-v1.json',RUN/'full-public-values-inspected-v1.json',RUN/'two-canaries-local-milestone-v1.json',RUN/'prior-readonly-source-pdf64.png',RUN/'prior-readonly-source-pdf65.png',RUN/'prior-readonly-source-pdf64.txt',RUN/'prior-readonly-source-pdf65.txt',PDF]
paths+=list(CONTRACT.glob('frozen-*-v1.json'))+list(RUN.glob('safe-verify-*-command-v1.json'))
for short in ['scalar_actual_two_rounds','finiteDim_source_lower_bound']:
    paths+=[RUN/(short+s) for s in ['-attempt-v1.lean','-focused-build-v1.json','-native-fence-v1.json','-fence-compared-v1.json','-exact-before-v1.json']]
for p in paths: assert p.is_file(),p
manifest=RUN/'canary-BODY-review-inputs-v1.json'
write(manifest,dict(task=TASK,kind='Separate full7/9conjunction canary BODY and selected compiled VALUE review; not FINAL',rows=rows(paths),frozen_PUBLIC_Test=rows([PUBLIC,TEST]),old_baseline=33852,source_container_closed=False,chapter_complete=False,whole_Goal='ACTIVE'))
write(RUN/'canary-BODY-review-request-v1.md','''# Separate canary BODY review

Check every immutable input RAW SHA before/after and all33852 old tracked RAW rows. Personally inspect both complete Test theorem bodies, their frozen7/9conjunction types and actual compiled public examples. Review T2 pre-update regret=1 and real states/strictly decreasing positive steps, and T64 E2D unit vector, nonzero update, globally convex/Lipschitz losses, proved phi>=1/15/threshold, source bound,256/15<=R,17<R and fully applied theorem5.4 existential. Different horizon-specific streams: no common-prefix claim. Numeric and existential proof obligations must not be assumed, vacuous, replaced by scalar simulation or unused proof calls.

Inspect actual four separately selected compiled conjunct values: scalar index6 retains new scalar identity; vector indices6/7 retain new vector lower bound; vector index8 retains new theorem5.4. They are direct VALUE presences after top-level let substitution/And selection, not occurrence counts/full transitive graph/source counts. Audit all17public #check/#printaxioms and actual13safe-verify commands; retain distinction between complete typed examples and previous partial theorem application. Production BODY already independently accepted, now frozen unchanged; no source/definition/header weakening.

Record separate create-only canary-BODY-review-v1.md/json, actor requested Astra/medium and reused staged history/no runtime attestation; verdict, production_BODY_verdict, canary_BODY_verdict, required_repairs, report/path/SHA, input_manifest/path/SHA and RAW checks. Review ONLY this stage. If accepted allows preparation of exact prospective publication plan, not its materialization; root/readers/registry remain unchanged until separately reviewed plan. No chapter/container/Goal acceptance, merge/deploy or external human review claim.
''')
canary_guard()
print('Canary BODY immutable inputs:',len(load(manifest)['rows']),'manifest SHA',sha(manifest),flush=True)
