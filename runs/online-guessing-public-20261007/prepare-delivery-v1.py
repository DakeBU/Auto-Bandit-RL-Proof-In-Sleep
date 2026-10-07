"""Record actual app-attached bounded draft; final DIRECT audit remains separate."""
from common_v1 import *
fixed(True)
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v1.json')
assert pr['number']==183 and pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['head']['ref']=='codex/research-online-guessing-osd-migration' and pr['base']['ref']=='codex/research-online-guessing-osd-policy'
assert load(RUN/'base-PR182-creation-fresh-v1.json')['head']['sha']==BASE
assert a['source_package_accepted'] and a['new_proofs']==0 and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and load(RUN/'app-attach-v1.json')['isError'] is False
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-final-v1-01','source-scope-final-v1-01','committed-raw-audit-v1-01','full-harness-current-reader-v2-01']:
 assert load(RUN/(label+'-exit.json'))['exit_code']==0,label
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json','app-attach-v1.json','pixel-review-v1.json','formula-render-v2.json','full-harness-current-reader-v2-01-exit.json']
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='existing-canonical-source-public-reuse-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=a['site_source_commit'],branch=pr['head']['ref'],exact_base_PR=182,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],new_public_proofs=0,new_public_definitions=0,new_registry_nodes=0,new_source_math_closures=0,existing_public_proofs=12,existing_public_definitions=1,existing_canary_proofs=27,canary_definitions=6,canary_abbreviations=1,source_package_accepted=True,generic_policy_family='Already separately accepted and delivered PR182; not missing or counted twice.',Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,remaining_required=a['remaining_required'],worktree=ROOT.as_posix(),worktree_disposition='Active whole-book checkout retained for required linearization/optimal-step/unit-analysis and Chapter1/2 completion after final DIRECT audit; ignored artifacts/shared Git/.lake preserved.',final_head_boundary='Final metadata head checked DIRECT without recursive self-head artifact.'))
write(RUN/'delivery-v1.md',f'''# Canonical absolute-loss guessing evidence delivered

OPEN draft PR183: {pr['html_url']}; app-attached, unmerged. Branch {pr['head']['ref']}; exact PR182 base {BASE}; creation head {pr['head']['sha']}; applicable clean local site source {a['site_source_commit']}. Later delivery metadata head is checked DIRECT separately. Canonical main/live unchanged.

The existing twelve public proofs and one loss definition, twenty-seven canary proofs/six definitions/one abbreviation remain unchanged. Zero new mathematics, definitions, source-terminal closures or registry nodes. Full global support translation and closed tie set; actual canonical true projected OSD same-run all-comparator sqrt(T); only one-sided separately tuned horizon-family average control. PR182 history-policy family, four notes and two cards remain unchanged and already delivered.

Actual focused3323 jobs;47 named standard-only kernel checks;twelve frozen native/raw guards;25 prespecified proofVALUE pairs. Shared root9092/Tests9240 jobs including caches;full harness466 tests/seven existing skips, repeated for accepted/current reader metadata. Exact-base contributor/scoped preservation/own shadow/clean local Lean-verified site pass. All10821 shared registry IDs/URLs preserved with twelve current native hashes. Six cards/sixteen notes/four curated links; seven final actual browser images reviewed. Original screenshot occlusion and v2 repair preserved. Required distinct automated CONTRACT/BODY/FINAL and neutral decoder roles discharge R1-R8; no human/external/runtime attestation. Explicit retained raw snapshots resolve the six original website rows; old receipts stay unchanged. Nine OTHER Chapter1 origin/main contributor gaps remain UNWAIVED.

{a['remaining_required']} No merge/deploy/main/live update/retirement. Active checkout retained to continue this total Goal.
''')
fixed(True);print('Actual bounded canonical reuse PR183 delivered; zero new math; whole Goal ACTIVE; final DIRECT audit pending.')
