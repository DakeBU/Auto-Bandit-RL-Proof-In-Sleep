"""Actual app-attached draft delivery, no chapter/book or main/live completion."""
from common_v1 import *
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['ref']=='codex/research-online-osd-policy-migration' and pr['base']['ref']=='codex/research-online-osd-migration'
assert load(RUN/'base-PR179-creation-fresh-v1.json')['head']['sha']==BASE and a['source_package_accepted'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and not load(RUN/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-final-v1-01','committed-raw-audit-v4-01']:passed(label)
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v3.json','created-PR-v1.json','pr-payload-v2.json','pr-payload-before-API-v2.json','app-attach-v1.json','pixel-review-v1.json','formula-render-v1.json']
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='scoped-policy-reuse-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=179,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],new_proofs=0,new_definitions=0,new_canary_proofs=0,new_registry_nodes=0,new_source_math_obligations_closed=0,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,remaining_required=a['remaining_required'],worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained to continue required Example2.32/linearization/unitanalysis packages after DIRECT final clean/localremoteREST/all-current-run-raw audit.',final_head_boundary='Final metadata head checked DIRECT without recursive self-head artifact.'))
write(RUN/'delivery-v1.md',f'''# Existing finite-history OSD policy evidence delivered

OPEN draft PR{pr['number']}: {pr['html_url']}; app-attached/unmerged. Branch {pr['head']['ref']}; exact PR179 base {BASE}; creation head {pr['head']['sha']}; applicable clean local site source {reg['source_commit']}. Final metadata head checked DIRECT afterwards. Canonical main/live unchanged.

Existing21 public proofs/7defs/2abbr and whole74canary proofs/11defs/7abbr remain unchanged. Zero new mathematical proofs/defs/registry nodes/maintext obligation closures. Current source/public revalidation only. Actual finite-history recurrence, played-only legality and same-run sharp fixed/variable/tuned/coarse terminals, exact canonical bridges. No randomized-law/measurable/executable/anytime or external-parameter independence claim.

Current focused{a['focused_jobs']} jobs/122named standard-only kernel checks/21guards; selected122 nodes95proofs27defs incl9abbr/{a['selected_direct_references']} directrefs/32pre-specified VALUE pairs. Combined{json.dumps(a['root_Tests_jobs'])} jobs inclcaches/fullharness{a['full_tests']} tests/{a['existing_skips']} existing skips. Exact-base contributor/scoped/taskshadow/cleanlocalLeanverifiedsite/10817preservedsharedIDsURLs21hashes/fiveactualimages pass. Required distinct decoder/CONTRACT/BODY/FINAL and allR1-R8 discharged. Nine OTHERChapter1 origin/main gaps UNWAIVED.

{a['remaining_required']} No merge/deploy/main/live/retirement. Active checkout retained after DIRECT final audit.
''')
fixed(True);print('Actual policy draftPR',pr['number'],'delivered; whole Goal ACTIVE, final DIRECT pending.')
