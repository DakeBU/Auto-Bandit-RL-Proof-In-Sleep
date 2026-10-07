from common_v1 import *
fixed(integrated=True);pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['ref']==BRANCH and pr['base']['ref']==BASE_BRANCH
assert load(RUN/'base-PR189-creation-fresh-v1.json')['head']['sha']==BASE and load(RUN/'app-attach-v1.json')['isError'] is False
assert a['source_package_accepted'] and a['new_public_math']==0 and a['new_source_subobligation_closures']==1 and not a['goal_complete']
for label in ['create-pr-v1','push-creation-v1','contributor-final-v1','scoped-diff-final-v1','source-scope-final-v1','committed-raw-audit-v1','full-harness-final-v1']:assert load(RUN/(label+'-exit.json'))['exit_code']==0
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-v3.json','registry-v4.json','pixel-review-v1.json','created-PR-v1.json','pr-payload-v1.json','app-attach-v1.json','committed-raw-audit-v1.json','full-harness-final-v1-exit.json']
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='One-typed-domain-mapping-accepted-draft-delivered',PR=pr['html_url'],number=pr['number'],branch=BRANCH,creation_head=pr['head']['sha'],exact_base_PR=189,exact_base_head=BASE,state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],applicable_site_commit=a['applicable_site_commit'],new_named_validation_proofs=8,new_public_math=0,new_public_definitions=0,new_source_subobligation_closures=1,new_production_registry_nodes=0,source_package_accepted=True,chapter_complete=False,goal_complete=False,merged=False,main_updated=False,live=False,remaining_required=a['remaining_required'],worktree=ROOT.as_posix(),worktree_disposition='Active total Goal checkout retained; unique source/runtime/site/profile cache and shared Git/.lake links preserved',final_head_checked_DIRECT_without_recursive_self_head_file=True))
write(RUN/'delivery-v1.md',f'''# Typed action/comparator Regret domain mapping delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, app-attached/unmerged. Branch {BRANCH}, exact PR189 base {BASE}; creationhead {pr['head']['sha']}; applicable clean local site source {a['applicable_site_commit']}. Later final metadata head checked DIRECT. Canonical main/live unchanged.

{a['scope']} Actual20named kernel/axiom checks,10 exact proposition and10 definition identities,10 full native guards,3 required VALUE pairs. Combined root9093/Tests9245/full harness472 tests7 existing skips. Same10835 shared IDsURLs/source-statementhashes,8 current panels individually inspected. Distinct reused required automated roles/CONTRACT/BODY/FINAL accepted with explicit deltas; allR1–R8 satisfied. Typed losses onW/outputsW/comparatorsV inclusion, same suppliedstream, source ordinarylimit versus epsilon upper interpretation explicit; no generic algorithm/minimum/ordinarylimit/nonnegative/uniform performance theorem. Illustrative negativegame derivesbound0, not assumed regretcertificate. All failed premises/commands/versioned repairs retained; no target weakening/human/external/runtime attestation.

{a['remaining_required']} Continue the next required whole Goal obligation.
''')
fixed(integrated=True)
