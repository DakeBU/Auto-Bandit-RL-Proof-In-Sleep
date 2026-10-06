"""Record scoped actual draft PR delivery, no chapter/book completion or merge claim."""
from common import *
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v2.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['base']['ref']=='codex/research-online-subgradient-sum-migration' and pr['head']['ref']=='codex/research-online-subgradient-absolute-migration'
assert load(RUN/'base-PR170-fresh-v1.json')['head']['sha']==BASE
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and not load(RUN/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-v4-01','committed-raw-audit-v3-01']:passed(label)
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v2.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v2.json','registry-v2.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json','app-attach-v1.json','formula-visual-review-v3.json']
counts={k:a[k] for k in ['retained_public_proofs','retained_definitions','new_public_proofs','new_definitions','new_test_proofs','new_registry_nodes','source_body_examples','source_cases']}
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=170,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],legacy_before=5,legacy_remaining=4,legacy_delta_only=['OnlineSubgradientAbsolute'],Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for continuous same-project Chapter2 work; next branch only after final direct clean/local/remote/REST and ALLcurrentrun NONIGNORED Gitblob equality verification.',final_head_boundary='Final metadata head and all current run nonignored raw blobs checked directly afterwards, no recursive self-head artifact.',**counts))
body=f'''# Example2.24 package delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, app attached, unmerged. Branch {pr['head']['ref']}, exact stacked PR170 base {BASE}. Creation head {pr['head']['sha']}; clean applicable site source {reg['source_commit']}; later final metadata head checked directly. Canonical main/live unchanged.

ONE body Example2.24, THREE sign cases, FOUR retained proofs/ZERO new mathematics or TESTs. {a['explicit_delta']}

Distinct automated CONTRACT/BODY/FINALv2 accepted-with-explicit-delta. Fresh applicable postcomment root9089/Tests9234/full466tests7existing skips, whole3oldcanaries/7namedstandard kernelchecks/4guards/exact contributor/scoped CRLF-aware whitespace/history53270raw bindings/site checks pass. Cached jobs included. Selected7proofnodes1024refs9valuepairs/readiness4nodes666refs separate, not fullgraph. All10811 shared IDs/URLs/0newnodes/4canonical links/4original curated routes/3notation entries preserved. Actual first viewport and source formula tall screenshot/crop inspected; FULL CLOSED [-1,1] and allthree rows visible. No blanket mobile/fullpage visual certification. Currentrun raw bindings exclude initial ignored runtime pycache, which is preserved locally.

Real failures remain: preparer quoting before execution; explanatory ASCII plus/minus spelling initially opened a nested Lean comment, repaired comment only with raw original mathematics retained; FINALv1 rejected damaged displayed zero row despite sitecheck passing, repaired only interval grouping; repeated native wrapper labels overwrote4oldcommand outputs and historyv2 failed, exact committed raw Git blobs recovered without changing rejected receipt and historyv3 passed; anchor screenshot command exited0 but pixels were blank, preserved/rejected and replaced by actual nonblank tall/crop evidence. The initial delivery raw audit ran before its new gate logs were committed, then git show HEAD:longpath hit a Windows path limit. Both failures remain; exact tree/blob-object reads avoid path disambiguation without renaming snapshots or changing global config. The all-current-run raw audit subsequently passed. No mathematical weakening or hidden proof failure. Native command gates distinct from file/prompt role conventions; three distinct automated actors requested Astra/medium, no human/external/runtime model attestation.

Legacy5->4 ONLY OnlineSubgradientAbsolute after this real PR. Example2.25 and remaining Chapter1/2/appendix obligations remain REQUIRED, nineOTHERChapter1 mainrelative contracts remain missing diagnostic. Chapter2 totalnull/incomplete,3-16unenumerated, wholeGoalACTIVE/unbudgeted. No merge/deploy/main/live or retirement. Current checkout retained for continuous next package after direct final clean/head/rawblob checks.
'''
write(RUN/'delivery-v1.md',body)
fixed(True)
print('Actual scoped PR',pr['number'],'delivered; final direct clean/head/raw checks pending.')
