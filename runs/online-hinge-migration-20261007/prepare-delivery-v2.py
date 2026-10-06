"""Bind actual scoped delivery; do not replace full mandatory chapter totals with legacy counts."""
from common_v2 import *
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['head']['ref']=='codex/research-online-hinge-migration' and pr['base']['ref']=='codex/research-online-subgradient-max-migration'
assert load(RUN/'base-PR173-fresh-v1.json')['head']['sha']==BASE
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and not load(RUN/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v2-01','push-creation-v1-01','contributor-final-v2-01','scoped-diff-final-v2-01','committed-raw-audit-v2-01']:passed(label)
paths=['raw-storage-repair-v2.json','accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v2.json','created-PR-v1.json','pr-payload-v2.json','pr-payload-before-API-v2.json','app-attach-v1.json','formula-visual-review-v1.json','formula-render-v1.json']
counts={k:a[k] for k in ['source_body_examples','source_claims','supporting_foundations','retained_public_proofs','retained_definitions','new_public_proofs','new_definitions','new_test_proofs','new_registry_nodes']}
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=173,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],legacy_before=2,legacy_remaining=1,legacy_delta_only=['OnlineHinge'],Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for continuous next Chapter2 package after DIRECT clean/localremoteREST/all-current-run-nonignored raw Git blob audit.',final_head_boundary='Final metadata head is checked DIRECT without writing a recursive self-head artifact.',**counts))
write(RUN/'delivery-v1.md',f'''# Bounded Example2.27 delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, app attached/unmerged. Branch {pr['head']['ref']}; exact PR173 base {BASE}; creation head {pr['head']['sha']}; applicable clean local site source {reg['source_commit']}. Final metadata head checked DIRECT afterwards. Canonical main/live unchanged.

ONE body example/THREE branches, TWELVE supporting proofs/ONE terminal/TWO complete definitions; THIRTEEN retained proofs and zero new math/TEST/registry nodes. {a['explicit_delta']}

Actual CONTRACT/BODY/FINAL and native acceptance passed; separate command/source/canary/kernel/fence/dependency/combined rootTests/harness/contributor/scoped diff/history/shared registry/site/actual pixel evidence retained. All five old scalar canaries unchanged,20kernelchecks15guards/selected20nodes2161refs29valuepairs/ready15nodes1367refs23pairs. All10811oldIDsURLs/15publiccanonicalnodes/4highlights4curatedlinks3notations1sourcecard preserved. No 2D/newcanary/source-result-count13 claim. Nine reader obligations resolved. Required actors automated/requested Astra medium with honest prior history, no human/external/runtime attestation.

Unused pre-use helper corrections and readonly lookup diagnostics preserved, no mathematical weakening. Actual initial committed-raw-audit-v1-01 failed because Git core.autocrlf normalized native CRLF evidence; task-local -text attributes and renormalized staging preserve exact original reviewed working bytes. Version2 raw/contributor/scoped checks replace the failed delivery gate, whose raw output remains. Main-relative nine OTHERChapter1 contract gaps remain mandatory and unwaived. Native commands distinguish actual enforcement from file/prompt/role conventions. No productivity experiment.

Legacy2->1 ONLY OnlineHinge AFTER this realPR. Next Theorem2.28 affine transport and all remaining Chapter1/2 maintext/necessary appendices REQUIRED; Chapter2totalnull/incomplete,3-16unenumerated,totalGoalACTIVE. No merge/deploy/mainlive/retirement. Checkout retained; DIRECT final clean/head/raw audit precedes next branch.
''')
fixed(True)
print('Actual scoped hinge PR',pr['number'],'delivered; final DIRECT audit pending.')
