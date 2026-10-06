"""Record actual bounded PR delivery; never close the chapter or whole Goal."""
from common_v2 import *
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['head']['ref']=='codex/research-online-subgradient-max-migration' and pr['base']['ref']=='codex/research-online-normal-cone-migration'
assert load(RUN/'base-PR172-fresh-v1.json')['head']['sha']==BASE
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
assert not load(RUN/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-final-v1-01','committed-raw-audit-v1-01']:passed(label)
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json','app-attach-v1.json','formula-visual-review-v1.json','formula-render-v1.json']
counts={k:a[k] for k in ['retained_public_proofs','retained_definitions','new_public_proofs','new_definitions','new_test_proofs','new_registry_nodes','source_formal_results','source_claims','supporting_foundations']}
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=172,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],legacy_before=3,legacy_remaining=2,legacy_delta_only=['OnlineSubgradientMax'],Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for continuous same-project Chapter2 work; next branch only after DIRECT clean/local/remote/REST and all current run nonignored raw Git blob checks.',final_head_boundary='Final metadata head is checked DIRECT without creating a recursive self-head artifact.',**counts))
write(RUN/'delivery-v1.md',f'''# Bounded Theorem2.26 package delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, app attached, unmerged. Branch {pr['head']['ref']}; exact PR172 base {BASE}. Creation head {pr['head']['sha']}; applicable clean local site source {reg['source_commit']}. Final metadata head will be verified DIRECT afterwards. Canonical main/live unchanged.

ONE source theorem, ONE terminal, SIXTEEN supporting proofs, TWO retained full definitions: SEVENTEEN retained public proofs and zero new mathematical/TEST/registry nodes. {a['explicit_delta']}

Actual staged CONTRACT/BODY/FINAL and native accepted event passed. Automated required roles with requested Astra/medium are distinct; no human/external review or attested runtime model provenance. Root9089/Tests9234/full466tests7existing skips, whole19oldcanaryproofs2TESTdefs/40kernelchecks/19guards and exact-base contributor pass. Readiness19nodes1795references16pairs and selected40nodes3402references21pairs are separately checked, not the full registry. All10811 old IDs/URLs,19publiccanonical links,5highlights,4curated links,3notations and1sourcecard preserved. Actual firstviewport and full MathJax sourcecard pixels were reviewed; no mobile/physical/fullpage/live claim. 66489 historical raw bindings verified.

Failures and pre-use corrections remain in immutable versioned evidence. Actual Lean API probe, output-boundary helper, history-variable and contributor-prefix repairs did not change mathematical statements, bodies or canary. Separate main-relative contributor diagnostic still fails for nine OTHER mandatory Chapter1 contracts, not waived. Command-enforced gates and prompt/file/role conventions remain distinct. No productivity experiment is claimed.

Legacy3->2 ONLY OnlineSubgradientMax AFTER actual PR delivery. Next Example2.27 hinge and all remaining Chapter1/2 maintext and necessary appendix work REQUIRED. Chapter2 mandatory total null/incomplete; Chapters3-16 unenumerated; persistent total Goal ACTIVE. No merge/deploy/main/live/retirement. Retain this checkout for the next scoped package after DIRECT final audit.
''')
fixed(True)
print('Actual scoped Max PR',pr['number'],'delivered; final DIRECT clean/head/all-raw checks pending.')
