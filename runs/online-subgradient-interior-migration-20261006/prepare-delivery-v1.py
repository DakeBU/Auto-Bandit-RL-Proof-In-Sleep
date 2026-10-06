"""Bind the real created and attached PR to this accepted source package."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pr=load(run/'created-PR-v1.json');a=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['base']['ref']=='codex/research-online-subgradient-basic-migration' and pr['head']['ref']=='codex/research-online-subgradient-interior-migration'
assert load(run/'base-PR167-fresh-v1.json')['head']['sha']=='b7b72d2c587128ddb639b2fd40c27016f20555bc'
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-v2-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json']
data=dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=167,exact_base_head='b7b72d2c587128ddb639b2fd40c27016f20555bc',creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(run/p).as_posix(),sha256=sha(run/p)) for p in paths],legacy_before=8,legacy_remaining=7,retained_proofs=1,new_proofs=2,new_definitions=0,new_registry_nodes=2,source_numbered_anchors=0,source_unnumbered_required_result_groups=2,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for continuous same-project Chapter2 work; next branch only after final direct clean/local/remote/REST and ALLcurrentrunGitblob equality verification.',final_head_boundary='Final metadata head and ALLcurrentrun raw blobs checked directly afterwards, no recursive self-head artifact.')
body=f'''# Interior existence package delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, attached to the chat, unmerged. Branch {pr['head']['ref']} on exact OPEN draftPR167 b7b72d2c587128ddb639b2fd40c27016f20555bc. Creation head {pr['head']['sha']}; clean applicable site source {reg['source_commit']}; final metadata head checked directly afterwards. Canonical main/live unchanged.

Orabona v10 printed17/PDF29: zero numbered anchors, two mandatory unnumbered source branches (ambient existence and stronger relative-interior footnote1). One retained ambient producer, two genuinely new proofs, zero new definitions. The affine contact helper is a necessary intermediate, not another printed result. It restricts to the ORIGINAL domain affine span at the prescribed point, reuses canonical ambient contact, extends the linear functional and corrects the intercept while retaining equality at the SAME point. The vector theorem uses Riesz and finite-dimensional derived completeness. Supports quantify over every ambient query. No closedness, full-dimensionality, differentiability, support oracle, new CompleteSpace binder or uniqueness added; zero dimension/zero slope and nonclosed lower-dimensional domains allowed. Generic S remains broader than source proper specialization. Three separate native guards preserve all frozen target headers and old code/test bytes. Genuine new ray/singleton canaries exercise producers; original interval canary retained.

Distinct automated CONTRACT/BODY/FINAL accepted-with-explicit-delta; final report SHA {a['final_review_report_sha256']}; nine reader requirements checked. Focused3307jobs/public body/canary builds/eight named standard kernel foundation checks without sorryAx/three native guards/sequential root9089 Tests9233/full466tests7existing skips passed. Cached jobs are included; no every-job clean rebuild claim. Actual selected graph8nodes1193direct references, not a full graph export. Site checks preserve10809old IDsURLs and add exactly2 canonical mathproof nodes (10811 total), with four source-qualified links and original shared Minorant ownership. Actual first browser viewport viewed; no lowerfold/device claim; server stopped, profile kept, generated _site untouched.

Preserved failures and concrete metadata-only repairs: untracked new packaging canary tracked without test/body changes; manifest Windows path normalized; registry verifier corrected reader-link versus formal ownership expectation. Full harness v3 passed after manifest repair. Default raw CRLF/evidence whitespace diagnostics retained alongside exact scoped real-blank checks/enumerated raw exceptions. Historical raw snapshots and actual binding checks retained. Source/preparation/parser/path errors and unused versions preserved. Native runtime gates and prompt/file conventions are distinct; three actors requested Astra/medium with restricted-packet honest history, no independent human/external/model-runtime attestation claim.

Legacy8 to7 ONLY OnlineSubgradientInterior; two new mathematical proof gains recorded separately. T2.22/T2.23 and all other Chapter1/2 mandatory obligations remain required. Main-relative diagnostic retains nine OTHER Chapter1 legacy contract gaps. Chapter2 mandatory total remains null/incomplete; Chapters3-16 unenumerated, whole Goal active/unbudgeted. No merge/deploy/main/live update or retirement. Shared Git/junctions/private/anonymous/runtime preserved. Next same-project Chapter2 obligation starts only after direct final clean/head/rawblob checks.
'''
for name,value in [('delivery-obligations-overlay-v1.json',data),('delivery-v1.md',body)]:
 p=run/name;assert not p.exists()
 p.write_bytes((value if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
print('Actual PR',pr['number'],'delivery recorded; final direct clean/head/rawchecks pending.')
