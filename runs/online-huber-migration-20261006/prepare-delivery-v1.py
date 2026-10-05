"""Bind PR creation and current accepted evidence without a self-referential head hash."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pr=load(run/'created-PR-v1.json');a=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert pr['number']==165 and pr['state']=='open' and pr['draft'] and not pr['merged']
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v2-01','scoped-diff-v2-01']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json']
rows=[dict(path=(run/p).as_posix(),sha256=sha(run/p)) for p in paths]
data=dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=165,creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch='codex/research-online-huber-migration',exact_base_PR=164,exact_base_head='52f628a7ae699887069c5a621d301901718ed772',creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=rows,legacy_remaining=10,retained_proofs=19,retained_definitions=3,new_proofs=0,new_registry_nodes=0,source_printed_results=1,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='retained for continued same-project Chapter2 work; next branch only after final clean/local/remote/API-head and current-run Git-blob verification',final_head_boundary='Final metadata commit/head, remote and REST state are checked directly afterwards; no recursive self-head hash artifact.')
for name,x in [('delivery-obligations-overlay-v1.json',data),('delivery-v1.md',f'''# Huber Example2.15 package delivery

Draft PR165: {pr['html_url']}, OPEN/unmerged, attached to this chat. Branch codex/research-online-huber-migration is stacked on exact OPENdraftPR164 head52f628a7ae699887069c5a621d301901718ed772; canonical main/live unchanged. PR creation head {pr['head']['sha']}. Clean proof-site source commit {reg['source_commit']}; later metadata delivery head is separately checked directly.

ONE printed Example2.15,19retained support proofs/3full definitions/whole14canaryproofs, zero new proof code/registry nodes. Source-implicit delta>=0 incl0, actual Hilbert generality/source Euclidean, features-before-prediction/labels-after, actual full-space projection/global RegularLoss/gradient producers. Sharp fixed positive-step allT>=0 bound retains negative terminal residual; T0 cancellation/delta0Z0 included. Positive known-horizon coefficient1 family eta_T=1/sqrtT, numeric upper-envelope Tendsto0 and literal one-sided actual average regret eventually<epsilon per fixed comparator; no actual signed convergence/anytime/uniform cutoff/Chapter4 claim.

Distinct CONTRACT/BODY/FINAL decisions accepted-with-explicit-delta with no mathematical or required reader repair. Final report SHA {a['final_review_report_sha256']}; all19native headers/math proof+3definition tokens/original suffix/wholecanary/rootTests unchanged.36named standard3-or-none axes/no sorryAx,19native guards, explicit sequentialroot9089/Tests9232/full466tests7existing skips, exactstacked contribution, historical21096raw rows, task-only frontier/shadow and scoped CRLF-aware whitespace passed. Default raw whitespace fails retain exact output/endings, no evidence trimming/global config change. Current-run * -text preserves exact raw Git blobs; separate audit checked378files at its recorded commit, all final current-run files checked directly after metadata commit. Earlier directories not blanket cross-platform recertified.

Actual scoped22nodes2954directtype/value edges includes definitions, not full/canary export. Clean local site/source_dirtyfalse/lean_verifiedtrue after applicable fresh Lean gate, shared22nodes/all10809oldIDsURLs/zero new nodes; actual first1440x1800viewport viewed/display1408x1760/SHAab03b307da4fda1a1583030a86439ed1ba17a3e029697843c56d040a241864b4; no lower-fold/physical-device claim. Server stopped, task profile/screenshot retained. Eight reader qualifications and pre-gate exact boundary phrase compatibility applied, no changed mathematics/tests. Read-only lookup errors recorded; global reference-index rewrite not run outside bounded window. Native command gates and role/prompt/file conventions remain separate; three automated actors requested Astra/medium, no human/external/runtime attestation.

Only OnlineHuber legacy migration11→10, zero new-proof gain. Main-relative contribution diagnostic still lacks9other Chapter1legacy paths. Chapter1migration/Chapter2mandatorytotalnull/incomplete/Chapters3–16mandatoryunenumerated/real whole Goal ACTIVE unbudgeted. All main-text/necessary appendix obligations retained, some alreadycompiled but unaudited; no Chapter3competitive writing. Checkout E:/ABRL/worktrees/research-online-book is retained/reused for next Chapter2closed/proper audit only after final local/remote/REST-head/clean checks; no retirement/sharedGit/junction/private/anonymous/generated_site modification, merge or deployment.
''')]:
 p=run/name;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x)
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
print('PR165 creation and immutable accepted evidence bound; final direct head/clean/remote verification pending.')
