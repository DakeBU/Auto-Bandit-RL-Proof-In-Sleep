"""Bind real created PR without inventing a number or self-referential head."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pr=load(run/'created-PR-v1.json');a=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['base']['ref']=='codex/research-online-huber-migration' and pr['head']['ref']=='codex/research-online-closed-proper-migration'
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v2-01','scoped-diff-v2-01']:assert load(run/(label+'-exit.json'))['exit_code']==0,label
raw=load(run/'committed-raw-audit-v1.json');history=load(run/'history-binding-audit-v1.json');browser=load(run/'browser-v1-binding.json')
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json']
rows=[dict(path=(run/p).as_posix(),sha256=sha(run/p)) for p in paths]
data=dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch='codex/research-online-closed-proper-migration',exact_base_PR=165,exact_base_head='f989706461cb466bc290261f4845f113621e807d',creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=rows,legacy_remaining=9,retained_proofs=3,retained_definitions=2,new_proofs=0,new_registry_nodes=0,source_numbered_anchors=4,source_unnumbered_required_results=1,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for continuous same-project Chapter2 work; next branch only after final clean/local/remote/API-head and current-run Git-blob equality verification.',final_head_boundary='Final metadata head/remote/REST and ALL current-run raw blobs checked directly afterwards, no recursive self-head artifact.')
body=f'''# Closed/proper source package delivery

Draft PR{pr['number']}: {pr['html_url']}, OPEN/unmerged, attached to this chat. Branch codex/research-online-closed-proper-migration stacked on exact OPENdraftPR165f989706461cb466bc290261f4845f113621e807d. Creation head {pr['head']['sha']}; clean proof-site source {reg['source_commit']}; final metadata head is checked directly afterwards. Canonical main/live unchanged.

Four numbered anchors Definitions2.16/2.18/Examples2.17/2.19 plus REQUIRED unnumbered closedness/LSC equivalence, printed16/PDF28;3retainedproofs2complete definitions/whole6canaryproofs, zero new mathcode/registry nodes. Source Euclidean/stated Hausdorff sufficient scope to stronger arbitrary topology; realcuts/both infinities/bottomrealunion/topempty/no no-bottom-proper-convex/closedepigraph substitute. SourceProper core no topology, actual properiff retains TopologicalSpace. SAMEcanonical0/top indicator/directcuts/genuinefinitewitness/emptyambient allclosed-noneproper/fullindicatoriffambientnonempty. Three independent proof leaves/no mutual value edges; reading order not proof dependency.

Distinct CONTRACT/BODY/FINAL accepted-with-explicit-delta/no mathematical or required reader repairs. Final report SHA {a['final_review_report_sha256']}. Seven reader fixes checked against actual JSON/HTML.3nativeheaders/mathtokens/2complete definitions/originalrawsuffix/wholecanary/rootTests fixed.11named standard3-or-none axes/no sorryAx (including bottom_closed),3separate nativeguards, sequentialroot9089Tests9232/full466tests7existing skips, exactstacked contribution/history{history['raw_rows_verified']}rawrows/taskfrontier-shadow/scopedCRLFawarewhitespace passed. Actual gate invocations include cached jobs, no cleanrebuild claim. Default raw diagnostics retained with enumeratedexactrawexceptions/realtrailingblankchecks; currentrun*-text and committedraw audit{raw['checked_files']}files at its exact recorded commit, all final files checked directly after metadata commit. Earlier directories not blanket cross-platform recertified. ASTpreparation/rawfailure/unusedhelpername/read-only command errors retained, no mathematical/test weakening; globalreference-index rewrite notrun in boundedreusewindow.

Actualcompiled5scopednodes213directtype/value edges incl2definitions, notfull/canarygraph. Cleanlocalsite source_dirtyfalse/lean_verifiedtrue after current applicable combinedLeangate;5canonical sharedscopednodes/all10809oldIDsURLs/0new. Actual first1440x1800browserviewport viewed, screenshot SHA {browser['snapshot_sha256']}, no lower-fold/device claim. Server stopped/taskprofile retained/generated_site untouched. Three automatedactorsrequestedAstra/medium/restrictedpacket honesthistory/nohumanexternalruntimeattestation; nativecommandgates versusprompt/file conventions distinct.

Legacy10->9 ONLYOnlineClosedProper/zero newproofgain. Mainrelative contributiondiagnostic lacks9otherChapter1legacy productioncontracts. Chapter1migration/Chapter2mandatorytotalnull/incomplete/Chapters3–16mandatoryunenumerated/wholeGoalACTIVEunbudgeted. All required maintext/necessaryappendix obligations retained, some alreadycompiledbutunaudited. NoChapter3competitivewriting/merge/deploy/retirement. Checkout retained with sharedGit/junction/private/anonymous/runtime content preserved, next sameproject Chapter2 obligation begins only after final direct clean/local/remote/REST/rawblob verification.
'''
for name,x in [('delivery-obligations-overlay-v1.json',data),('delivery-v1.md',body)]:
 p=run/name;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x)
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
print('Real PR',pr['number'],'immutable accepted evidence bound; final direct head/clean/remote checks pending.')
