"""Record actual created/attached draft PR; earlier acceptance history remains immutable."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pr=load(run/'created-PR-v1.json');a=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v2.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['base']['ref']=='codex/research-online-subgradient-differentiability-migration' and pr['head']['ref']=='codex/research-online-subgradient-sum-migration'
assert load(run/'base-PR169-fresh-v1.json')['head']['sha']=='52c24a9971a5d7953a129227b61384061ea3493e'
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
assert not load(run/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-v3-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v2.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json','app-attach-v1.json']
data=dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=169,exact_base_head='52c24a9971a5d7953a129227b61384061ea3493e',creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(run/p).as_posix(),sha256=sha(run/p)) for p in paths],legacy_before=6,legacy_remaining=5,retained_proofs=9,retained_definitions=1,new_proofs=0,new_definitions=0,new_test_proofs=0,new_registry_nodes=0,source_numbered_anchors=1,source_branches=2,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for continuous same-project Chapter2 work; next branch only after final direct clean/local/remote/REST and ALLcurrentrunGitblob equality verification.',final_head_boundary='Final metadata head and ALLcurrentrun raw blobs checked directly afterwards, no recursive self-head artifact.')
body=f'''# Theorem2.23 package delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, app attached, unmerged. Branch {pr['head']['ref']}, exact stacked PR169 base52c24a9971a5d7953a129227b61384061ea3493e. Creation head {pr['head']['sha']}; clean applicable site source {reg['source_commit']}; later final metadata head checked directly. Canonical main/live unchanged.

ONE printed T2.23/TWO branches/nine retained proofs/full simultaneous vector M definition/ZERO new production math or TESTs. {a['explicit_delta']}

Distinct automated CONTRACT/BODY/FINAL accepted-with-explicit-delta, eleven reader requirements checked; final report SHA {a['final_review_report_sha256']}. Fresh post-comment sequential root9089/Tests9234/full466tests7existing skips/whole20oldcanaryproofs3defs/29namedstandard kernelchecks/nineguards/exact contributor/scopedCRLF-aware whitespace/history42501rawbindings/site checks pass. Cached jobs included. Selected33nodes2844refs22valuepairs/readiness10nodes1146refs separate, not fullgraph. Shared10811oldIDsURLs/0newnodes, ten canonical module links/full M/original four curated links. Actual firstviewport only, server stopped/profile kept/generated _site untouched.

Actual firstsitecheck failed exactly-three notation-primer rule; reader-onlyv2 merges space entry into existing M entry retainingALLfour meanings, originalfourcuratedroutes and unchangedmathematics/generator/checker. Freshfullharness/site v2 passed; oldfailure/site/PNG preserved. Count/path/CLI/helper preparation diagnostics, partial/unused versions and original raw snapshots preserved; no proof/header/definition/canary weakening or hidden mathematical repair. Currentrun * -text/raw exceptions preserve exact evidence without blanket historical portability recertification. Command gates versus file/prompt conventions separate, three distinct automated actors requested Astra/medium/restricted history, no human/external/runtime model attestation.

Legacy6->5 ONLY OnlineSubgradientSum; no new source mathematical growth claimed from retained proof count. Next Example2.24 and remaining Chapter1/2/appendix obligations required; nineOTHERChapter1main-relativecontracts still fail required diagnostic. Chapter2total null/incomplete,3-16unenumerated, whole GoalACTIVE/unbudgeted. No merge/deploy/main/live update or retirement. Current worktree remains for continuous next package after direct final clean/head/rawblob checks.
'''
for name,value in [('delivery-obligations-overlay-v1.json',data),('delivery-v1.md',body)]:
 p=run/name;assert not p.exists();p.write_bytes((value.rstrip('\n')+'\n' if isinstance(value,str) else json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode())
print('Actual PR',pr['number'],'delivered; final direct clean/head/raw checks pending.')
