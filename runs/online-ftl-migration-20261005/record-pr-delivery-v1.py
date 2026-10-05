"""Record actual PR creation/head separately from later evidence-only commits."""
from pathlib import Path
import hashlib,json,subprocess
run=Path(__file__).parent
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
for n in ['push-accepted-v1-01-exit.json','pr-create-v1-01-exit.json','pr-authoritative-v1-01-exit.json']:
    assert load(n)['exit_code']==0,n
pr=json.loads((run/'pr-authoritative-v1-01.log').read_text(encoding='utf-8'))
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()
assert pr['state']=='OPEN' and pr['isDraft'] is True and pr['mergedAt'] is None
assert pr['headRefOid']==head=='ee936af39d7dd9bb9af0166b17448a7204c8f12c'
assert pr['baseRefName']=='codex/research-online-ogd-migration'
result=dict(stage='accepted-local-and-stacked-draft-PR-delivered',PR=pr,
    payload_head_at_creation=head,later_metadata_commits_are_not_creation_payload=True,
    exact_stacked_base='4b55f5ebebb370ebe9e173b9bf5155b97a2e3998',predecessor_PR=154,
    app_attachment=dict(type='pull_request',url=pr['url'],attached=True),
    acceptance='accepted-decision-v1.json',raw_binding_audit='accepted-binding-audit-v1.json',
    source_reader_commit='477d8e2c572d02b457d4893158bc3e8949376002',
    retained_proofs=7,new_proofs=0,selected_old_production_paths=1,remaining_main_missing_paths=20,
    canonical_source='E:/ABRL/research',worktree='E:/ABRL/worktrees/research-online-book',
    disposition='Retained active checkout for next same-chapter package; ignored sourcePDF/graph/site/browser profile preserved. No retirement.',
    chapter_complete=False,book_complete=False,goal_complete=False,whole_goal='active',
    merged=False,deployed=False,main_updated=False,live_updated=False)
with (run/'pr-delivery-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Actual OPEN draftPR155 delivered/app-attached at exact creation payload; persistent whole-book Goal active.')
