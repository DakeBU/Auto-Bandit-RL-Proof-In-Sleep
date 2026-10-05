from pathlib import Path
import hashlib,json
run=Path(__file__).parent
remote=json.loads((run/'pr-create-REST-v1-01.log').read_text(encoding='utf-8'))
assert remote['state']=='open' and remote['draft'] and remote['merged_at'] is None
assert remote['base']=='7c3b241a13b1b43d1efcd08429f33c93b890a981' and remote['head']=='64ce285053cd1c5727b88b6393b9ab8eff3ce93f'
assert remote['number']==160
target=run/'pr-delivery-v1.json';assert not target.exists()
data=dict(status='open-draft-stacked-PR-created',number=remote['number'],url=remote['html_url'],creation_head=remote['head'],stacked_base=remote['base'],base_PR=159,head_branch='codex/research-online-expectation-migration',base_branch=remote['base_branch'],accepted_decision='accepted-decision-v1.json',accepted_decision_sha256=hashlib.sha256((run/'accepted-decision-v1.json').read_bytes()).hexdigest(),boundary='Creation head differs from later metadata/final remote head. Representation foundation only, not Jensen/merge/live/chapter/book completion.',worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='retained for persistent active Goal')
with target.open('w',encoding='utf-8',newline='\n') as handle:json.dump(data,handle,ensure_ascii=False,indent=2);handle.write('\n')
print('Recorded actual OPEN draft PR160 and exact creation/base heads.')
