from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
remote=json.loads((root/'pr-create-REST-v1-01.log').read_text(encoding='utf-8'))
assert remote['number']==159 and remote['state']=='open' and remote['draft'] and remote['merged_at'] is None
assert remote['base']=='c9b47c8ba79a234d0dfa6e8ef5643a43677dd33a'
assert remote['head']=='bf7c2f79eda61b95af3d1483cd39235d5f194288'
target=root/'pr-delivery-v1.json';assert not target.exists()
data={
 'status':'open-draft-stacked-PR-created', 'number':remote['number'], 'url':remote['html_url'],
 'creation_head':remote['head'], 'stacked_base':remote['base'], 'base_PR':158,
 'head_branch':'codex/research-online-optimality-migration', 'base_branch':remote['base_branch'],
 'accepted_decision':'accepted-decision-v1.json',
 'accepted_decision_sha256':hashlib.sha256((root/'accepted-decision-v1.json').read_bytes()).hexdigest(),
 'boundary':'Creation head is distinct from later metadata/final remote head. Not merge/live/chapter/book completion.',
 'worktree':'E:/ABRL/worktrees/research-online-book',
 'worktree_disposition':'retained for persistent active Goal'
}
with target.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(data,handle,ensure_ascii=False,indent=2);handle.write('\n')
print('Recorded actual OPEN draft PR 159 and exact creation/base heads.')
