"""Bind actual PR creation and observed app attachment, preceding final metadata commit."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'pr-create-v1-01-exit.json')['exit_code']==0
pr=load(run/'pr-create-v1-01.log');assert pr['number']==162 and pr['draft'] and pr['merged_at'] is None
assert pr['base']=='f68646457a12de93ee6cb8d585a4162f9f0a112c'
assert pr['head']=='a64c3c1ce12a46984cfd8180abc7db4475bb1c64'
path=run/'pr-delivery-v1.json';assert not path.exists()
with path.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='OPEN-draft-PR-delivered',url=pr['html_url'],number=pr['number'],branch='codex/research-online-minorant-migration',creation_head=pr['head'],exact_stacked_base=pr['base'],stacked_base_PR=161,base_branch=pr['base_branch'],app_artifact_attached=True,attachment_evidence='Successful mcp__codex_app__attach_artifact in this task, observed tool result; no invented external receipt.',accepted_decision_sha256=hashlib.sha256((run/'accepted-decision-v1.json').read_bytes()).hexdigest(),site_source_commit=load(run/'registry-v1.json')['source_commit'],creation_head_differs_from_site_source_commit=True,retained_proofs=4,new_proofs=0,new_definitions=0,new_registry_nodes=0,legacy_before=15,legacy_after=14,chapter2_mandatory_total=None,parent_jensen_accepted=False,chapter2_complete=False,goal_complete=False,main_updated=False,live_updated=False,merged=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained and immediately reused for the next authorized Chapter2 Jensen task; no retirement/deletion/shared-link changes.',final_head_boundary='This creation receipt precedes its metadata commit; final clean local/remote/REST head checked directly after final push, without a log/commit loop.'),f,indent=2);f.write('\n')
print('Observed draft PR162 and app attachment recorded; Goal ACTIVE and Jensen next.')
