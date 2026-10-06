"""Create one authorized draft PR after fresh exact-base, duplicate and push checks."""
from pathlib import Path
import hashlib,json,subprocess
run=Path(__file__).parent;repo='repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def api(label,*args):
 out=run/(label+'.json');assert not out.exists(),out
 child=subprocess.run(['gh','api',*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if child.returncode:
  (run/(label+'-error.log')).write_bytes(child.stderr)
  raise RuntimeError('API failed; inspect raw error and query duplicates before retry: '+label)
 out.write_bytes(child.stdout);return json.loads(child.stdout)
assert load(run/'push-creation-v1-01-exit.json')['exit_code']==0
payload=run/'pr-payload-v1.json';assert hashlib.sha256(payload.read_bytes()).hexdigest()==load(run/'pr-payload-before-API-v1.json')['sha256']
base=api('base-PR169-fresh-v1',repo+'/pulls/169')
assert base['state']=='open' and base['draft'] and not base['merged']
assert base['head']['sha']=='52c24a9971a5d7953a129227b61384061ea3493e' and base['head']['ref']=='codex/research-online-subgradient-differentiability-migration'
duplicates=api('duplicate-PR-fresh-v1',repo+'/pulls?state=all&head=DakeBU%3Acodex%2Fresearch-online-subgradient-sum-migration')
assert not duplicates,'Existing PR found; inspect/reuse, do not POST duplicate.'
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()
remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/codex/research-online-subgradient-sum-migration'],encoding='utf-8').split()[0]
assert remote==head
pr=api('created-PR-v1',repo+'/pulls','--method','POST','--input',payload.as_posix())
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==head
assert pr['base']['ref']=='codex/research-online-subgradient-differentiability-migration'
print(json.dumps(dict(number=pr['number'],url=pr['html_url'],creation_head=head,state=pr['state'],draft=pr['draft'],merged=pr['merged']),ensure_ascii=False))
