"""Create one scoped authorized draft after exact-parent/push/duplicate checks."""
from common_v2 import *
repo='repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep'
def api(label,*args):
 out=RUN/(label+'.json');assert not out.exists(),out
 child=subprocess.run(['gh','api',*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if child.returncode:write(RUN/(label+'-error.log'),child.stderr);raise RuntimeError('Inspect actual API result and duplicates before retry: '+label)
 write(out,child.stdout);return json.loads(child.stdout)
passed('push-creation-v1-01');payload=RUN/'pr-payload-v1.json';assert sha(payload)==load(RUN/'pr-payload-before-API-v1.json')['sha256']
base=api('base-PR178-creation-fresh-v1',repo+'/pulls/178');assert base['state']=='open' and base['draft'] and not base['merged'] and base['head']['sha']==BASE and base['head']['ref']=='codex/research-online-convex-uncountability'
duplicates=api('duplicate-PR-fresh-v1',repo+'/pulls?state=all&head=DakeBU%3Acodex%2Fresearch-online-osd-migration');assert not duplicates,'Inspect/reuse existing PR instead of duplicating.'
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip();remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/codex/research-online-osd-migration'],encoding='utf-8').split()[0];assert remote==head
pr=api('created-PR-v1',repo+'/pulls','--method','POST','--input',payload.as_posix());assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==head and pr['base']['ref']=='codex/research-online-convex-uncountability'
print(json.dumps(dict(number=pr['number'],url=pr['html_url'],creation_head=head,state=pr['state'],draft=pr['draft'],merged=pr['merged']),ensure_ascii=False))
