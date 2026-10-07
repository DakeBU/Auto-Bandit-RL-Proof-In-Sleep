"""Prepare own render/scope/registry/delivery tools; no generated site edits."""
from common_v1 import *
headers();old=Path('runs/online-osd-policy-public-20261007')
for name in ['browser-v1.py','render-source-card-v1.py','render-source-card-v1.cjs']:
 text=(old/name).read_text(encoding='utf-8').replace('online-osd-policy-public','online-guessing-osd-policy').replace('chapters/online-osd-policy/','chapters/online-guessing-osd/')
 if name!='browser-v1.py':
  text=text.replace("len(rendered['cards'])==4","len(rendered['cards'])==6").replace('[1,2,3,4]','[1,2,3,4,5,6]').replace('actual-four-source-cards','actual-six-source-cards').replace('FOUR actual','SIX actual').replace('length>=4','length>=6').replace('count()!==4','count()!==6').replace('exactly FOUR','exactly SIX').replace('i<4','i<6')
 write(RUN/name,text)
scope=(old/'check-scoped-diff-v1.py').read_text(encoding='utf-8')
write(RUN/'check-scoped-diff-v1.py',scope)
commit=(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('codex/research-online-osd-policy-migration','codex/research-online-guessing-osd-policy')
write(RUN/'commit-owned-v1.py',commit)
audit=(old/'audit-committed-raw-v1.py').read_text(encoding='utf-8').replace('fixed(True)','headers()').replace('codex/research-online-osd-policy-migration','codex/research-online-guessing-osd-policy')
write(RUN/'audit-committed-raw-v1.py',audit)
paths=[PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl','runs/lifecycle_memory.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','proof-obligations/'+TASK+'.json','proof-obligations/'+TASK+'-proving-v1.json','research-wiki/retrieval-index/online-guessing-osd-policy-20261007.md','research-wiki/contribution-contracts/online-guessing-osd-policy-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
baseline=Path('tmp/online-osd-policy-public-site-v1/books/registry.json')
assert sha(baseline)==load(old/'registry-v1.json')['registry_sha256'] and len(load(baseline)['nodes'])==10817
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
write(RUN/'site-tools-before-first-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'browser-v1.py',RUN/'render-source-card-v1.py',RUN/'render-source-card-v1.cjs',RUN/'check-scoped-diff-v1.py',RUN/'commit-owned-v1.py',RUN/'audit-committed-raw-v1.py',RUN/'owned-commit-paths-v1.json',RUN/'registry-base-snapshot-v1.json']],shared_baseline_nodes=10817,six_actual_cards=True,no_source_targets_changed=True))
print('Own six-card rendering, bounded commit/raw audit and shared registry baseline prepared.')
