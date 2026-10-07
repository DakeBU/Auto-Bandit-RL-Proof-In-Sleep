"""Prepare current-route rendering/scope tools; no reader/proof mutation."""
from common_v1 import *
fixed(True)
old=Path('runs/online-osd-public-20261007')
browser=(old/'browser-v3.py').read_text(encoding='utf-8').replace('online-osd-public','online-osd-policy-public').replace('chapters/online-osd/','chapters/online-osd-policy/').replace('-v3','-v1')
write(RUN/'browser-v1.py',browser)
render=(old/'render-source-card-v3.py').read_text(encoding='utf-8').replace('common_v2','common_v1').replace('online-osd-public','online-osd-policy-public').replace('chapters/online-osd/','chapters/online-osd-policy/').replace('-v3','-v1').replace("len(rendered['cards'])==6","len(rendered['cards'])==4").replace('actual-six-source-cards','actual-four-source-cards').replace('[1,2,3,4,5,6]','[1,2,3,4]').replace('SIX actual source cards','FOUR actual source cards')
write(RUN/'render-source-card-v1.py',render)
js=(old/'render-source-card-v3.cjs').read_text(encoding='utf-8').replace('length>=6','length>=4').replace('count()!==6','count()!==4').replace('exactly SIX','exactly FOUR').replace('i<6','i<4').replace('actual-six-source-cards','actual-four-source-cards').replace('-v3','-v1')
write(RUN/'render-source-card-v1.cjs',js)
scope=(old/'check-scoped-diff-v1.py').read_text(encoding='utf-8').replace('common_v2','common_v1');write(RUN/'check-scoped-diff-v1.py',scope)
for n in ['commit-owned-v1.py','audit-committed-raw-v1.py']:
 text=(old/n).read_text(encoding='utf-8').replace('common_v2','common_v1').replace('codex/research-online-osd-migration','codex/research-online-osd-policy-migration');write(RUN/n,text)
paths=['runs/lifecycle_sessions.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/contribution-contracts/online-osd-policy-public-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
baseline=Path('tmp/online-osd-public-site-v3/books/registry.json')
assert sha(baseline)==load(old/'registry-v3.json')['registry_sha256'];assert len(load(baseline)['nodes'])==10817
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
write(RUN/'site-tools-before-first-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'browser-v1.py',RUN/'render-source-card-v1.py',RUN/'render-source-card-v1.cjs',RUN/'check-scoped-diff-v1.py',RUN/'commit-owned-v1.py',RUN/'audit-committed-raw-v1.py',RUN/'owned-commit-paths-v1.json',RUN/'registry-base-snapshot-v1.json']],shared_baseline_nodes=10817,four_performance_cards_only=True,no_source_targets_changed=True))
print('Own four-card renderer/scope tools and immutable shared registry baseline prepared.')
