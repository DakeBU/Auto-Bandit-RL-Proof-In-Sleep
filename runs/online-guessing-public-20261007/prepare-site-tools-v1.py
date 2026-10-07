from common_v1 import *
fixed(True);old=Path('runs/online-guessing-osd-policy-20261007')
for name in ['browser-v1.py','render-source-card-v1.py','render-source-card-v1.cjs']:
 text=(old/name).read_text(encoding='utf-8').replace('online-guessing-osd-policy','online-guessing-public');write(RUN/name,text)
write(RUN/'check-scoped-diff-v1.py',(old/'check-scoped-diff-v1.py').read_text(encoding='utf-8'))
write(RUN/'commit-owned-v1.py',(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('codex/research-online-guessing-osd-policy','codex/research-online-guessing-osd-migration'))
paths=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/retrieval-index/online-guessing-public-20261007.md','research-wiki/contribution-contracts/online-guessing-public-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
baseline=Path('tmp/online-guessing-osd-policy-site-v1/books/registry.json');assert sha(baseline)==load(old/'registry-v1.json')['registry_sha256'] and len(load(baseline)['nodes'])==10821
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
write(RUN/'site-tools-before-first-use-v1.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['browser-v1.py','render-source-card-v1.py','render-source-card-v1.cjs','check-scoped-diff-v1.py','commit-owned-v1.py','owned-commit-paths-v1.json','registry-base-snapshot-v1.json']],shared_baseline_nodes=10821,new_nodes_expected=0,six_actual_cards=True,generated_site_edits=False))
print('Actual six-card tools/owncommit paths/shared10821 baseline prepared; no new nodes.')
