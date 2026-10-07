from common_v2 import *
fixed(True);old=Path('runs/online-guessing-public-20261007')
script=(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('codex/research-online-guessing-osd-migration',BRANCH);write(RUN/'commit-owned-v1.py',script)
write(RUN/'check-scoped-diff-v1.py',(old/'check-scoped-diff-v1.py').read_text(encoding='utf-8').replace('from common_v1 import *','from common_v2 import *'))
paths=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/retrieval-index/online-linearization-public-20261007.md','research-wiki/contribution-contracts/online-linearization-public-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
baseline=Path('tmp/online-guessing-public-site-v1/books/registry.json');assert sha(baseline)==load(old/'registry-v1.json')['registry_sha256'] and len(load(baseline)['nodes'])==10821
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
write(RUN/'site-tools-before-first-use-v1.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['commit-owned-v1.py','check-scoped-diff-v1.py','owned-commit-paths-v1.json','registry-base-snapshot-v1.json','verify-registry-v1.py','audit-scope-v1.py','capture-reader-v1.cjs','capture-reader-v1.py']],shared_baseline_nodes=10821,new_nodes_expected=0,one_card_thirteen_route_formulas=True,generated_site_edits=False))
print('Actual owned tools/shared10821 baseline prepared; no new nodes/duplicate proofs.')
