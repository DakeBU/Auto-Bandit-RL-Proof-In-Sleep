from common_v1 import *
fixed(True)
paths=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/retrieval-index/'+TASK+'.md','research-wiki/contribution-contracts/online-foundations-public-20261007.json',CANARY.as_posix(),'Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
old=Path('runs/online-unit-scaling-public-20261007')
write(RUN/'commit-owned-v1.py',(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('codex/research-online-unit-scaling-migration',BRANCH))
write(RUN/'check-scoped-diff-v1.py',(old/'check-scoped-diff-v1.py').read_bytes())
baseline=Path('tmp/online-unit-scaling-public-site-v1/books/registry.json');assert sha(baseline)==load(old/'registry-v1.json')['registry_sha256']
assert len(load(baseline)['nodes'])==10821
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
write(RUN/'snapshots/Tests-root-after-one-import-v1.raw',Path('Tests.lean').read_bytes())
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
write(RUN/'site-tools-before-first-use-v1.json',dict(owned_commit_paths=paths,shared_baseline_registry_nodes=10821,new_production_nodes_expected=0,new_named_validation_proofs=7,route_source_cards=4,updated_source_cards=1,updated_public_notes=1,curated_links=4,expected_source_guide_formulas=7,source_guide_data_math_fields=7,generated_site_edits=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Owned scope/exact baseline/site help/after-import raw evidence prepared; site/registry/pixels pending.')
