from common_v1 import *
fixed(proving=True,integrated=True)
old=Path('runs/online-foundations-public-20261007')
write(RUN/'commit-owned-v1.py',(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('codex/research-online-foundations-migration',BRANCH))
write(RUN/'check-scoped-diff-v1.py',(old/'check-scoped-diff-v1.py').read_bytes())
baseline=Path('tmp/online-foundations-public-site-v2/books/registry.json');assert sha(baseline)==load(old/'registry-v2.json')['registry_sha256'] and len(load(baseline)['nodes'])==10821
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
write(RUN/'snapshots/Tests-root-after-one-import-v1.raw',Path('Tests.lean').read_bytes())
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
write(RUN/'site-tools-before-first-use-v1.json',dict(shared_baseline_registry_nodes=10821,new_production_nodes_expected=2,new_named_validation_proofs=6,route_source_cards=6,updated_source_cards=1,new_source_cards=2,old_curated_links=4,new_public_notes=2,expected_source_guide_formulas=9,data_math_fields=9,generated_site_edits=False,chapter_complete=False,goal_complete=False))
