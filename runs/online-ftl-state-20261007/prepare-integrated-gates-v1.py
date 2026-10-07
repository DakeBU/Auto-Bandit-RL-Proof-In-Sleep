from common_v1 import *
fixed(proving=True,integrated=True)
write(RUN/'check-scoped-diff-v1.py',Path('runs/online-ftl-sharp-20261007/check-scoped-diff-v1.py').read_bytes())
baseline=Path('tmp/online-ftl-sharp-site-v2/books/registry.json')
assert sha(baseline)==load('runs/online-ftl-sharp-20261007/registry-v2.json')['registry_sha256'] and len(load(baseline)['nodes'])==10823
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
write(RUN/'site-tools-before-first-use-v1.json',dict(shared_base_nodes=10823,expected_new_production_nodes=12,new_public_proofs=9,new_public_definitions=3,source_subobligations=2,new_named_tests=6,source_cards=7,new_notes=9,old_curated_links=4,generated_site_edits=False,chapter_complete=False,goal_complete=False))
write(RUN/'retrieval-invocation-failure-v1.json',dict(actual_tool_call='Read guessed prepare-render-tools-v1.py/render_formulas_v2.py absent paths; remaining actual existing paths read successfully',scope='Read-only invocation error; corrected rg --files found actual capture-reader-v2.py/cjs. No edits or gate claims. One JSON registry read also produced an unnecessarily large single-line result; no evidence file modified.'))
