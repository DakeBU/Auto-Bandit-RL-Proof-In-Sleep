from common_v1 import *
fixed(True);old=Path('runs/online-linearization-public-20261007')
write(RUN/'commit-owned-v1.py',(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('codex/research-online-linearization-migration',BRANCH))
write(RUN/'check-scoped-diff-v1.py',(old/'check-scoped-diff-v1.py').read_text(encoding='utf-8').replace('common_v2','common_v1'))
write(RUN/'audit-scope-v1.py',(old/'audit-scope-v1.py').read_text(encoding='utf-8').replace('common_v2','common_v1'))
script=(old/'verify-registry-v1.py').read_text(encoding='utf-8').replace('common_v2','common_v1').replace('online-linearization','online-optimal-step').replace('onlinelinearization','onlineoptimalstep').replace('native-statement-fingerprints-v2','native-statement-fingerprints-v1').replace('[3,4,1]','[3,4,2]').replace('len(hi)==18','len(hi)==11').replace('source_cards=1,highlight_links=18','source_cards=2,highlight_links=11').replace('18frozen native hashes, onecard18notes4curatedlinks','11frozen native hashes,2cards11notes4curatedlinks')
write(RUN/'verify-registry-v1.py',script)
paths=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/retrieval-index/online-optimal-step-public-20261007.md','research-wiki/contribution-contracts/online-optimal-step-public-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
baseline=Path('tmp/online-linearization-public-site-v1/books/registry.json');assert sha(baseline)==load(old/'registry-v1.json')['registry_sha256'] and len(load(baseline)['nodes'])==10821
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
write(RUN/'site-tools-before-first-use-v1.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['commit-owned-v1.py','check-scoped-diff-v1.py','owned-commit-paths-v1.json','registry-base-snapshot-v1.json','verify-registry-v1.py','audit-scope-v1.py','capture-reader-v1.cjs','capture-reader-v1.py']],shared_baseline_nodes=10821,new_nodes_expected=0,source_cards=2,route_data_formulas=15,expected_rendered_route_formulas=12,algorithm_three_math_steps_rendered_as_prose=True,wide_formula_builtin_scroll_pairs_required_if_present=True,generated_site_edits=False))
fixed(True);print('Owned scope/site tools and same10821 baseline prepared; no new nodes.')
