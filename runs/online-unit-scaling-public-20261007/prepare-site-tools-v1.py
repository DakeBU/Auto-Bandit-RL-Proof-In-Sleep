from common_v1 import *
fixed(True);old=Path('runs/online-optimal-step-public-20261007')
for name in ['project-gates-v1.py','commit-owned-v1.py','check-scoped-diff-v1.py','audit-scope-v1.py','source-site-gates-v1.py','capture-reader-v1.py','capture-reader-v1.cjs']:
 s=(old/name).read_text(encoding='utf-8')
 s=s.replace('online-optimal-step','online-unit-scaling').replace('optimal-step','unit-scaling')
 if name=='source-site-gates-v1.py':s=s.replace('exact_PR184_base_separately_passed','exact_PR185_base_separately_passed').replace('fixed-coefficient scalar','uniform coordinate unit-scaling').replace('11hashes','22hashes')
 if name=='capture-reader-v1.cjs':s=s.replace("'proof-bridge-v1.png',4,1","'proof-bridge-v1.png',5,1").replace("'worked-example-v1.png',5,1","'worked-example-v1.png',4,1")
 write(RUN/name,s)
s=(old/'verify-registry-v1.py').read_text(encoding='utf-8').replace('online-optimal-step','online-unit-scaling').replace('onlineoptimalstep','onlineunitscaling')
s=s.replace("len(x['proof_bridge']['steps'])==4","len(x['proof_bridge']['steps'])==5").replace('len(hi)==11','len(hi)==22').replace('highlight_links=11','highlight_links=22').replace('proofbridge_steps=4','proofbridge_steps=5').replace('11frozen native hashes,2cards11notes','22frozen native hashes,2cards22notes')
write(RUN/'verify-registry-v1.py',s)
paths=['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/retrieval-index/online-unit-scaling-public-20261007.md','research-wiki/contribution-contracts/online-unit-scaling-public-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
baseline=Path('tmp/online-optimal-step-public-site-v1/books/registry.json');assert sha(baseline)==load(old/'registry-v1.json')['registry_sha256'] and len(load(baseline)['nodes'])==10821
write(RUN/'registry-base-snapshot-v1.json',baseline.read_bytes())
for label,p in [('contributor','tools/check_contributor_contract.py'),('site-build','website/scripts/build_site.py'),('site-check','website/scripts/check_site.py')]:gate('help-'+label+'-v1',sys.executable,'-B','-X','utf8',p,'--help')
write(RUN/'site-tools-before-first-use-v1.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['commit-owned-v1.py','check-scoped-diff-v1.py','owned-commit-paths-v1.json','registry-base-snapshot-v1.json','verify-registry-v1.py','audit-scope-v1.py','capture-reader-v1.cjs','capture-reader-v1.py']],shared_baseline_nodes=10821,new_nodes_expected=0,source_cards=2,library_notes=22,route_data_formulas=15,expected_rendered_route_formulas=12,algorithm_three_math_steps_rendered_as_prose=True,wide_formula_builtin_scroll_pairs_required_if_present=True,generated_site_edits=False))
fixed(True);print('Owned unit-scaling site tools/same10821baseline prepared; no new nodes or generated edits.')
