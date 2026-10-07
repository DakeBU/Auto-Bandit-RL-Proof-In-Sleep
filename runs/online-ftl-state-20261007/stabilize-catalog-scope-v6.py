from common_v1 import *
fixed(proving=True,integrated=True)
r=load(RUN/'catalog-scope-receipt-v6.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta' and not r.get('required_repairs',[]) and sha(r['report'])==r['report_sha256']
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for row in load(RUN/'catalog-scope-review-inputs-v6.json')['rows']:assert reviewed[row['path']]==row['sha256']==sha(row['path'])
snapshot=RUN/'snapshots/catalog-scope-v6-build_site.py.raw';write(snapshot,Path('website/scripts/build_site.py').read_bytes())
write(RUN/'catalog-scope-reviewed-source-resolution-v6.json',dict(original_live_path='website/scripts/build_site.py',immutable_snapshot=snapshot.as_posix(),sha256=sha(snapshot),reason='Exact reviewed preimplementation scanner bytes preserved; only approved source-presentation hook is permitted. No Lean/body input changes.'))
owned=load(RUN/'owned-commit-paths-v1.json')
add=['website/scripts/build_site.py','website/content/declaration-boundaries.json','tools/test_source_declaration_boundaries.py']
write(RUN/'owned-commit-paths-v2.json',owned+add)
write(RUN/'commit-owned-v2.py',(RUN/'commit-owned-v1.py').read_text(encoding='utf-8').replace('owned-commit-paths-v1.json','owned-commit-paths-v2.json'))
write('website/content/declaration-boundaries.json',load(RUN/'catalog-boundaries-proposed-v6.json'))
cpath=Path('research-wiki/contribution-contracts/online-ftl-state-20261007.json');write(RUN/'snapshots/contribution-before-catalog-v6.raw',cpath.read_bytes());c=load(cpath)
c['affected_files']+=add[:2]
c['target']+=' Approved narrow source-presentation repair: one generic shared opt-in source-range hook fixes only the new ftlState catalogue; no inherited definition hash migration.'
c['verification']['focused_checks'].append('Required focused Python source-boundary valid/stale/truncated/wrong-file checks; existing Lean19fullfences/24kernel/16VALUE1979refs unchanged. Boundaries are raw source presentation, not a Lean parser/kernel/native recursive := fence.')
c['verification']['site_check']='Same10823old IDsURLs/source-presentation hashes; exactly12new production nodes. Only newftlState source presentation corrected by approved source-qualified file/start/end/block pin; remaining11new nodes unchanged. Current freshsite/correctcatalogpixels required.'
c['truth_boundary']+=' Actual v3catalog appended nexttheorem. Approved scope-v6 pins exact unchanged3-lineftlState source for shared optional scanner hook;100old definition hash migrations NOTapplied, pending separate source-presentation audit. No mathematical target change.'
cpath.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode())
native('catalog-scope-stabilized-v6','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(scope='Reviewer-approved source-presentation conversion',catalog_scope_receipt=(RUN/'catalog-scope-receipt-v6.json').as_posix(),source_contract_v1_unchanged=True,old_registry_hash_migration=False,implementation_gates_pending=True)))
write(RUN/'catalog-scope-stabilized-v6.json',dict(status='Actual source-presentation scope accepted before implementation',receipt_sha256=sha(RUN/'catalog-scope-receipt-v6.json'),report_sha256=r['report_sha256'],fixed_rows=19,allowed_additional_files=add,public_Lean_sources_unchanged=True,source_contract_math_v1_unchanged=True,implementation_FINAL_pending=True,chapter_complete=False,goal_complete=False))
