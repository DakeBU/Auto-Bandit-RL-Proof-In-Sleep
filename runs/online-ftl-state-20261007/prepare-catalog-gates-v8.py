from common_v1 import *
fixed(proving=True,integrated=True)
for name in ['capture-reader-v3.py','capture-reader-v3.cjs','verify-registry-v3.py']:
 target=name.replace('-v3','-v4');source=(RUN/name).read_text(encoding='utf-8').replace('-v3','-v4')
 if name=='verify-registry-v3.py':
  source += '''
current={x['id']:x for x in new};prior={x['id']:x for x in load(RUN/'registry-v3.json')['new_nodes']}
assert set(current)==set(prior)
changed=[k for k in current if current[k]['statement_sha256']!=prior[k]['statement_sha256']]
assert changed==['declaration:'+PRE+'ftlState']
from website.scripts import build_site as scanner
module_current=scanner.scan_module(PUBLIC)
stmt=next(x['statement'] for x in module_current['declarations'] if x['full_name']==PRE+'ftlState')
assert 'theorem' not in stmt and '| 0 => (0, initial)' in stmt and '| t + 1 => ftlMeanStep' in stmt
assert nodes['declaration:'+PRE+'ftlState']['statement_sha256']==hashlib.sha256(stmt.encode()).hexdigest()
write(RUN/'registry-boundary-repair-v4.json',dict(status='passed',changed_new_node=changed,all_other11_new_hashes_unchanged=True,all10823_old_ID_URL_statement_hashes_exact=True,complete_source_definition_presentation=stmt,native_definition_fence=False))
'''
  source=source.replace('from website.scripts import build_site as scanner','sys.path.insert(0,str(ROOT))\nfrom website.scripts import build_site as scanner').replace('IDsURLs/nativehashes','IDsURLs/source-presentation-hashes')
 write(RUN/target,source)
write(RUN/'check-scoped-diff-v2.py',(RUN/'check-scoped-diff-v1.py').read_text(encoding='utf-8').replace('[1,2,3]','[1,2,3,4]'))
write(RUN/'continue-catalog-site-v8.py','''from common_v1 import *
fixed(proving=True,integrated=True)
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v2.py','Repair only source-pinned recursive FTL state catalogue boundary'],check=True)
gate('contributor-reader-v5',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','reader-v5')
gate('source-scope-reader-v5',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','reader-v5')
native('full-harness-reader-v5','check')
raw=(RUN/'full-harness-reader-v5.log').read_text(encoding='utf-8');counts=re.search(r'Ran (\\d+) tests',raw);skips=re.search(r'OK \\(skipped=(\\d+)\\)',raw)
assert counts and skips and 'check passed' in raw
write(RUN/'combined-gates-reader-v5.json',{**load(RUN/'combined-gates-reader-v4.json'),'full_tests':int(counts[1]),'existing_skips':int(skips[1]),'current_source_catalog_repair_checked':True,'new_python_boundary_tests':6,'current_harness_log_sha256':sha(RUN/'full-harness-reader-v5.log')})
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v2.py','Bind current FTL state catalogue and complete harness gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-state-site-v4');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-state-site-build-v4.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v4.log',temporary.read_bytes());write(RUN/'site-build-v4-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v4.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v4',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v4',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v4.py')
fixed(proving=True,integrated=True)
''')
