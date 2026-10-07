from common_v1 import *
fixed(proving=True,integrated=True)
assert load(RUN/'scoped-diff-final-v1-exit.json')['exit_code']==1 and 'WinError 206' in (RUN/'scoped-diff-final-v1.log').read_text(encoding='utf-8')
source=(RUN/'check-scoped-diff-v2.py').read_text(encoding='utf-8')
old="child=subprocess.run(['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE+'...HEAD','--',*checked],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)"
assert old in source
new='''command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE+'...HEAD','--']
batches=[];batch=[]
for path in checked:
 if batch and len(subprocess.list2cmdline(command+batch+[path]))>16000:batches.append(batch);batch=[]
 batch.append(path)
assert not batch or len(subprocess.list2cmdline(command+batch))<=16000
if batch:batches.append(batch)
assert [p for b in batches for p in b]==checked
results=[subprocess.run(command+b,stdout=subprocess.PIPE,stderr=subprocess.STDOUT) for b in batches]
child=subprocess.CompletedProcess(command,max((r.returncode for r in results),default=0),stdout=b''.join(r.stdout for r in results))'''
source=source.replace(old,new).replace('production_JSON_scripts_docs_checked=True,','production_JSON_scripts_docs_checked=True,batch_count=len(batches),max_Windows_command_characters=max((len(subprocess.list2cmdline(command+b)) for b in batches),default=0),every_checked_path_in_exactly_one_batch=True,')
write(RUN/'check-scoped-diff-v3.py',source)
write(RUN/'publication-command-repair-v2.json',dict(stage='publication repair; mathematical acceptance unchanged',failed_gate='scoped-diff-final-v1',failed_log_sha256=sha(RUN/'scoped-diff-final-v1.log'),cause='Windows CreateProcess command line exceeds limit; diff check did not execute.',repair='Exact same production/JSON/scripts/docs path list partitioned into <=16000-character commands; all paths exactly once, all exits/output recorded; raw exceptions unchanged. No whitelist broadening, source/body/type/reader change.',full_harness_final_exit=load(RUN/'full-harness-final-v1-exit.json')['exit_code'],prior_FINAL_inputs_unchanged=True,PR_created=False,pushed=False,chapter_complete=False,goal_complete=False))
gate('scoped-diff-final-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v3.py','final-v2')
gate('source-scope-final-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','final-v2')
