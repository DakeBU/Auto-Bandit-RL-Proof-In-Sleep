"""Production/JSON/scripts/docs whitespace checked; immutable raw outputs separately enumerated."""
from common_v1 import *
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines();exceptions=[];checked=[]
for p in paths:
 reason=None
 if p.startswith(RUN.relative_to(ROOT).as_posix()+'/'):
  if p.endswith('.log'):reason='exact raw command output'
  elif '/snapshots/' in p or p.endswith('/manifest-before-nondiff-entry-v1.txt'):reason='exact original reviewed raw bytes/prefix'
  elif re.search(r'/source-pdf\d+-v1\.txt$',p):reason='exact PDF extraction'
  elif any(p.endswith('/formula-render-v'+str(i)+'-dom.html') for i in [1,2,3,4]):reason='exact browser DOM bytes'
 if reason:exceptions.append(dict(path=p,reason=reason))
 else:checked.append(p)
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE+'...HEAD','--']
batches=[];batch=[]
for path in checked:
 if batch and len(subprocess.list2cmdline(command+batch+[path]))>16000:batches.append(batch);batch=[]
 batch.append(path)
assert not batch or len(subprocess.list2cmdline(command+batch))<=16000
if batch:batches.append(batch)
assert [p for b in batches for p in b]==checked
results=[subprocess.run(command+b,stdout=subprocess.PIPE,stderr=subprocess.STDOUT) for b in batches]
child=subprocess.CompletedProcess(command,max((r.returncode for r in results),default=0),stdout=b''.join(r.stdout for r in results))
write(RUN/('scoped-diff-audit-'+sys.argv[1]+'.json'),dict(exit_code=child.returncode,base=BASE,checked_paths=checked,exceptions=exceptions,production_JSON_scripts_docs_checked=True,batch_count=len(batches),max_Windows_command_characters=max((len(subprocess.list2cmdline(command+b)) for b in batches),default=0),every_checked_path_in_exactly_one_batch=True,CRLF_lineendings_accepted=True))
print('Checked',len(checked),'paths; enumeratedexactrawexceptions',len(exceptions))
if child.returncode:print(child.stdout.decode('utf-8',errors='replace'))
sys.exit(child.returncode)
