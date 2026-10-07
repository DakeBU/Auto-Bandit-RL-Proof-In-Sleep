from common_v1 import *
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines();exceptions=[];checked=[]
for p in paths:
 reason=None
 if p.startswith(RUN.relative_to(ROOT).as_posix()+'/'):
  if p.endswith('.log'):reason='exact raw command output'
  elif '/snapshots/' in p:reason='exact reviewed raw source/prefix or native generated snapshot'
  elif re.search(r'/source-pdf\d+-v1\.txt$',p):reason='exact PDF extraction'
  elif p.endswith('/formula-render-v1-dom.html'):reason='exact browser DOM bytes'
 if reason:exceptions.append(dict(path=p,reason=reason))
 else:checked.append(p)
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE+'...HEAD','--']
batches=[];batch=[]
for path in checked:
 if batch and len(subprocess.list2cmdline(command+batch+[path]))>16000:batches.append(batch);batch=[]
 batch.append(path)
if batch:batches.append(batch)
assert [p for b in batches for p in b]==checked and all(len(subprocess.list2cmdline(command+b))<=16000 for b in batches)
results=[subprocess.run(command+b,stdout=subprocess.PIPE,stderr=subprocess.STDOUT) for b in batches]
code=max((r.returncode for r in results),default=0)
write(RUN/('scoped-diff-'+sys.argv[1]+'.json'),dict(exit_code=code,base=BASE,checked_paths=checked,exceptions=exceptions,batch_count=len(batches),max_Windows_command_characters=max((len(subprocess.list2cmdline(command+b)) for b in batches),default=0),every_path_checked_once=True,production_JSON_scripts_docs_checked=True,CRLF_lineendings_accepted=True))
print('Actual diff checked',len(checked),'paths; exactraw exceptions',len(exceptions))
if code:print(b''.join(r.stdout for r in results).decode('utf-8',errors='replace'))
sys.exit(code)
