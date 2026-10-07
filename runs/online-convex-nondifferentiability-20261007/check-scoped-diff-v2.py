"""Production/JSON/scripts/docs whitespace checked; immutable raw outputs separately enumerated."""
from common_v4 import *
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines();exceptions=[];checked=[]
for p in paths:
 reason=None
 if p.startswith(RUN.relative_to(ROOT).as_posix()+'/'):
  if p.endswith('.log'):reason='exact raw command output'
  elif '/snapshots/' in p or p.endswith('/manifest-before-nondiff-entry-v1.txt'):reason='exact original reviewed raw bytes/prefix'
  elif p.endswith('/source-printed19-pdf31.txt'):reason='exact PDF extraction'
  elif any(p.endswith('/formula-render-v'+str(i)+'-dom.html') for i in [1,2,3]):reason='exact browser DOM bytes'
 if reason:exceptions.append(dict(path=p,reason=reason))
 else:checked.append(p)
child=subprocess.run(['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE+'...HEAD','--',*checked],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/('scoped-diff-audit-'+sys.argv[1]+'.json'),dict(exit_code=child.returncode,base=BASE,checked_paths=checked,exceptions=exceptions,production_JSON_scripts_docs_checked=True,CRLF_lineendings_accepted=True))
print('Checked',len(checked),'paths; enumeratedexactrawexceptions',len(exceptions))
if child.returncode:print(child.stdout.decode('utf-8',errors='replace'))
sys.exit(child.returncode)
