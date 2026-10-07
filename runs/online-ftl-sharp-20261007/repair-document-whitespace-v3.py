from common_v1 import *
fixed(proving=True,integrated=True);assert load(RUN/'scoped-diff-v2-exit.json')['exit_code']==2
paths=['conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','tasks/'+TASK+'.md'];changes=[]
for p in paths:
 raw=Path(p).read_bytes();assert raw.endswith(b'\n\n')
 snap=RUN/'snapshots'/('before-EOF-repair-'+p.replace('/','--')+'.raw');write(snap,raw)
 cleaned=raw.rstrip(b'\r\n')+b'\n';Path(p).write_bytes(cleaned)
 changes.append(dict(path=p,before_sha256=sha(snap),after_sha256=sha(p),only_trailing_blank_lines_removed=True))
write(RUN/'document-whitespace-repair-v3.json',dict(failed_gate_sha256=sha(RUN/'scoped-diff-v2-exit.json'),failed_log_sha256=sha(RUN/'scoped-diff-v2.log'),cause='Three own lifecycle documents have an extra blank line at EOF',repair='Remove only terminal blank lines, keep exact previous reviewed raw snapshots; source/contract/public/test/reader statements and bodies unchanged.',rows=changes,original_failure_retained=True))
fixed(proving=True,integrated=True)
