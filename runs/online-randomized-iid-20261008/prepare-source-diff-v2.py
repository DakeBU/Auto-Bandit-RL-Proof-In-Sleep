from common_integrated_v2 import *
import re

fixed_integrated()
assert load(RUN/'full-harness-v3-exit.json')['exit_code']==0
gate('source-scope-pre-stage-v2',sys.executable,'-B','-X','utf8',RUN/'audit-owned-scope-v2.py','pre-stage-v2')
paths=[line[3:] for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()]
globals={'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl'}
for group,raw in [([p for p in paths if p not in globals],True),([p for p in paths if p in globals],False)]:
    for offset in range(0,len(group),48):
        command=['git']+(['-c','core.autocrlf=false'] if raw else [])+['add','--']+group[offset:offset+48]
        child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
    for p in group:
        content=subprocess.check_output(['git','show',':'+p])
        if raw: assert content==Path(p).read_bytes(),p
        else: assert content.startswith(subprocess.check_output(['git','show',BASE+':'+p])),p
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
    'diff','--cached','--check',BASE,'--','.']
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'source-full-diff-v2.log',child.stdout)
diagnostics=child.stdout.decode('utf8',errors='replace')
write(RUN/'source-full-diff-v2-exit.json',dict(command=command,cwd=ROOT.as_posix(),
    actual_exit_code=child.returncode,log_sha256=sha(RUN/'source-full-diff-v2.log'),
    unexcluded_passed=child.returncode==0,source_and_evidence_staged_after_all_writers_finished=True,
    findings=[dict(path=p,line=int(line),message=message) for p,line,message in
        re.findall(r'(?m)^([^:\n]+):(\d+): ([^\n]+)',diagnostics)],
    package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual full staged whitespace diff exit:',child.returncode)
print('Finding paths:',sorted(set(p for p,line,message in re.findall(r'(?m)^([^:\n]+):(\d+): ([^\n]+)',diagnostics))))
fixed_integrated()
if child.returncode: raise RuntimeError('Full unexcluded whitespace diff failed; raw finding evidence preserved. Review exact raw-bound files before any scoped exception.')
