"""Commit only this task's bounded source qualification and evidence."""
from pathlib import Path
import subprocess,sys
run=Path(__file__).parent
paths=['BanditRLProof/OnlineFTLFailure.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
    'research-wiki/contribution-contracts/ONLINE-FTL-MIGRATION-20261005.json','MANIFEST.md',
    'tasks/ONLINE-FTL-MIGRATION-20261005.md','conversion-windows/ONLINE-FTL-MIGRATION-20261005.md',
    'proof-obligations/ONLINE-FTL-MIGRATION-20261005.md','docs/contracts/online-ftl-migration-v1',str(run),
    'runs/online-ch2-enumeration-20261005','runs/lifecycle_sessions.jsonl','runs/trials.jsonl']
def call(args):
    p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode:print(p.stdout.decode('utf-8',errors='replace')[-1400:]);raise SystemExit(p.returncode)
    return p.stdout.decode('utf-8')
assert call(['git','branch','--show-current']).strip()=='codex/research-online-ftl-migration'
call(['git','add','--']+paths)
print(call(['git','commit','-m',sys.argv[1]])[:700])
status=call(['git','status','--porcelain']);assert not status,status
print('Clean committed task checkout',call(['git','rev-parse','HEAD']).strip())
