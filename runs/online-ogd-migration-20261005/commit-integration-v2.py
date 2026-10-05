"""Scope subsequent OGD integration/evidence commits without touching unrelated paths."""
from pathlib import Path
import subprocess,sys
run=Path(__file__).parent
paths=['BanditRLProof/OnlineGradientDescentVariable.lean',
    'website/content/readings.json','website/content/highlights.json',
    'research-wiki/contribution-contracts/ONLINE-OGD-MIGRATION-20261005.json',
    str(run),'runs/lifecycle_sessions.jsonl','runs/trials.jsonl']
def call(args):
    p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode:print(p.stdout.decode('utf-8',errors='replace')[-1200:]);raise SystemExit(p.returncode)
    return p.stdout.decode('utf-8')
assert call(['git','branch','--show-current']).strip()=='codex/research-online-ogd-migration'
call(['git','add','--']+paths)
print(call(['git','commit','-m',sys.argv[1]])[:600])
status=call(['git','status','--porcelain']);assert not status,status
print('Clean committed checkout',call(['git','rev-parse','HEAD']).strip())
