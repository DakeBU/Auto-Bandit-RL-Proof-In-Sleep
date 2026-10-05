"""Commit only this package's explicitly owned paths; preserve all other worktrees."""
import subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
paths=['BanditRLProof.lean','Tests.lean','BanditRLProof/OnlineConstraintFiniteLoss.lean','Tests/OnlineConstraintFiniteLossCanary.lean',
 'MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl','runs/online-finite-loss-20261005',
 'docs/contracts/online-finite-loss-v1','tasks/ONLINE-FINITE-LOSS-20261005.md',
 'conversion-windows/ONLINE-FINITE-LOSS-20261005.md','proof-obligations/ONLINE-FINITE-LOSS-20261005.md',
 'research-wiki/contribution-contracts/online-finite-loss-20261005.json',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-finite-loss'
p=subprocess.run(['git','add','--',*paths],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert p.returncode==0,p.stdout.decode('utf-8',errors='replace')
p=subprocess.run(['git','commit','-m',sys.argv[1]],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)
print(subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip())
