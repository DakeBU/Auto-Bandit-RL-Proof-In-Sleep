"""Commit this package's explicit owned paths; retain every unrelated workspace."""
import subprocess,sys
paths=['BanditRLProof/OnlineConvexOptimality.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',
 'runs/online-optimality-migration-20261005','docs/contracts/online-optimality-migration-v1',
 'tasks/ONLINE-OPTIMALITY-MIGRATION-20261005.md','conversion-windows/ONLINE-OPTIMALITY-MIGRATION-20261005.md',
 'proof-obligations/ONLINE-OPTIMALITY-MIGRATION-20261005.md',
 'research-wiki/contribution-contracts/online-optimality-migration-20261005.json',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-optimality-migration'
for cmd in [['git','add','--',*paths],['git','commit','-m',sys.argv[1]]]:
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)
print(subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip())
