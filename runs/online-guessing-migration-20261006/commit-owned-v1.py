"""Commit the explicitly owned proof package, preserving unrelated workspaces."""
import subprocess,sys
paths=['BanditRLProof/OnlineGuessingOGD.lean','BanditRLProof/OnlineGuessingLower.lean','BanditRLProof/OnlineGuessingComparison.lean','BanditRLProof.lean','Tests/OnlineGuessingComparisonCanary.lean','Tests.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',
 'runs/online-guessing-migration-20261006','docs/contracts/online-guessing-migration-v1',
 'tasks/ONLINE-GUESSING-MIGRATION-20261006.md','conversion-windows/ONLINE-GUESSING-MIGRATION-20261006.md',
 'proof-obligations/ONLINE-GUESSING-MIGRATION-20261006.md','research-wiki/contribution-contracts/online-guessing-migration-20261006.json',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-guessing-migration'
for cmd in [['git','add','--',*paths],['git','commit','-m',sys.argv[1]]]:
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)
print(subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip())
