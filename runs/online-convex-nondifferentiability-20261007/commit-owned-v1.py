"""Commit only the new example's explicit source/evidence/publication paths."""
import subprocess,sys
paths=['BanditRLProof/OnlineConvexNondifferentiability.lean','Tests/OnlineConvexNondifferentiabilityCanary.lean','BanditRLProof.lean','Tests.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl','runs/online-convex-nondifferentiability-20261007','docs/contracts/online-convex-nondifferentiability-v1','docs/contracts/online-convex-nondifferentiability-v2','tasks/ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007.md','conversion-windows/ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007.md','proof-obligations/ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007.md','research-wiki/contribution-contracts/online-convex-nondifferentiability-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-convex-nondifferentiability'
for cmd in [['git','add','--',*paths],['git','commit','-m',sys.argv[1]]]:
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)
print(subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
