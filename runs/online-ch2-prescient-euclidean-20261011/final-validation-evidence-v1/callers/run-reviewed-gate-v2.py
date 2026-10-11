import subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
py=str(Path(r"C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe"))
commands={
"combined-v2":["python","-X","utf8","tools/bandit.py","check"],
"contributor-v2":[py,"-X","utf8","tools/check_contributor_contract.py","--base","8045070bf1ee53c83778d04eb168f8ad6f728b59"],
"process-memory-v2":[py,"-X","utf8","tools/check_process_memory.py","check"],
"site-preflight-v2":["python","-X","utf8","website/scripts/build_site.py","--output","tmp/online-ch2-prescient-euclidean-site-20261011-preflight-v2"],
"site-build-v2":["python","-X","utf8","website/scripts/build_site.py","--lean-verified","--output","tmp/online-ch2-prescient-euclidean-site-20261011-v1"],
"site-check-v2":["python","-X","utf8","website/scripts/check_site.py","--output","tmp/online-ch2-prescient-euclidean-site-20261011-v1"]}
label=sys.argv[1]
cmd=["python","-X","utf8","tmp/online-ch2-prescient-euclidean-gates-20261011/capture-gate-v1.py","--root",str(root),"--run","tmp/online-ch2-prescient-euclidean-gates-20261011/actual-evidence-v2","--label",label,"--leaf-contract","docs/contracts/online-ch2-prescient-euclidean-v1"]
for name in ["docs/proof-digestion-protocol.md","docs/evidence-routed-memory-protocol.md","docs/openai-math-assimilation-protocol.md","research-wiki/openai-math-2026-intake.json","runs/process_memory.json"]:
 cmd += ["--owned-source",name]
cmd += ["--"]+commands[label]
sys.exit(subprocess.call(cmd,cwd=str(root)))
