import hashlib,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
helper=root/"tmp/online-ch2-prescient-euclidean-gates-20261011/capture-gate-v1.py"
assert hashlib.sha256(helper.read_bytes()).hexdigest()=="d7d10142361f940c51712e7dd174dfae51ad768f65f87f26decd87d91faf58fc"
head="3b393adb009bc25a2c6e3fa3148bf9a3a2b4c376"
gate=root/"tmp/online-ch2-prescient-euclidean-gates-20261011/actual-evidence-v2/combined-v2/receipt.json"
gsha=hashlib.sha256(gate.read_bytes()).hexdigest()
site=root/"tmp/online-ch2-prescient-euclidean-site-20261011-v1"
kind=sys.argv[1];version=sys.argv[2] if len(sys.argv)>2 else "v1"
if kind=="structural":
 spec=root/"tmp/online-ch2-prescient-euclidean-structural-20261011/input-spec-execution-v2.json"
 baseline=root/"tmp/online-ch2-unbounded-ogd-site-20261011-v2/books/registry.json"
 script=root/"tmp/online-ch2-prescient-euclidean-structural-20261011/check-prescient-structure-v4.py"
 assert hashlib.sha256(script.read_bytes()).hexdigest()=="9972b600caf600bf36c53ecbc3208a03ee71c374ef16a9923e2fe6587a7f8d87"
 argv=["python","-X","utf8",str(script),"--root",str(root),"--site",str(site),"--gate",str(gate),"--before",str(root/"runs/online-ch2-prescient-euclidean-20261011/integration-snapshots/before"),"--old-registry",str(baseline),"--spec",str(spec),"--output",str(root/("tmp/online-ch2-prescient-euclidean-structural-20261011/actual-result-"+version+".json")),"--head",head,"--gate-sha256",gsha,"--old-registry-sha256","6bbabc167361664910ed212e11de79574a30733a94a1a32c946b792281a33d40","--spec-sha256","ed5345bddaa9ac3dd6dacaafce00d02fadf1dd2df0644417015989335d6e0c59"]
elif kind=="render":
 qa=root/"tmp/online-ch2-prescient-euclidean-reader-qa-20261011"
 script=qa/"capture-prescient-euclidean-reader-v4.cjs"
 assert hashlib.sha256(script.read_bytes()).hexdigest()=="50a098cd5b3d7863ea95e623c9548fae53e007f0d28fa8365bd307174b8ce3d3"
 argv=[r"C:/Program Files/nodejs/node.exe",str(script),"http://127.0.0.1:8890/chapters/online-ogd/",str(qa/("capture-"+version)),str(qa/("edge-profile-"+version)),str(site/"books/registry.json"),str(root),str(site),str(gate),gsha,head]
else:raise ValueError(kind)
cmd=["python","-X","utf8",str(helper),"--root",str(root),"--run","tmp/online-ch2-prescient-euclidean-gates-20261011/actual-evidence-v2","--label",kind+"-"+version,"--leaf-contract","docs/contracts/online-ch2-prescient-euclidean-v1"]
for name in ["docs/proof-digestion-protocol.md","docs/evidence-routed-memory-protocol.md","docs/openai-math-assimilation-protocol.md","research-wiki/openai-math-2026-intake.json","runs/process_memory.json"]:cmd += ["--owned-source",name]
cmd += ["--"]+argv
sys.exit(subprocess.call(cmd,cwd=str(root)))
