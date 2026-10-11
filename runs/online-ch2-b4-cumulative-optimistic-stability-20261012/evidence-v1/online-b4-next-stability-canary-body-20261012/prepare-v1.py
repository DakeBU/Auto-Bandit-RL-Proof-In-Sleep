from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent;R=P.parent.parent
core=R/'tmp/online-b4-next-stability-body-20261012'
freeze=R/'tmp/online-b4-next-stability-canary-freeze-20261012'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bind(p):return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
def write(p,s):
 with p.open('x',encoding='utf-8',newline='\n') as f:f.write(s)
frozen=freeze/'scratch-context-and-statement-v1.txt'
s=frozen.read_text(encoding='utf-8');head,tail=s.split('theorem tight_stability_at_nonminimizer :\n',1)
statement=tail.split('\n\nend ',1)[0]
write(P/'HeaderElaboration-v1.lean',head+'#check ('+statement+'\n)\n\nend BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary\n')
pins=json.loads((core/'capture-pins-v1.json').read_text())
pins['core_dir']=str(core);pins['core_inputs']=[bind(core/x) for x in ['candidate-v1.lean','CumulativeOptimisticStabilityCandidate.olean','focused-v1/receipt.json']]
pins['release']=bind(freeze/'ignored-canary-body-resource-authorization-v1.json');pins['freeze']=bind(freeze/'local-canary-freeze-v1.json');pins['frozen_header']=bind(frozen);pins['header_probe']=bind(P/'HeaderElaboration-v1.lean');pins['capture']=bind(P/'capture-v1.py')
write(P/'capture-pins-v1.json',json.dumps(pins,indent=2)+'\n')
print(sha(P/'capture-pins-v1.json'))
