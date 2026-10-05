"""Version only the failed anonymous-instance lookup; freeze all old evidence."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'public-axioms-v1-01-exit.json')['exit_code']!=0
assert load(run/'probability-instance-retrieval-v1-01-exit.json')['exit_code']==0
actual=(run/'probability-instance-retrieval-v1-01.log').read_text(encoding='utf-8').splitlines()[:2]
assert actual==['Tests.OnlineJensenInfinite.instIsProbabilityMeasureNatLaw','Tests.OnlineJensenFinite.instIsProbabilityMeasureRealLaw']
changes=dict(zip(['Tests.OnlineJensenInfinite.instIsProbabilityMeasureLaw','Tests.OnlineJensenFinite.instIsProbabilityMeasureLaw'],actual))
metadata=load(run/'public-named-declarations-v1.json')
metadata['axiom_probe']=[changes.get(n,n) for n in metadata['axiom_probe']]
metadata['generated_instance_names_status']='Actual #synth/#print prefix retrieved; complete named audit still pending'
rows=[]
for srcname,destname in [('leaves/public-axioms-v1.lean','leaves/public-axioms-v2.lean'),('prepare-body-review-v1.py','prepare-body-review-v2.py')]:
 src=run/srcname;dest=run/destname;assert not dest.exists()
 text=src.read_text(encoding='utf-8')
 for old,new in changes.items():assert old in text;text=text.replace(old,new)
 if src.suffix=='.py':
  text=text.replace('public-axioms-v1-01','public-axioms-v2-01').replace('public-named-declarations-v1.json','public-named-declarations-v2.json')
  ast.parse(text)
 with dest.open('w',encoding='utf-8',newline='\n') as f:f.write(text)
 rows.append(dict(path=dest.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(dest)))
p=run/'public-named-declarations-v2.json';assert not p.exists()
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(metadata,f,indent=2);f.write('\n')
out=run/'auxiliary-audit-repair-preparation-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(rows=rows,actual_instance_names=actual,captured_before_execution=True,old_probe_log_exit_immutable=True,changes='Actual anonymous probability-instance constants and versioned audit paths only; all mathematical targets/bodies/canary unchanged.'),f,indent=2);f.write('\n')
print('Actual two probability instance names prepared in v2; full audit must still run.')
