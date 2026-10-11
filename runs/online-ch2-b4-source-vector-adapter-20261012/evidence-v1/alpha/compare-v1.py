from pathlib import Path
import json,hashlib,sys
r=Path.cwd();d=r/'tmp/online-b4-vector-adapter-alpha-comparator-20261012'
a=json.loads((d/'scratch-constants-v1.json').read_text(encoding='utf-8'));b=json.loads((d/'canonical-constants-v1.json').read_text(encoding='utf-8'))
assert a==b, 'Imported constant occurrence or first-provider mismatch'
rows=[]
for row in a:
 for kind in ['TYPE','VALUE']:
  n=row['declaration'];x=d/('scratch-'+n+'-'+kind+'.txt');y=d/('canonical-'+n+'-'+kind+'.txt')
  hx=hashlib.sha256(x.read_bytes()).hexdigest();hy=hashlib.sha256(y.read_bytes()).hexdigest()
  rows.append({'declaration':n,'kind':kind,'scratch_alpha_sha256':hx,'canonical_alpha_sha256':hy,'equal':hx==hy})
result={'method':'binder names anonymized; mdata removed; all other Expr nodes preserved; no proof irrelevance or equality substitution','rows':rows,'all_equal':all(x['equal'] for x in rows)}
with (d/'canonical-comparison-v1.json').open('x',encoding='utf-8') as f:json.dump(result,f,indent=2)
assert result['all_equal']
print(json.dumps(result))
