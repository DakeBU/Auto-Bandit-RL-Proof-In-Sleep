from pathlib import Path
import json,hashlib,sys
sys.path.insert(0,'tools')
from abrl_lifecycle import statement_hash
out=Path('tmp/online-ch2-b4-strong-convex-growth-body-20261011')
def bind(p):
 p=Path(p);b=p.read_bytes();return dict(path=p.as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
raw=(out/'imported-production-v1.stdout.raw').read_text(encoding='utf-8');d=json.loads(raw.split('IMPORTED_PRODUCTION_JSON=',1)[1]);old=json.loads((out/'actual-dependencies-v1.json').read_text(encoding='utf-8'))
for k in ['TYPE','VALUE']:d[k]=sorted(d[k])
rep=d.pop('type_expression_repr');(out/'imported-production-type-repr-v1.txt').write_text(rep+'\n',encoding='utf-8')
d['type_expression_sha256']=hashlib.sha256(rep.encode()).hexdigest();d['type_expression_hash_convention']='SHA256 UTF8 exact Lean repr string, no trailing LF; runtime syntax fingerprint, not normalized mathematical equivalence';d['axioms']=['propext','Classical.choice','Quot.sound'];assert '[propext, Classical.choice, Quot.sound]' in raw
comparison={k:{'candidate_count':len(old[k]),'imported_count':len(d[k]),'equal':old[k]==d[k],'added':sorted(set(d[k])-set(old[k])),'removed':sorted(set(old[k])-set(d[k]))} for k in ['TYPE','VALUE']}
header=Path('docs/contracts/online-ch2-b4-strong-convex-growth-v1/neutral-frozen-header-v1.txt').read_text(encoding='utf-8');module=Path('BanditRLProof/OnlineStrongConvexMinimum.lean').read_text(encoding='utf-8');declheader=header[header.index('theorem '):header.index('\n\nend ')];actualheader=module[module.index('theorem '):module.index(' := by')]
assert actualheader==declheader
both=set(d['TYPE'])&set(d['VALUE']);typeonly=set(d['TYPE'])-set(d['VALUE']);valueonly=set(d['VALUE'])-set(d['TYPE'])
report=dict(status='IMPORTED_PRODUCTION_PROBE_ACTUAL_EXIT0_COMBINED_GATES_PENDING',module=d['module'],module_source=bind('BanditRLProof/OnlineStrongConvexMinimum.lean'),receipt=bind(out/'imported-production-v1.json'),comparison=comparison,exact_header_equal=True,lifecycle_statement_fingerprint=statement_hash(actualheader),fingerprint_api='tools/abrl_lifecycle.py statement_hash(normalize_statement)',export_api='Same Expr.getUsedConstantsAsSet and ConstantInfo.value?(allowOpaque=true) as tools/ProofGraphExport.lean; imported environment module ownership verified',type_expression_sha256=d['type_expression_sha256'],axioms=d['axioms'],TYPE_only=sorted(typeonly),TYPE_and_VALUE=sorted(both),VALUE_only=sorted(valueonly),counts=dict(TYPE=len(d['TYPE']),VALUE=len(d['VALUE']),TYPE_only=len(typeonly),TYPE_and_VALUE=len(both),VALUE_only=len(valueonly)),scope='Direct constant occurrence, not logical necessity. Import-only Mathlib.Analysis.Convex.Strong is retained by exact frozen imports; its StrongConvexOn abstraction is not a VALUE dependency.',production_modified_by_probe=False,purification='Local one-theorem audit only, not PURIFIED or Exposition acceptance')
(out/'imported-production-dependencies-v1.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');(out/'imported-production-comparison-v1.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'comparison':comparison,'counts':report['counts'],'fingerprint':report['lifecycle_statement_fingerprint'],'type_only':sorted(typeonly),'comparison_file':bind(out/'imported-production-comparison-v1.json')},ensure_ascii=True,indent=2))
