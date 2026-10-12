from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent;R=P.parent.parent
def rec(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
def read(n):return json.loads((P/n).read_text(encoding='utf-8'))
def put(n,v):
 with (P/n).open('x',encoding='utf-8',newline='\n') as f:json.dump(v,f,indent=2);f.write('\n')
stages=['header-v1','header-v2','focused-v1','imported-v1']
rs={n:read(n+'/receipt.json') for n in stages}
for n in stages[1:]:
 q=rs[n];assert q['actual_exit']==0 and q['integrity_pass']
 assert q['runtime_before']==q['runtime_after'] and len(q['runtime_before'])==19
 assert q['companion_membership_before']==q['companion_membership_after']
a=read('imported-audit-v1.json');o=read('imported-origins-v1.json');cl=read('closure-manifest-v1.json')
old={x['module']:str(Path(x['olean']).resolve()).lower() for x in cl['origins']}
for x in o:
 if x['module']=='WeierstrassExtendedCanary':assert Path(x['olean']).resolve()==(P/'WeierstrassExtendedCanary.olean').resolve()
 else:assert old[x['module']]==str(Path(x['olean']).resolve()).lower(),x
assert a['first_conjunction_actual_A3'] and len(a['provider_operands'])==1 and a['provider_operands'][0]['arity']==8
stdout=(P/'imported-v1/stdout.raw').read_text(encoding='utf-8');assert '[propext, Classical.choice, Quot.sound]' in stdout
frozen=P/'scratch-frozen-whole-v2.txt';s=(P/'candidate-v2.lean').read_bytes();assert s.split(b' := by\n',1)[0]+b'\n\nend BanditRL.Tests.OnlineWeierstrassExtendedCanary\n'==frozen.read_bytes()
report=dict(status='ACTUAL_SCRATCH_CANARY_COMPILED_AND_IMPORTED_PENDING_INDEPENDENT_BODY_REVIEW',declaration=a['declaration'],candidate=rec(P/'candidate-v2.lean'),scratch_header=rec(frozen),canonical_header=rec(R/'tmp/online-b4-next-weierstrass-canary-freeze-20261012/canonical-frozen-whole-v2.txt'),scratch_olean=rec(P/'WeierstrassExtendedCanary.olean'),actual_first_conjunction_provider=a['provider_operands'],declaration_origins=a['declaration_origins'],first_conjunction_actual_A3=True,exact_six_closed_facts=True,public_premise_binders=0,implicit_instance_audit_scope='All eight provider Expr operands exported; Real ambient, objective, feasible, hlsc, hcompact and hdom structurally checked. Topological/T2 implicit instance Exprs exported for independent source/type review, not separately asserted against independently elaborated expected instances.',TYPE=dict(count=len(a['TYPE']),constants=a['TYPE'],normalized_stream=rec(P/'TYPE-normalized-v1.txt')),VALUE=dict(count=len(a['VALUE']),constants=a['VALUE'],normalized_stream=rec(P/'VALUE-normalized-v1.txt')),normalizer=dict(method='Anonymous binder names, remove mdata, all remaining Expr structure preserved; no proof irrelevance or equality substitution.',source=rec(P/'ImportedAudit-v1.lean')),axioms=['propext','Classical.choice','Quot.sound'],receipts={n:rec(P/n/'receipt.json') for n in stages},receipt_results={n:{k:rs[n][k] for k in ['actual_exit','integrity_pass']} for n in stages},failure_ledger=['Frozen context V1 header failed dependsOnNoncomputable for constant-bottom objective. Independent context-only correction inserted noncomputable section; all theorem facts/definitions unchanged. Failed receipt/source retained.'],source_proof='Construct global lsc of constant bottom, compact singleton and actual singleton-domain intersection. The first conjunct is the genuine source_weierstrass_extended objective feasible hlsc hcompact hdom result. Other conjuncts expose source premises, bottom value and failure of SourceProper. No finite-value or no-bottom assumption is introduced.',provenance=dict(capture=rec(P/'capture-v2.py'),pins=rec(P/'capture-pins-v2.json'),input_manifest=rec(P/'closure-manifest-v1.json'),actual_origins=rec(P/'imported-origins-v1.json'),actual_module_count=len(o),input_superset_modules=len(cl['origins']),input_superset_files=len(cl['inputs']),actual_module_origins_reconciled=True,runtime_members=19,runtime_before_after_membership_and_hashes=True,source_lib_IR_companion_before_after_membership_and_hashes=True,scope='Current df2 canary captures; inherited A3 core remains its separately reported historical fixed-list runtime scope. OS loader/system DLLs outside portable seal.'),boundary='Experimental scratch only. Independent canary BODY/source acceptance remains pending. No canonical install, Theorem6.9 execution, full B4/chapter completion or live claim.')
put('compiled-canary-report-v1.json',report)
print(json.dumps(dict(report=rec(P/'compiled-canary-report-v1.json'),TYPE=len(a['TYPE']),VALUE=len(a['VALUE']),origins=len(o))))
