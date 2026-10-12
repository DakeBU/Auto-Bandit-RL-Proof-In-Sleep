from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parent.parent
def rec(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
def read(n):return json.loads((P/n).read_text(encoding='utf-8'))
def put(n,x):
 with (P/n).open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n')
rr={n:read(n+'/receipt.json') for n in ['header-v1','header-v2','focused-v1','focused-v2','imported-v1']}
for n in ['header-v2','focused-v2','imported-v1']:assert rr[n]['actual_exit']==0 and rr[n]['integrity_pass']
a=read('imported-audit-v3.json');o=read('imported-origins-v3.json');cl=read('closure-manifest-v1.json')
origins={x['module']:str(Path(x['olean']).resolve()).lower() for x in cl['origins']}
extra=[]
for x in o:
 if x['module']=='WeierstrassExtendedCandidate':assert Path(x['olean']).resolve()==(P/'WeierstrassExtendedCandidate.olean').resolve()
 else:
  assert x['module'] in origins,x
  assert str(Path(x['olean']).resolve()).lower()==origins[x['module']],x
assert len({x['module'] for x in o})==len(o)
rows=a['provider_applications_including_partial'];full=max(rows,key=lambda x:x['arity'])
assert sum(x['arity']==full['arity'] for x in rows)==1
binders=[x['binder'] for x in full['operands']]
for n in ['X','f','V','hnonempty','hV']:assert n in binders,(n,binders)
lsc=[x for x in full['operands'] if x['head_constant']=='LowerSemicontinuous.lowerSemicontinuousOn']
assert len(lsc)==1 and 'hf' in lsc[0]['used_binders'] and 'V' in lsc[0]['used_binders']
frozen=R/'tmp/online-b4-next-attainment-header-freeze-20261012/A3-frozen-context-and-header-v1.txt'
assert (P/'candidate-v2.lean').read_bytes().split(b' := by\n',1)[0]+b'\n'==frozen.read_bytes()
stdout=(P/'imported-v1/stdout.raw').read_text(encoding='utf-8')
assert '[propext, Classical.choice, Quot.sound]' in stdout
report=dict(status='ACTUAL_SCRATCH_COMPILED_AND_IMPORTED_NOT_INDEPENDENT_BODY_ACCEPTANCE',declaration=a['declaration'],source=rec(P/'candidate-v2.lean'),frozen_header=rec(frozen),scratch_olean=rec(P/'WeierstrassExtendedCandidate.olean'),receipts={n:rec(P/n/'receipt.json') for n in rr},receipt_status={n:{k:rr[n][k] for k in ['actual_exit','integrity_pass']} for n in rr},failure_ledger=['focused-v1 actual1: LowerSemicontinuous.lowerSemicontinuousOn requires explicit V. Candidate-v2 changes this BODY application only.','header-v1 actual0 had compiler executable but no separately inventoried runtime DLLs; superseded by authoritative expanded-runtime header-v2.','ImportedAudit-v1/v2 were unexecuted constructions; v3 adds scoped binder exports and safe head-constant lookup.'],proof_spine='Actual intersection witness supplies V.Nonempty; actual hf.lowerSemicontinuousOn V and hV feed Mathlib LowerSemicontinuousOn.exists_isMinOn. Exact source T2/global lsc/domain-intersection premises retained although general Mathlib theorem is stronger. No no-bottom or SourceProper premise.',TYPE=dict(count=len(a['TYPE']),constants=a['TYPE'],normalized_stream=rec(P/'TYPE-normalized-v1.txt')),VALUE=dict(count=len(a['VALUE']),constants=a['VALUE'],normalized_stream=rec(P/'VALUE-normalized-v1.txt')),provider=dict(name='LowerSemicontinuousOn.exists_isMinOn',full_application_count=1,arity=full['arity'],actual_operands=full['operands'],direct_f_V_nonempty_compact_verified=True,actual_global_lsc_restricted_to_V_verified=True),standard_axioms=['propext','Classical.choice','Quot.sound'],normalizer=dict(method=a['normalization'],source=rec(P/'ImportedAudit-v3.lean'),proof_irrelevance_or_equality_substitution=False),provenance=dict(capture=rec(P/'capture-v2.py'),pins=rec(P/'capture-pins-v2.json'),closure=rec(P/'closure-manifest-v1.json'),sealed_superset_modules=len(cl['origins']),sealed_superset_files=len(cl['inputs']),actual_imported_modules=len(o),actual_origins=rec(P/'imported-origins-v3.json'),actual_origins_match_sealed_superset_plus_own_scratch=True,companion_enumeration=rec(P/'companion-presence-audit-v1.json'),runtime_scope='All toolchain bin files and bundled Python root DLLs separately pinned in expanded captures; OS runtime trust external.',scope='Conservative prior compiler-derived superset refreshed at606; actual current imported compiler origins reconciled into it. Full before/after RAW equality; no historical fresh-compilation provenance claim for existing imported dependencies.'),boundary='Experimental scratch only. No canonical installation, canary execution, Theorem6.9 BODY, full B4/chapter acceptance or goal closure. Separate independent source BODY acceptance remains required.')
put('compiled-core-report-v1.json',report)
print(json.dumps(dict(report=rec(P/'compiled-core-report-v1.json'),TYPE=len(a['TYPE']),VALUE=len(a['VALUE']),provider_arity=full['arity'],actual_modules=len(o))))
