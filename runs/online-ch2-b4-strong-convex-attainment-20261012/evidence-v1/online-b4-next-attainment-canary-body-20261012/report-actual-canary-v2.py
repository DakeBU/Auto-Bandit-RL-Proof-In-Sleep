from pathlib import Path
import json,hashlib,re,datetime
P=Path(__file__).resolve().parent;R=P.parent.parent

def bind(p):
 p=p.resolve();h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def put(p,v):
 with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(v,f,indent=2,ensure_ascii=False);f.write('\n')
receipts={n:read(P/n/'receipt.json') for n in ['header-v3','focused-v1','focused-v2','focused-v3','imported-v2']}
for n in ['header-v3','focused-v3','imported-v2']:
 assert receipts[n]['actual_exit']==0 and receipts[n]['integrity_pass'] is True
for n in ['focused-v1','focused-v2']:assert receipts[n]['actual_exit']==1 and receipts[n]['integrity_pass'] is True
src=(P/'scratch-candidate-v3.lean').read_bytes();frozen=(P/'scratch-frozen-whole-v1.txt').read_bytes()
sp=re.split(rb'(?m)^theorem ',src);fp=re.split(rb'(?m)^theorem ',frozen)
ending=b'\nend BanditRL.Tests.OnlineStrongConvexAttainmentCanary\n'
assert len(sp)==len(fp)==3 and sp[0]==fp[0] and src.endswith(ending)
for i in [1,2]:assert sp[i].split(b' := by\n',1)[0]==(fp[i] if i==1 else fp[i][:-len(ending)]).rstrip(b'\n')
canonical=frozen.replace(b'import StrongConvexAttainmentCandidate\n',b'import BanditRLProof.OnlineStrongConvexAttainment\n',1)
assert canonical==(P.parent/'online-b4-next-attainment-canary-freeze-20261012/canonical-frozen-whole-v1.txt').read_bytes()
audit=read(P/'imported-audit-v1.json');origins=read(P/'imported-origins-v1.json');cl=read(P/'closure-manifest-v3.json')
assert len(audit['rows'])==2
std={};out=(P/'imported-v2/stdout.raw').read_text(encoding='utf-8')
for row in audit['rows']:
 name=row['declaration'];m=re.search(re.escape("'"+name+"'")+r'.*?\[(.*?)\]',out,re.S);assert m,name
 axioms=[x.strip() for x in m.group(1).split(',')];assert set(axioms)=={'propext','Classical.choice','Quot.sound'} and len(axioms)==3;std[name]=axioms
expected={x['module']:str(Path(x['olean']).resolve()).lower() for x in cl['origins']};expected['StrongConvexAttainmentCanaries']=str((P/'StrongConvexAttainmentCanaries.olean').resolve()).lower()
actual={x['module']:str(Path(x['olean']).resolve()).lower() for x in origins};assert len(actual)==len(origins) and actual==expected
for n,r in receipts.items():
 assert r['before_RAW']==r['after_RAW'] and r['pre_git']==r['post_git']
 assert r['runtime_before']==r['runtime_after'] and len(r['runtime_before'])==19
 assert r['companion_membership_before']==r['companion_membership_after']
streamrows=[]
for row,label in zip(audit['rows'],['positive','zero'],strict=True):
 for kind in ['TYPE','VALUE']:streamrows.append(dict(declaration=row['declaration'],kind=kind,stream=bind(P/f'{label}-{kind}-normalized-v1.txt'),constant_count=len(row[kind])))
proof=dict(status='ACTUAL_COMPILED_SCRATCH_AWAITING_INDEPENDENT_SOURCE_REVIEW',positive=dict(first_conj='hattainment: actual stronglyConvex_existsUnique_minimizer call',proper='Globally no bottom; finite point0 value2',closed='Real cuts intersection of closed halfline and continuous quadratic cuts',curvature='Lambda1 exact one-dimensional squared-norm identity',global_support='Point(-2) at nonminimizer point0; quadratic residual y0²/2 >=0; top outside',identification='Unique minimum identified as point2; domain unbounded halfline'),zero=dict(proper=True,closed=True,curvature=0,global_support='Point1 at point0',no_minimum='For any p use point(p0-1)',target_call=False),limitations=audit['limitations'],boundaries='No canonical installation, combined gates, reader acceptance, full B4/performance/chapter completion.')
put(P/'source-proof-signature-v2.json',proof)
report=dict(status='ACTUAL_0_IMPORTED_CANARIES_AWAITING_INDEPENDENT_SOURCE_REVIEW',head=receipts['imported-v2']['post_git'],source=bind(P/'scratch-candidate-v3.lean'),olean=bind(P/'StrongConvexAttainmentCanaries.olean'),frozen=dict(scratch=bind(P/'scratch-frozen-whole-v1.txt'),canonical=bind(P.parent/'online-b4-next-attainment-canary-freeze-20261012/canonical-frozen-whole-v1.txt'),raw_context_and_headers_exact=True,sole_import_transport='BanditRLProof.OnlineStrongConvexAttainment -> StrongConvexAttainmentCandidate'),receipts={n:dict(file=bind(P/n/'receipt.json'),actual_exit=r['actual_exit'],integrity_pass=r['integrity_pass'],input_count=len(r['before_RAW']),module_families=len(r['companion_membership_before']),runtime_members=19,stdout=r['stdout'],stderr=r['stderr']) for n,r in receipts.items()},probe=bind(P/'ImportedAudit-construction-v2.lean'),manifest=bind(P/'import-input-manifest-v2.json'),audit_file=bind(P/'imported-audit-v1.json'),origin_file=bind(P/'imported-origins-v1.json'),module_count=len(origins),origins_exactly_closure_plus_own=True,standard_axioms=std,streams=streamrows,normalizer='Exact reviewed binder-name/mdata-only recursive normalization. No reduction or proof-irrelevance/equality substitution.',provider_operands=audit['provider_operands'],first_conjunction_actual_parent=audit['first_conjunction_actual_parent'],zero_case_no_parent_call=audit['zero_case_no_parent_call'],declaration_origins=audit['declaration_origins'],provider_raw_export=bind(P/'provider-operands-v1.txt'),source_proof=bind(P/'source-proof-signature-v2.json'),limitations=audit['limitations'],history=dict(V2_prechild_interruption=bind(P/'header-v1-interruption-record-v1.json'),failed_import=bind(P/'imported-v1/receipt.json'),partial_report=bind(P/'compiled-canary-partial-report-v1.json'),current_import_pins=bind(P/'capture-pins-import-v4.json'),current_import_capture=bind(P/'capture-import-v4.py'),failed_candidates=[bind(P/f'scratch-candidate-v{i}.lean') for i in [1,2]],failed_attempts='focused-v1 and focused-v2 retain actual1; no failed proof overwritten'),boundaries=proof['boundaries'])
put(P/'compiled-canary-report-v2.json',report)
print(json.dumps(bind(P/'compiled-canary-report-v2.json')))
