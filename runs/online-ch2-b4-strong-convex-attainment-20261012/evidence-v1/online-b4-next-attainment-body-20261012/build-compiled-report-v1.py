from pathlib import Path
import hashlib,json,re,os,subprocess
P=Path(__file__).resolve().parent;R=P.parent.parent
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for x in iter(lambda:f.read(1048576),b''):h.update(x)
 return h.hexdigest()
def bind(p):
 p=Path(p).resolve();return dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def key(p):return os.path.normcase(str(Path(p).resolve()))
def put(n,v):
 with (P/n).open('x',encoding='utf-8',newline='\n') as f:json.dump(v,f,indent=2);f.write('\n')
audit=read(P/'imported-audit-construction-v1.json')
assert audit['declaration']=='BanditRL.OnlineConvex.stronglyConvex_existsUnique_minimizer'
stdout=(P/'imported-v1/stdout.raw').read_text(encoding='utf-8')
matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",stdout)
assert len(matches)==1 and matches[0][0]==audit['declaration']
axioms=[x.strip() for x in matches[0][1].split(',')]
assert set(axioms)=={'propext','Classical.choice','Quot.sound'} and len(axioms)==3
expected={'BanditRL.OnlineConvex.source_weierstrass_extended':8,
 'BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth':19,
 'BanditRL.OnlineConvex.stronglyConvex_minimum_growth':16,
 'BanditRL.OnlineConvex.subgradient_point_finite':8}
providers=audit['provider_operands'];assert len(providers)==4
assert {x['provider']:x['arity'] for x in providers}==expected
assert all(n in audit['VALUE'] for n in expected)
candidate=P/'candidate-v3.lean';raw=candidate.read_bytes()
header=raw.split(b' := by\n',1)[0]+b'\n'
assert header==(P/'scratch-frozen-header-v4.txt').read_bytes()
canonical=header.replace(b'import WeierstrassExtendedCandidate',b'import BanditRLProof.OnlineWeierstrassExtended')
assert hashlib.sha256(canonical).hexdigest()=='58decad0d7dbd318b0c21949d2f699893df9059cb70dfd3fcee020a8ee12b1a5'
origins=read(P/'imported-origins-construction-v1.json');closure=read(P/'closure-manifest-v1.json')
known={x['module']:key(x['olean']) for x in closure['origins']}
known['StrongConvexAttainmentCandidate']=key(P/'StrongConvexAttainmentCandidate.olean')
assert len(origins)==len({x['module'] for x in origins})
for x in origins:assert known[x['module']]==key(x['olean'])
assert 'StrongConvexAttainmentCandidate' in {x['module'] for x in origins}
receipts=[]
for name,exitcode in [('header-v4',0),('focused-v1',1),('focused-v2',1),('focused-v3',0),('imported-v1',0)]:
 path=P/name/'receipt.json';j=read(path)
 assert j['actual_exit']==exitcode and j['integrity_pass'] is True
 assert j['before_RAW']==j['after_RAW'] and j['pre_git']==j['post_git']
 assert j['runtime_before']==j['runtime_after'] and len(j['runtime_before'])==19
 assert j['companion_membership_before']==j['companion_membership_after']
 receipts.append(dict(attempt=name,receipt=bind(path),actual_exit=exitcode,integrity_pass=True,
  start_utc=j['start_utc'],end_utc=j['end_utc'],pre_post_git=j['pre_git'],sealed_input_count=len(j['before_RAW']),
  runtime_count=19,companion_membership_count=len(j['companion_membership_before']),
  stdout=bind(P/name/'stdout.raw'),stderr=bind(P/name/'stderr.raw')))
signature={'source_scope':'Orabona v10 Theorem6.9 printed66/PDF78, dependent on TheoremA.3 printed291/PDF303.',
 'frozen_header_sha256':hashlib.sha256(canonical).hexdigest(),'scratch_header_sha256':hashlib.sha256(header).hexdigest(),
 'actual_public_telescope':audit['header_telescope'],
 'source_assumptions':'Arbitrary original real norm on finite algebraic-coordinate E; SourceProper; SourceClosed; positive curvature on effectiveDomain; nonempty actual global coordinate subdifferential domain. No supplied minimizer, compact domain, coercivity, all-point support or isometry.',
 'genuine_proof_route':['Derive FiniteDimensional from algebraic e.symm. Derive convex effectiveDomain from finite strong-interpolation upper bound.',
 'Transport properness to f composed e.symm; actual global subgradient witness y,g yields y finite through subgradient_point_finite.',
 'Define S={x|f x<=f y}. Original-space coordinate support growth and continuous-dual norm bound imply closed-ball containment with radius2||L||/lam.',
 'SourceClosed closes S; finite-dimensional proper-space compactness yields compact S. Actual A3 supplies p attaining f on S.',
 'Compare outside S against f y to promote p to global minimum. Actual stronglyConvex_minimum_growth at p and positive lam force uniqueness.'],
 'compiled_body_repairs':'V1→V2 explicit unfolding hyS reflexivity; V2→V3 explicit S/D inequality unfolding in hSD. Header and assumptions unchanged.',
 'imported_structural_limits':audit['structural_limits'],
 'actual_source_review_status':'Pending independent SOURCE review; actual compilation and imported provider checks do not grant canonical/chapter acceptance.'}
put('source-proof-signature-v1.json',signature)
report={'status':'EXPERIMENTAL_CORE_ACTUAL_0_IMPORTED_AUDIT_PASSED_SOURCE_REVIEW_PENDING',
 'source_head':'df2ebfc8fb047f95b98801e14e325e65155edaba','candidate':bind(candidate),
 'olean':bind(P/'StrongConvexAttainmentCandidate.olean'),'capture_pins':bind(P/'capture-pins-v4.json'),
 'closure_manifest':bind(P/'closure-manifest-v1.json'),'import_input_manifest':bind(P/'import-input-manifest-v1.json'),
 'probe':bind(P/'ImportedAudit-construction-v1.lean'),'audit':bind(P/'imported-audit-construction-v1.json'),
 'source_proof_signature':bind(P/'source-proof-signature-v1.json'),'receipts':receipts,
 'standard_axioms':axioms,'standard_axioms_enforced':True,
 'whole_expression_exports':{kind:dict(stream=bind(P/(kind+'-normalized-construction-v1.txt')),
  constant_count=len(audit[kind]),constants=audit[kind]) for kind in ['TYPE','VALUE']},
 'provider_applications':providers,'opaque_operands_and_instances':bind(P/'provider-operands-construction-v1.txt'),
 'declaration_origins':audit['declaration_origins'],'all_module_origins':bind(P/'imported-origins-construction-v1.json'),
 'actual_module_count':len(origins),'accepted_discovery_module_count':len(closure['origins']),
 'origin_reconciliation':'Every actual imported origin matches independently sealed discovery map or exact new own scratch candidate olean. No binary relabeling.',
 'normalizer':'Exact previously accepted A3 normalizer: anonymous binders/mdata removal only. Whole stream hashes are normalized Expr hashes, not source hashes.',
 'limitations':audit['structural_limits'],
 'resource_status':'RETURNED immediately after imported-v1 child completion; no remaining Lean processes owned by this actor.',
 'truth_boundary':'Ignored scratch core only. Canary bodies constructed but uncompiled, canonical A3/6.9 installation and combined gates/reader pending. No chapter/fullperformance/global goal acceptance.'}
put('compiled-core-report-v1.json',report)
print(json.dumps({'report':bind(P/'compiled-core-report-v1.json'),'source_signature':bind(P/'source-proof-signature-v1.json'),
 'TYPE_count':len(audit['TYPE']),'VALUE_count':len(audit['VALUE']),'modules':len(origins),'std_axioms':axioms},indent=2))
