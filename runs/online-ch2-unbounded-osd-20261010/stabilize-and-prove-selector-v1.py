from common import *
fixed()
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
receipt=RUN/'contract-source-review-v1.json';r=load(receipt)
assert sha(receipt)=='5e236b777c3d14065461c2ef72d631c12355b070d8e52c3187552d09e26bb010'
assert r['CONTRACT_verdict']=='accepted-with-explicit-delta' and r['first_leaf_verdict']=='accepted' and not r['required_repairs']
assert sha(r['report'])==r['report_sha256']=='4e616f8a5908b706c3d4bbffb9593a5d729ca1ba0327a31c115151a5f463f28a'
assert sha(r['input_manifest'])==r['input_manifest_sha256']
for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
h=load(CONTRACT/'headers-draft-v1.json');assert len(h['targets'])==11
assert load(RUN/'draft-type-probe-v2.json')['actual_exit']==0
for row in h['targets']:
    assert hashlib.sha256((row['header']+'\n').encode('utf8')).hexdigest()==row['raw_header_sha256']
    fence=lifecycle.make_statement_fence(declaration=row['name'],file=PUBLIC.relative_to(ROOT).as_posix(),statement=row['header'])
    write(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'),dict(**fence,scoped_context=row['context'],raw_header_sha256=row['raw_header_sha256'],header_origin='Exact independently reviewed pre-body draft; native source extraction follows each real declaration'))
assert (CONTRACT/'definitions-draft-v1.lean').read_bytes()==(h['prefix']+h['definitions']).encode('utf8')
write(CONTRACT/'definitions-frozen-v1.json',dict(file=(CONTRACT/'definitions-draft-v1.lean').as_posix(),sha256=sha(CONTRACT/'definitions-draft-v1.lean'),raw_base64=base64.b64encode((CONTRACT/'definitions-draft-v1.lean').read_bytes()).decode('ascii'),names=['powerSteps','phi','switchSlope','switchLoss'],scope='Four complete definition bodies, imports and scoped context frozen. Same actual OSD borrowed; no duplicated algorithm.'))
write(CONTRACT/'stabilized-v1.json',dict(task=TASK,status='stabilized',source_sha256=PDF_SHA,source_card=rows([CONTRACT/'source-card-draft-v1.json']),targets=h['targets'],definitions=rows([CONTRACT/'definitions-draft-v1.lean',CONTRACT/'definitions-frozen-v1.json']),source_review=rows([receipt,Path(r['report'])]),neutral_review=rows([RUN/'blind-reconstruction-v1.md',RUN/'blind-reconstruction-v1.json']),conversion_window=rows([ROOT/'conversion-windows'/(TASK+'.md'),RUN/'native-conversion-template-RAW-v1.json']),DAG=rows([CONTRACT/'dependency-DAG-draft-v1.json']),allowed_proof_scope='New production module only, finite dependency-ready leaves; own task evidence. Roots/Tests/readers/global registry unchanged. Test canary types/bodies require later exact review/freeze.',source_terminal='One Theorem5.4 plus explicitphi range/limit; 11 Lean leaves not source/chapter denominator',chapter_complete=False,chapter_total=None,whole_Goal='ACTIVE'))
def snap(label):
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps],provenance='Contemporaneous exact RAW before scoped native mutation'))
snap('native-stabilized-exact-before-v1')
event('native-stabilized-event-v1','stabilized',dict(task=TASK,terminal_count=11,definitions=4,contract_sha256=sha(CONTRACT/'stabilized-v1.json'),source_review_sha256=sha(receipt),source_result_closed=False,chapter_complete=False))
snap('native-proving-selector-exact-before-v1')
leaf=h['targets'][0]
event('native-proving-selector-v1','proving',dict(task=TASK,leaf=leaf['name'],allowed_file=PUBLIC.relative_to(ROOT).as_posix(),dependencies=leaf['parents'],frozen_statement_hash=load(CONTRACT/'frozen-currentSubgradient_affine-v1.json')['statement_hash'],full_source_lower_bound='required/open'))
assert not PUBLIC.exists()
body='''  classical
  have hs : (BanditRL.OnlineConvex.SourceSubdifferential
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x).Nonempty := by
    rw [BanditRL.OnlineConvex.affine_subdifferential a b x]
    exact Set.singleton_nonempty a
  unfold BanditRL.OnlineSubgradientDescent.currentSubgradient
  rw [dif_pos hs]
  have hc := Classical.choose_spec hs
  rw [BanditRL.OnlineConvex.affine_subdifferential a b x] at hc
  exact Set.mem_singleton_iff.mp hc
'''
text=h['prefix']+h['definitions']+'''\n/-!
Required Chapter2 unbounded varying-step OSD failure dependency, Orabona v10
Theorem5.4 printed52-53/PDF64-65. Four source witness definitions and eleven
terminal contracts are frozen before lowering. This actual selector producer is
only the first dependency-ready leaf; the complete lower bound/phi range/limit,
canaries, combined project and publication gates remain open. No chapter closure.
-/\n'''+leaf['context']+'\n'+leaf['header']+' := by\n'+body+'\nend BanditRL.OnlineUnboundedOSD\n'
write(PUBLIC,text)
write(RUN/'selector-attempt-source-v1.lean',PUBLIC.read_bytes())
code,out=capture('selector-focused-build-v1','lake','build','BanditRLProof.OnlineUnboundedOSD',required=False)
write(RUN/'selector-focused-inspected-v1.json',dict(actual_exit=code,actual_stdout=out,build_completed_marker='Build completed successfully' in out,source=rows([PUBLIC]),leaf=leaf['name'],status='compiled focused leaf only' if code==0 and 'Build completed successfully' in out else 'failed/unconfirmed',other_frozen_terminals_open=10,source_lower_bound_closed=False,chapter_complete=False))
assert code==0 and 'Build completed successfully' in out
capture('selector-native-fence-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',leaf['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/'selector-native-extracted-v1.json')
native=load(CONTRACT/'selector-native-extracted-v1.json');frozen=load(CONTRACT/'frozen-currentSubgradient_affine-v1.json')
assert native['statement_hash']==frozen['statement_hash']
write(RUN/'selector-fence-compared-v1.json',dict(actual_native_hash=native['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True,definitions_prefix_exact=PUBLIC.read_bytes().startswith((CONTRACT/'definitions-draft-v1.lean').read_bytes()),other_frozen_terminals_open=10))
write(RUN/'SelectorPublicAuditV1.lean','''import BanditRLProof.OnlineUnboundedOSD
#check BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
#check (BanditRL.OnlineUnboundedOSD.currentSubgradient_affine (3 : ℝ) 2 7)
#print axioms BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
''')
capture('selector-public-axiom-v1','lake','env','lean',RUN/'SelectorPublicAuditV1.lean')
fixed()
print('Exact first actual-selector proof compiled and frozen header matched; remaining10/source lower bound still open.')
