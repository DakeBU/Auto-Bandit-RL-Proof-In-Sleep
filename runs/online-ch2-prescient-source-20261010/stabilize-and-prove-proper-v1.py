from common import *
fixed()
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
review=load(RUN/'contract-source-review-v1.json')
assert review['CONTRACT_verdict']=='accepted-with-explicit-delta'
assert review['canary_v2_verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
assert sha(RUN/'contract-source-review-v1.md')==review['report_sha256']
assert load(RUN/'draft-type-probe-inspected-v3.json')['actual_exit']==0
assert load(RUN/'canary-type-probe-v2.json')['actual_exit']==0
headers=load(CONTRACT/'headers-draft-v2.json')
canaries=load(CONTRACT/'canary-headers-draft-v2.json')
for row in headers['targets']:
    assert hashlib.sha256((row['header']+'\n').encode('utf8')).hexdigest()==row['sha256']
    fence=lifecycle.make_statement_fence(declaration=row['name'],file=PUBLIC.relative_to(ROOT).as_posix(),statement=row['header'])
    write(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'),dict(**fence,header_origin='Reviewed exact draft header; lifecycle make_statement_fence API before body. Actual CLI source extraction checked after each real declaration exists.',scoped_context=row['context'],raw_header_sha256=row['sha256']))
write(CONTRACT/'stabilized-v1.json',dict(task=TASK,status='stabilized',source_fingerprint=PDF_SHA,statement_manifest=rows([CONTRACT/'headers-draft-v2.json']),canary_manifest=rows([CONTRACT/'canary-headers-draft-v2.json']),six_targets=headers['targets'],review=rows([RUN/'contract-source-review-v1.md',RUN/'contract-source-review-v1.json',RUN/'blind-reconstruction-v1.md',RUN/'blind-reconstruction-v1.json']),conversion_window=rows([ROOT/'conversion-windows'/(TASK+'.md'),RUN/'native-conversion-window-exact-before-v1.json']),DAG=rows([CONTRACT/'dependency-DAG-draft-v1.json']),proof_scope='Only new production module and new task evidence; six terminal headers/scoped contexts fixed. No old root/registry/publication changes. First ready proper leaf, then strict/unique/identity/endpoints.',chapter_status='incomplete; eight forwards remain open; whole Goal active'))
def native_before(label):
    paths=[RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'own-artifact-journal.md',RUN/'trials.jsonl']
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.relative_to(ROOT).as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in paths],provenance='Contemporaneous before actual native event.'))
native_before('native-stabilized-exact-before-v1')
event('native-stabilized-event-v1','stabilized',dict(task=TASK,contract='docs/contracts/online-ch2-prescient-source-v1/stabilized-v1.json',terminal_count=6,semantic_review=review['CONTRACT_verdict'],canary_review=review['canary_v2_verdict']))
native_before('native-proving-proper-exact-before-v1')
event('native-proving-proper-v1','proving',dict(task=TASK,leaf='BanditRL.OnlineConvex.sourceProper_of_domain',allowed_file=PUBLIC.relative_to(ROOT).as_posix(),dependencies=['EReal.coe_toReal'],terminal_count=6,unresolved=6))
assert not PUBLIC.exists()
body='''  refine ⟨hbot, ?_⟩
  obtain ⟨z, hz⟩ := hV
  exact ⟨z, (f z).toReal, (EReal.coe_toReal (ne_of_lt (hdom hz)) (hbot z)).symm⟩
'''
prefix='''import BanditRLProof.OnlinePrescientBregmanRegret

/-!
Source-domain/properness and unique-update transports for the required Chapter2
prescient forward dependency in Orabona v10, Algorithm15.8/Theorem15.30.
The source guarantee concerns valid interior argmin runs. Closedness and strict
convexity are not universal attainment assumptions; the existing exponential
counterexample and Option failure boundary remain in force. Source wrappers
retain literal finite-dimensional/closedness premises. The same shared loss,
divergence, selector and recursion are reused. No new per-Book project.
See docs/contracts/online-ch2-prescient-source-v1/stabilized-v1.json.
-/

noncomputable section
open Set Finset
open BanditRL.OnlineBregman
set_option autoImplicit false

'''
row=headers['targets'][0]
text=prefix+row['context']+'\n'+row['header']+' := by\n'+body+'\nend BanditRL.OnlineConvex\n'
write(PUBLIC,text)
write(RUN/'proper-attempt-source-v1.lean',PUBLIC.read_bytes())
code,out=capture('proper-focused-build-v1','lake','build','BanditRLProof.OnlinePrescientBregmanSource',required=False)
write(RUN/'proper-focused-inspected-v1.json',dict(actual_exit=code,actual_stdout=out,source=rows([PUBLIC]),terminal='BanditRL.OnlineConvex.sourceProper_of_domain',inference='Only exact first leaf body compiled if actual build output confirms; other five terminals open.'))
assert code==0
capture('proper-native-fence-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/'proper-native-extracted-v1.json')
actual=load(CONTRACT/'proper-native-extracted-v1.json')
frozen=load(CONTRACT/'frozen-sourceProper_of_domain-v1.json')
assert actual['statement_hash']==frozen['statement_hash']
write(RUN/'proper-fence-compared-v1.json',dict(actual_native_hash=actual['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True,other_targets_open=5))
fixed()
