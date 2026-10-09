from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
header=load(CONTRACT/'frozen-headers-draft-v2.json')['rows'][0]
assert lifecycle.statement_hash(lifecycle.lean_declaration_header(PUBLIC,header['declaration']))==header['normalized_header_sha256']
assert load(RUN/'production-focused-build-v1.json')['actual_exit']==0
write(RUN/'ProductionPublicProbeV1.lean','import BanditRLProof.OnlineAdaptiveSummation\n\nopen Set Finset MeasureTheory\n\n#check '+header['declaration']+'\nexample : '+header['exact_Prop']+' := '+header['declaration']+'\n#print axioms '+header['declaration']+'\n#print '+header['declaration']+'\n')
capture('production-public-value-axioms-v1','lake','env','lean',RUN/'ProductionPublicProbeV1.lean')
capture('production-named-retrieval-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','list-lean-decls','OnlineAdaptiveSummation','--statement')
fence=RUN/'fences/lemma-4-13-v2.json'
capture('production-statement-fence-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',header['declaration'],'--file',PUBLIC,'--output',fence)
assert load(fence)['statement_hash']==header['normalized_header_sha256']
_,out=capture('production-safe-verify-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',fence,'--lean-file',PUBLIC)
assert json.loads(out)['ok']
canary=CONTRACT/'canary-v1'
context=(canary/'definition-context-draft-v1.lean.txt').read_text(encoding='utf8')
props=[r['exact_header'].split(' :\n',1)[1] for r in load(canary/'frozen-headers-draft-v1.json')['rows']]
write(RUN/'CanaryFullContextTypeProbeV1.lean',context.replace('end Tests.OnlineAdaptiveSummationCanary\n','\n'.join('#check ('+p+')' for p in props)+'\nend Tests.OnlineAdaptiveSummationCanary\n'))
capture('canary-full-context-type-probe-v1','lake','env','lean',RUN/'CanaryFullContextTypeProbeV1.lean')
write(RUN/'production-focused-gates-inspected-v1.json',dict(production=rows([PUBLIC]),frozen_header_sha256=header['normalized_header_sha256'],actual_compiled_BODY=True,full_public_application=True,native_fence_and_token_scan=True,canary_Prop_full_context_typechecked=True,canary_BODY='unwritten',source_BODY_review='pending',candidate_accepted=False,chapter_complete=False,whole_Goal='active'))
fixed()
