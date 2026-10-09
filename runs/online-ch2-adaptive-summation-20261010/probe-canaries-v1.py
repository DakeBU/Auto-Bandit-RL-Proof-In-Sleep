from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
canary=CONTRACT/'canary-v1';test=ROOT/'Tests/OnlineAdaptiveSummationCanary.lean'
frozen=load(canary/'stabilized-v1.json')
assert sha(PUBLIC)==frozen['production_sha256'] and load(RUN/'canary-focused-build-v3.json')['actual_exit']==0
headers=frozen['public_headers']
probe='import Tests.OnlineAdaptiveSummationCanary\n\nopen Set Finset MeasureTheory\n\n'
for r in headers:
    assert lifecycle.statement_hash(lifecycle.lean_declaration_header(test,r['declaration']))==r['normalized_header_sha256']
    probe+='#check '+r['declaration']+'\nexample : ('+r['exact_header'].split(' :\n',1)[1]+') := '+r['declaration']+'\n#print axioms '+r['declaration']+'\n'
write(RUN/'CanaryPublicProbeV1.lean',probe)
capture('canary-full-public-axioms-v1','lake','env','lean',RUN/'CanaryPublicProbeV1.lean')
for i,r in enumerate(headers,1):
    fence=RUN/'fences'/('canary-'+str(i)+'-v1.json')
    capture('canary-statement-fence-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',r['declaration'],'--file',test,'--output',fence)
    assert load(fence)['statement_hash']==r['normalized_header_sha256']
    _,out=capture('canary-safe-verify-'+str(i)+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',fence,'--lean-file',test)
    assert json.loads(out)['ok']
capture('canary-named-retrieval-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','list-lean-decls','OnlineAdaptiveSummationCanary','--statement')
capture('canary-compiled-conjunct-VALUE-export-v1','lake','env','lean','--run',RUN/'ExportCanaryConjunctValuesV1.lean',RUN/'canary-compiled-conjunct-VALUE-v1.json')
d=load(RUN/'canary-compiled-conjunct-VALUE-v1.json')
assert len(d['nodes'])==3 and len(d['selected_conjuncts'])==3 and all(r['required_present'] for r in d['selected_conjuncts'])
write(RUN/'canary-focused-gates-inspected-v1.json',dict(production=rows([PUBLIC]),Test=rows([test]),full_canary_public_terminals=2,selected_public_reuse_conjuncts=3,frozen_headers_context_unchanged=True,actual_compiled_BODY=True,compiled_values=rows([RUN/'canary-compiled-conjunct-VALUE-v1.json']),semantic_BODY_review='pending',package_accepted=False,chapter_complete=False,whole_Goal='active'))
fixed()
