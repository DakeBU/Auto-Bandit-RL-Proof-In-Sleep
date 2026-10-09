from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
canary=CONTRACT/'canary-v1'
frozen=load(canary/'stabilized-v1.json')
assert sha(PUBLIC)==frozen['production_sha256']
test=ROOT/'Tests/OnlineAdaptiveSummationCanary.lean'
assert not test.exists()
context=(canary/'definition-context-draft-v1.lean.txt').read_text(encoding='utf8')
bodies=[(RUN/('canary-'+n+'-body-attempt-v1.txt')).read_text(encoding='utf8') for n in ['main','zero']]
decls=[r['exact_header']+' := by\n'+b for r,b in zip(frozen['public_headers'],bodies)]
write(test,context.replace('end Tests.OnlineAdaptiveSummationCanary\n','\n'.join(decls)+'\nend Tests.OnlineAdaptiveSummationCanary\n'))
for r in frozen['public_headers']:
    assert lifecycle.statement_hash(lifecycle.lean_declaration_header(test,r['declaration']))==r['normalized_header_sha256']
write(RUN/'canary-attempt-v1.lean.txt',test.read_bytes())
code,out=capture('canary-focused-build-v1','lake','build','Tests.OnlineAdaptiveSummationCanary',required=False)
write(RUN/'canary-attempt-inspected-v1.json',dict(Test=rows([test]),snapshot=rows([RUN/'canary-attempt-v1.lean.txt']),frozen_statements_unchanged=True,actual_build_exit=code,compiled=code==0,BODY_semantic_review='pending',chapter_complete=False))
print(out,flush=True)
fixed()
