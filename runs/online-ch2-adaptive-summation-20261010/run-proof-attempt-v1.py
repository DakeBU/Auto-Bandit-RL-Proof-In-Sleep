from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
assert (CONTRACT/'stabilized-v2.json').is_file() and not PUBLIC.exists()
header=load(CONTRACT/'stabilized-v2.json')['public_headers'][0]
context=(CONTRACT/'definition-context-v2.lean.txt').read_text(encoding='utf8')
body=(RUN/'lemma-body-attempt-v1.txt').read_text(encoding='utf8')
source=context.replace('end BanditRL.OnlineAdaptiveSummation\n',header['exact_header']+' := by\n'+body+'\nend BanditRL.OnlineAdaptiveSummation\n')
write(PUBLIC,source)
assert lifecycle.statement_hash(lifecycle.lean_declaration_header(PUBLIC,header['declaration']))==header['normalized_header_sha256']
write(RUN/'production-attempt-v1.lean.txt',PUBLIC.read_bytes())
code,out=capture('production-focused-build-v1','lake','build','BanditRLProof.OnlineAdaptiveSummation',required=False)
write(RUN/'production-attempt-inspected-v1.json',dict(source=rows([PUBLIC]),snapshot=rows([RUN/'production-attempt-v1.lean.txt']),frozen_statement_unchanged=True,actual_build_exit=code,compiled=code==0,source_semantic_review='pending',candidate_accepted=False,chapter_complete=False))
print(out,flush=True)
fixed()
