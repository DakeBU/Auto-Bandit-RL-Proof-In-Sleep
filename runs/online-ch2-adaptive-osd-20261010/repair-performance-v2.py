from common import *
import ast
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
public=ROOT/'Tests/OnlineAdaptiveOSDCanary.lean'
failed=RUN/'algorithm-canary-performance_canary-body-attempt-v1.lean.txt'
assert public.read_bytes()==failed.read_bytes()
headers=load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']
old='''  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [he, hn] using hp
  · simpa [he] using hs
  · simpa [he] using hb.1
  · simpa [he] using hb.2
'''
new='''  rw [he, hn] at hp
  rw [he] at hs hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num at hp
    exact hp
  · norm_num at hs
    exact hs
  · convert hb.1 using 1 <;> norm_num
  · convert hb.2 using 1 <;> norm_num
'''
assert public.read_text(encoding='utf8').count(old)==1
write(RUN/'algorithm-canary-performance-repair-route-v2.json',dict(classification='simp normalized half before matching local energy equality; explicit rewrite before arithmetic normalization',failed_snapshot=rows([failed]),failure_receipt=rows([RUN/'algorithm-canary-performance_canary-focused-build-v1.json']),scope='performance BODY only; exact headers unchanged; retain named parent occurrences'))
public.write_bytes(public.read_bytes().replace(old.encode(),new.encode()))
assert statement_hash(lean_declaration_header(public,'performance_canary'))==headers['performance_canary']['normalized_statement_hash']
write(RUN/'algorithm-canary-performance_canary-body-attempt-v2.lean.txt',public.read_bytes())
code,out=capture('algorithm-canary-performance_canary-focused-build-v2','lake','build','Tests.OnlineAdaptiveOSDCanary',required=False)
print(out[-6500:],flush=True)
if code: sys.exit(code)
write(RUN/'algorithm-canary-performance_canary-compiled-local-v2.json',dict(production_sha256=sha(public),header=headers['performance_canary'],boundary='focused only'))
