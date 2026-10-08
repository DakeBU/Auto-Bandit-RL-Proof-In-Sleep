from common_reviewed_v2 import *
import re

headers_fixed(7)
assert load(RUN/'actual-canary-types-fixtures-v2-exit.json')['exit_code']==1
source=(RUN/'leaves/actual-canary-types-fixtures-v2.lean').read_text(encoding='utf8')
source,count=re.subn(r'(?m)^def (?:target|xorY|xorTape) [^\n]*\n','',source)
assert count==4
write(RUN/'leaves/actual-canary-types-fixtures-v3.lean',source)
write(RUN/'canary-type-audit-failure-repair-v3.json',dict(
    failed_gate='actual-canary-types-fixtures-v2-exit.json',
    reason='Audit extraction copied adjacent single-line fixture definitions into multiple blocks, redeclaring xorTape.',
    repair='Remove only four accidental adjacent fixture copies from the audit leaf; retain all nine complete Fixture definitions and every identity.',
    public_changed=False,canary_changed=False,statement_changed=False))
gate('actual-canary-types-fixtures-v3','lake','env','lean',RUN/'leaves/actual-canary-types-fixtures-v3.lean')
bindings=load(RUN/'actual-compiled-kind-bindings-v2.json')
actual=load(RUN/'actual-public-canary-headers-v2.json')
axioms=load(RUN/'all-selected-axiom-bindings-v2.json')['axioms']
TEST='Tests.OnlineGuessingRandomizedIID.'
script=(RUN/'audit-actual-canary-types-v2.py').read_text(encoding='utf8')
tail=script[script.index("graph=load(RUN/'compiled-body-value-graph-v2.json')"):]
tail=tail.replace("canary_Prop_identities=29,", "actual_canary_types_gate='actual-canary-types-fixtures-v3-exit.json',canary_Prop_identities=29,")
exec(compile(tail,'canary-type-audit-resume-v3','exec'),globals())
