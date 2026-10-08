from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN/'all-exact-types-v3-exit.json')['exit_code']==1
old=(RUN/'leaves'/'all-exact-types-v3.lean').read_text(encoding='utf8')
lines=old.splitlines()
imports=[line for line in lines if line.startswith('import ')]
rest=[line for line in lines if not line.startswith('import ')]
write(RUN/'leaves'/'all-exact-types-v4.lean','\n'.join(imports+['']+rest))
write(RUN/'type-import-order-repair-v4.json',dict(obstruction='Restored scoped commands preceded retained imports.',
    repair='Move all retained imports to the file start; no statement, proof, mathematical context or universe restriction.',
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),package_accepted=False,chapter_complete=False,goal_complete=False))
gate('all-exact-types-v4','lake','env','lean',RUN/'leaves'/'all-exact-types-v4.lean')
actual=load(RUN/'actual-public-canary-headers-v2.json')
names=load(RUN/'axiom-bindings-v2.json')['names']
axioms=load(RUN/'axiom-bindings-v2.json')['axioms']
source=(RUN/'repair-type-audit-scopes-v3.py').read_text(encoding='utf8')
exec(compile(source[source.index("source=(RUN/"):],'audit-type-v3-resume-v4','exec'))
