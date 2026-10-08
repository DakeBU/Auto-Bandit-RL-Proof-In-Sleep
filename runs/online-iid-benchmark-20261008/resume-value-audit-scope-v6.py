from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN/'compiled-kind-assumption-repair-v5.json')['actual_compiler_kinds']==dict(theorem=44,definition=9)
write(RUN/'value-audit-resume-scope-v6.json',dict(actual_v5_failure='NameError TEST in resumed audit helper, after actual exported kinds passed.',
    repair='Restore original TEST prefix and local graph/header/axiom bindings before executing unchanged value/fence tail.',
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),package_accepted=False,chapter_complete=False,goal_complete=False))
TEST='Tests.OnlineGuessingIIDBenchmark.'
actual=load(RUN/'actual-public-canary-headers-v2.json')
axioms=load(RUN/'axiom-bindings-v2.json')['axioms']
graph=load(RUN/'compiled-value-graph-v2.json')
template_path=Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean')
source=(RUN/'audit-bodies-v2.py').read_text(encoding='utf8')
exec(compile(source[source.index('required = '):],'audit-bodies-unchanged-tail-resume-v6','exec'))
