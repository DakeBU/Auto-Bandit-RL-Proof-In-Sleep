from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN/'all-exact-types-v4-exit.json')['exit_code']==0
assert load(RUN/'compiled-value-graph-v2-exit.json')['exit_code']==0
graph=load(RUN/'compiled-value-graph-v2.json')
assert len(graph['nodes'])==53 and all(x['has_value'] for x in graph['nodes'])
assert sum(x['kind']=='definition' for x in graph['nodes'])==9
assert sum(x['kind']=='theorem' for x in graph['nodes'])==44
for short in ['coinLaw_probability','iidLaw_probability']:
    node=next(x for x in graph['nodes'] if x['name']=='Tests.OnlineGuessingIIDBenchmark.'+short)
    assert node['kind']=='theorem'
write(RUN/'compiled-kind-assumption-repair-v5.json',dict(
    actual_compiler_kinds=dict(theorem=44,definition=9),nodes=53,
    incorrect_prior_guess='v3 audit-repair guessed that proof-valued probability instances were definition-kind; actual pinned compiler emits theorem-kind for both.',
    repair='Use actual exported kernel kinds, retaining both full probability proof values and all original53 selected nodes. No public/canary/statement/source revision.',
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),package_accepted=False,chapter_complete=False,goal_complete=False))
actual=load(RUN/'actual-public-canary-headers-v2.json')
axioms=load(RUN/'axiom-bindings-v2.json')['axioms']
template_path=Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean')
source=(RUN/'audit-bodies-v2.py').read_text(encoding='utf8')
exec(compile(source[source.index('required = '):],'audit-bodies-value-resume-v5','exec'))
