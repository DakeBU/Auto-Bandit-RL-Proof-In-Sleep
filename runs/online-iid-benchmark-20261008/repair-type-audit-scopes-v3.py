from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'all-exact-types-v2-exit.json')['exit_code'] == 1
old = (RUN / 'leaves' / 'all-exact-types-v2.lean').read_text(encoding='utf8')
new = old.replace('import Tests.OnlineGuessingIIDBenchmarkCanary\n',
    'import Tests.OnlineGuessingIIDBenchmarkCanary\nopen MeasureTheory ProbabilityTheory\nopen scoped ENNReal\nnoncomputable section\n',1)
write(RUN / 'leaves' / 'all-exact-types-v3.lean',new)
write(RUN / 'type-audit-scopes-repair-v3.json',dict(
    obstruction='Removing the draft inlined definitions also removed its open namespace context; canary notation scope and noncomputable clone context must be explicit.',
    repair='Restore only scoped context in the new audit file, retaining all eight exact arbitrary-universe Props,28 actual canary types,nine complete definitions.',
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),math_source_headers_unchanged=True,
    compiler_kind_note='Lean probability instances use definition constants; nine object definitions plus two proof-valued instances are eleven definition-kind nodes, distinct from42 theorem-kind nodes.',
    package_accepted=False,chapter_complete=False,goal_complete=False))
gate('all-exact-types-v3','lake','env','lean', RUN/'leaves'/'all-exact-types-v3.lean')
actual=load(RUN/'actual-public-canary-headers-v2.json')
names=load(RUN/'axiom-bindings-v2.json')['names']
axioms=load(RUN/'axiom-bindings-v2.json')['axioms']
source=(RUN/'audit-bodies-v2.py').read_text(encoding='utf8')
tail=source[source.index("template_path = Path("):]
tail=tail.replace("sum(x['kind']=='definition' for x in graph['nodes']) == 9",
    "sum(x['kind']=='definition' for x in graph['nodes']) == 11\nassert sum(x['kind']=='theorem' for x in graph['nodes']) == 42")
exec(compile(tail,'audit-bodies-v2-scope-resume-v3','exec'))
