from common import *
import ast,re
prior=load(RUN/'delivery-scripts-prepared-20261011-v2.json')
paths=[]
for row in prior['scripts']:
    p=Path(row['path']);assert sha(p)==row['sha256']
    s=p.read_text(encoding='utf8')
    name=p.name.replace('_v2.py','_v3.py').replace('-v2.py','-v3.py')
    s=s.replace('from delivery_guard_20261011_v2 import *','from delivery_guard_20261011_v3 import *')
    if p.name.startswith('delivery_guard'):
        s=s.replace("CONFIG=load(RUN/'delivery-preparation-config-20261011-v1.json')", "assert sha(RUN/'common.py')=='"+sha(RUN/'common.py')+"','Imported common.py changed'\nCONFIG=load(RUN/'delivery-preparation-config-20261011-v1.json')")
        s=s.replace("('tools','.py'),('website/scripts','.py')", "('tools','.py'),('tools','.lean'),('website/scripts','.py')")
        s=s.replace("def same_binding(binding):\n    for row in binding: assert sha(row['path'])==row['sha256'],row['path']", "def same_binding(binding):\n    assert source_binding()==binding,'Complete source path set or source bytes changed since gate'")
    if p.name.startswith('summarize-axioms'):
        s=s.replace('out)\n    assert matches,name','out,re.S)\n    assert matches,name')
        s=s.replace("axioms=set(raw.split(', ')) if raw else set()", "axioms={item.strip() for item in raw.split(',') if item.strip()}")
        s=s.replace("assert len(production)==30 and production.issubset(declarations)", "assert len(production)==30 and production.issubset(declarations)\nexpected_canaries={'AdaptiveProbe.'+name for name in load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']} | {'Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall','Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal'}\nassert len(expected_canaries)==9 and set(declarations)-production==expected_canaries")
    if p.name.startswith('inspect-exact-head'):
        s="raise SystemExit('DISABLED S3: site candidate H0 and later evidence H1 require separately reviewed ancestry/source-equivalence delivery logic. Do not claim H1 was site-built.')\n"
    ast.parse(s,filename=name);write(RUN/name,s);paths.append(RUN/name)
# Pure read-only regression of parser against preserved outputs, not a compiler run.
parsed={}
for name in load(RUN/'delivery-preparation-config-20261011-v1.json')['axiom_receipts']:
    d=load(RUN/name);assert d['actual_exit']==0
    out=base64.b64decode(d['stdout_base64']).decode('utf8')
    for decl,raw in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",out,re.S):
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        assert axioms.issubset({'propext','Classical.choice','Quot.sound'}) and decl not in parsed
        parsed[decl]=sorted(axioms)
prod={r['name'] for r in load(RUN/'shared-book-mapping-proposal-20261011-v2.json')['canonical_declarations'] if r['kind']=='theorem'}
canaries={'AdaptiveProbe.'+name for name in load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']} | {'Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall','Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal'}
assert len(parsed)==39 and len(prod)==30 and set(parsed)-prod==canaries and len(canaries)==9
write(RUN/'prepared-axiom-parser-regression-20261011-v3.json',dict(unique_total=len(parsed),production=30,canaries=9,all_standard_only=True,declarations=parsed,fresh_compiler_run=False))
write(RUN/'delivery-scripts-prepared-20261011-v3.json',dict(config=prior['config'],scripts=rows(paths),support=rows([RUN/'common.py',RUN/'prepared-axiom-parser-regression-20261011-v3.json']),ast_parse=True,executed=False,supersedes=rows([RUN/'delivery-scripts-prepared-20261011-v2.json']),repairs=dict(S1='Exact whole fresh source_binding list equality, including added/removed paths and tools/*.lean; common.py hash pinned in guard and manifest.',S2='re.S and comma.strip parse wrapped axiom lists; exact39unique=30production+9namedcanaries pure regression passes.',S3='Exact-head script disabled with explicit refusal pending separately reviewed H0site/H1evidence ancestry/source-equivalence repair.'),requirements=prior['requirements'],exact_favorable_review=prior['exact_favorable_review']))
print('v3 helper manifest SHA '+sha(RUN/'delivery-scripts-prepared-20261011-v3.json'))
