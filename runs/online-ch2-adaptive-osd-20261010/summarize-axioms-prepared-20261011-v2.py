from delivery_guard_20261011_v2 import *
a=arguments();fixed(a);declarations={};inputs=[]
for name in CONFIG['axiom_receipts']:
    path=RUN/name;d,out=output_of(path)
    assert d['command'][:3]==['lake','env','lean'] and d['cwd']==ROOT.as_posix()
    matches=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",out)
    assert matches,name
    for decl,raw in matches:
        axioms=set(raw.split(', ')) if raw else set()
        assert axioms.issubset({'propext','Classical.choice','Quot.sound'}),(decl,axioms)
        assert decl not in declarations
        declarations[decl]=dict(axioms=sorted(axioms),receipt=path.as_posix())
    inputs+=rows([path])
assert len(declarations)==39
mapping=load(load(PLAN)['mapping'][0]['path'])
production={x['name'] for x in mapping['canonical_declarations'] if x['kind']=='theorem'}
assert len(production)==30 and production.issubset(declarations)
write(RUN/('axiom-summary-'+a.tag+'.json'),dict(source_binding=source_binding(),inputs=inputs,public_theorem_count=39,production_theorems=30,canary_theorems=9,actual_prior_public_output_revalidated=True,fresh_compiler_run=False,declarations=declarations,boundary='Revalidation of actual captured public probes at unchanged source hashes; standard axioms only, not semantic/chapter or new compiler evidence'))
