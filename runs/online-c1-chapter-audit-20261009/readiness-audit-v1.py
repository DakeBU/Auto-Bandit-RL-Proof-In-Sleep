from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
fixed()
targets=load(CONTRACT/'targets-v1.json')['targets']
context=load(CONTRACT/'definition-context-v1.json')['definitions']
for t in targets:
    assert sha(t['path'])==t['file_sha256']
    assert statement_hash(lean_declaration_header(Path(t['path']),t['name']))==t['statement_hash']
for label,args in [
    ('help-list-lean-v1',['list-lean-decls','--help']),
    ('help-search-memory-v1',['search-memory','--help']),
    ('help-shadow-v1',['frontier-shadow','--help']),
    ('retrieve-public-c1-v1',['list-lean-decls','BanditRL.OnlineLearning','--statement']),
    ('retrieve-c1-memory-v1',['search-memory','Chapter 1']),
    ('retrieve-mathlib-cards-v1',['list-mathlib']),
    ('retrieve-paper-cards-v1',['list-papers']),
    ('retrieve-weapon-cards-v1',['list-weapons'])]:
    gate(label,sys.executable,'-B','-X','utf8','tools/bandit.py',*args)
modules=sorted(set('BanditRLProof.'+Path(t['path']).stem for t in targets if '/BanditRLProof/' in t['path']))
gate('focused-existing-public-v1','lake','build',*modules)
check=RUN/'named-public-readiness-v1.lean'
write(check,'import BanditRLProof\n\n'+'\n'.join('#check '+t['name']+'\n#print axioms '+t['name'] for t in targets))
gate('named-public-readiness-v1','lake','env','lean',check)
log=(RUN/'named-public-readiness-v1.log').read_text(encoding='utf8')
assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==len(targets)
assert 'sorryAx' not in log
for line in log.splitlines():
    if 'depends on axioms:' not in line:continue
    allowed={'propext','Classical.choice','Quot.sound'}
    used={x.strip() for x in line.split('depends on axioms:',1)[1].strip().strip('[]').split(',') if x.strip()}
    assert used<=allowed,(line,used)
oldgraph=ROOT/'runs/online-ftl-obstruction-20261009/export-compiled-graph-v1.lean'
code=oldgraph.read_text(encoding='utf8')
body=code[code.index('def moduleName'):]
body=body.replace('Tests.OnlineFTLOscillationCanary','BanditRLProof')
body=body.replace('Four frozen actual FTL obstruction/iff bodies, eleven dyadic public canaries and exact parents. Selected direct coalesced TYPE_VALUE constants only; not full transitive graph or source/chapter coverage.',
    'Fifty exact reused public Chapter1 proof targets plus selected support definitions. Compiled current readiness only, not source/chapter acceptance. Selected coalesced direct TYPE_VALUE constant presence, not full transitive proof graph or new theorem count.')
names=[t['name'] for t in targets]+[t['name'] for t in context]
names=sorted(set(names))
graph=RUN/'export-readiness-graph-v1.lean'
write(graph,'import BanditRLProof\nimport Lean\nimport Lean.Util.FoldConsts\n\nopen Lean\n\ndef targets : Array Name := #[\n'+
    ',\n'.join('`'+name for name in names)+']\n\n'+body)
gate('export-readiness-graph-v1','lake','env','lean','--run',graph,RUN/'compiled-readiness-graph-v1.json')
g=load(RUN/'compiled-readiness-graph-v1.json')
assert {n['name'] for n in g['nodes']}==set(names)
assert all(n['has_value'] and n['module']!='unknown' for n in g['nodes'])
assert all(next(n for n in g['nodes'] if n['name']==t['name'])['kind']=='theorem' for t in targets)
fixed()
write(RUN/'compiled-readiness-v1.json',dict(phase='draft dependency readiness audit ONLY',
    actual_focused_build_zero=True,actual_named_public_typecheck_zero=True,selected_named_targets=len(targets),
    all_named_targets_have_compiled_public_theorem_values=True,unique_axiom_outputs=len(targets),standard_only=True,
    selected_nodes=len(g['nodes']),direct_coalesced_TYPE_VALUE_edges=len(g['edges']),
    no_new_production_math=True,source_inventory_acceptance=False,chapter_complete=False,goal_complete=False,
    source_header_hashes_unchanged=True,baseline_unchanged=True,
    retrieval_policy='Actual native source scan/read-only searches and cards. No generic new lemma or global reference-index rewrite. Frozen global indexes unchanged.'))
print('Actual draft readiness:',len(targets),'public proof values;',len(g['nodes']),'selected compiled nodes; chapter acceptance still pending.',flush=True)
