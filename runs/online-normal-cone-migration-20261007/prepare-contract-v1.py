from common import *
f=fixed();passed('retained-focused-v1-01');passed('actual-types-v1-01');passed('pinned-APIs-v1-01');passed('compiled-ready-graph-v1-01')
assert 'Build completed successfully' in (RUN/'retained-focused-v1-01.log').read_text(encoding='utf-8')
g=load(RUN/'compiled-ready-graph-v1.json');assert len(g['nodes'])==4 and sum(n['kind']=='theorem' for n in g['nodes'])==3 and sum(n['kind']=='definition' for n in g['nodes'])==1 and all(n['has_value'] for n in g['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[(PRE+n,PRE+'SourceNormalCone') for n in f['proof_names']]+[(PRE+f['proof_names'][0],PRE+n) for n in ['SourceSubdifferential','extendedIndicator','sourceProper_indicator_iff','effectiveDomain_indicator','subgradient_point_finite']]
for p in required:assert p in pairs,p
write(RUN/'ready-dependencies-v1.json',dict(status='passed',nodes=4,proof_nodes=3,definition_nodes=1,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-ready-graph-v1.json'),required_value_pairs=required,actual_project_value_pairs=sorted([list(p) for p in pairs if p[1].startswith('BanditRL.')]),full_graph_export=False,canary_graph=False,source_package_accepted=False))
for n,h in f['headers'].items():
 path=RUN/'native-draft-fences'/(n+'.json')
 native('draft-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',path);assert load(path)['statement_hash']==h
native('local-declaration-search-v1','list-lean-decls','normalCone','--statement')
native('local-memory-search-v1','search-memory','SourceNormalCone')
native('retrieval-record-v1','retrieval-record','--task',TASK,'--query','full indicator support/ambient interior normals/full closed unit-ball boundary nonnegative ray','--candidate',PRE+'indicator_subdifferential_eq_normalCone','--candidate',PRE+'SourceNormalCone','--candidate','norm_sub_sq_real','--candidate','real_inner_le_norm','--compiled-scratch',str(RUN/'actual-types-v1-01.log'),'--provenance','MLIB-ORDER-ALGEBRA and pinned metric/inner-product APIs; retained producer bodies inspected, no newgeneric lemma/external compatible rebuild/pin change','--output',str(RUN/'retrieval-record-v1.json'))
context=load(CONTRACT/'scoped-contexts.json');mapping={'SourceNormalCone':'N','SourceSubdifferential':'S','extendedIndicator':'J',**{n:'C0'+str(i+1) for i,n in enumerate(f['proof_names'])}}
def neutral(t):
 for n in sorted(mapping,key=len,reverse=True):t=re.sub(r'\b'+re.escape(PRE+n)+r'\b',mapping[n],t);t=re.sub(r'\b'+re.escape(n)+r'\b',mapping[n],t)
 return t
actual=(RUN/'actual-types-v1-01.log').read_text(encoding='utf-8');actual=actual[:actual.index('NormalIndicatorProbe.')]
packet='''Restricted neutral reconstruction packet. Requested GPT-6 Astra / medium. Read ONLY this packet, no repository search, source identity, proof bodies, prior verdicts or other files. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json next to this packet. Bind raw packet/report SHA and disclose exact input/history limits. Reconstruct EVERY target C01–C03 in natural language and LaTeX, seven semantic slots individually; separately reconstruct owned definition N and distinguish borrowed S/J. No source/package/chapter/Goal/external-human/runtime-model certification.

```lean
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
'''+neutral(context['owned_normal_definition'])+'\n\n'+neutral(context['borrowed_support_definition'])+'\n\n'+neutral(context['borrowed_indicator_definition'])+'\n```\n\nExact three neutral headers:\n```lean\n'+'\n\n'.join(neutral(r['statement']) for n,r in load(CONTRACT/'headers.json').items() if n in f['proof_names'])+'\n```\n\nActual neutral compiled public types:\n```text\n'+neutral(actual)+'''
```

Use actual explicit/inferred binders and every universal quantifier. EReal has top/bottom; J takes only0/top, S is global and can accept arbitrary EReal functions. Norm/inner product are the real inner-product structure's compatible norm. Convex ℝ V uses real convex combinations; interior is ambient topological interior. The first two statements retain nonempty convexV explicitly. Definitions may have fewer class parameters than the theorems. The final statement's existential scalar is real, with0≤α, equality includes all elements. Distinguish equality from inclusion, actual set membership from a supplied characterization, outside-query meaning, zero multipliers, empty/thin sets, finite-dimensional theorem binders and the closed norm≤1 set. Do not infer an algorithm, regret, probability, closedness of arbitraryV, relative interior, positive dimension, a separate coordinate isometry certificate or computable/measurable vector selection.
'''
write(RUN/'blind-packet-v1.md',packet);generated('blind-generated-before-use-v1.json',[RUN/'blind-packet-v1.md'])
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(RUN/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),unchanged_private_source=True,private_content_not_copied=True,paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',commands_versus_role_file_conventions_distinct=True))
event('draft',dict(frozen_headers=f['headers'],retained_proofs=3,retained_definitions=1,new_production_proofs=0,source_body_examples=1,source_claims=3,source_package_accepted=False))
print('Three proofs/one full owned definition/818 compiled readiness references; neutral current decoder packet ready, CONTRACT pending.')
