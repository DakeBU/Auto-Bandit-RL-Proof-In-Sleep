"""Bind actual dependency readiness and current neutral theorem packet."""
from common_v2 import *
f=fixed()
for label in ['retained-focused-v1-01','actual-types-v1-01','pinned-APIs-v1-01','compiled-ready-graph-v1-01','reference-index-scoped-v1-01']:passed(label)
g=load(RUN/'compiled-ready-graph-v1.json');assert len(g['nodes'])==1 and g['nodes'][0]['kind']=='theorem' and g['nodes'][0]['has_value']
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[[PRE+'theorem_2_28','ContinuousLinearMap.adjoint_inner_left'],[PRE+'theorem_2_28','ContinuousLinearMap.map_sub']]
for a,b in required:assert (a,b) in pairs,(a,b)
write(RUN/'ready-dependencies-v1.json',dict(status='passed',nodes=1,proof_nodes=1,definition_nodes=0,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-ready-graph-v1.json'),required_value_pairs=required,actual_project_value_pairs=sorted([list(p) for p in pairs if p[1].startswith('BanditRL.')]),full_graph_export=False,source_package_accepted=False))
p=RUN/'native-draft-fences/theorem_2_28.json';native('draft-fence-theorem_2_28-v1','statement-fence','--declaration',PRE+'theorem_2_28','--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==f['headers']['theorem_2_28']
native('retrieval-record-v1','retrieval-record','--task',TASK,'--query','proper arbitrary extended-real global subgradient under actual affine map adjoint inclusion without convexity','--candidate',PRE+'theorem_2_28','--candidate','ContinuousLinearMap.adjoint_inner_left','--candidate','ContinuousLinearMap.map_sub','--candidate',PRE+'subgradient_point_finite','--compiled-scratch',RUN/'actual-types-v1-01.log','--provenance','MLIB-CONVEX-LINALG; actual eleven pinned API types/current compiled production dependency graph. Reuse existing actual producer, no coordinate certificate or unchecked external library.','--output',RUN/'retrieval-record-v1.json')
context=load(CONTRACT/'scoped-contexts.json');mapping={'SourceSubdifferential':'S','SourceProper':'P','theorem_2_28':'L'}
def neutral(t):
 for n in sorted(mapping,key=len,reverse=True):
  t=re.sub(r'\b'+re.escape(PRE+n)+r'\b',mapping[n],t);t=re.sub(r'\b'+re.escape(n)+r'\b',mapping[n],t)
 return t
actual=(RUN/'actual-types-v1-01.log').read_text(encoding='utf-8');primary=actual[:actual.index('AffineProbe.')]
defs=[]
for n in ['SourceSubdifferential','SourceProper']:
 m=re.search(r'(?m)^def '+re.escape(PRE+n)+r'\b.*?(?=\n(?:def |$)|\Z)',actual,re.S);assert m,n;defs.append(m.group(0).split(':=',1)[0].rstrip())
packet='''Restricted neutral reconstruction packet. Requested GPT-6 Astra/medium. Read ONLY this packet; no repository/source/history/search/proof body/prior verdict. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to packet; bind exact raw packet/report SHA, actor.task and requested settings without runtime attestation. Reconstruct ONE theorem L separately in natural language and LaTeX, seven slots spaces/objects, quantifier order, assumptions, conclusion, constants, information/probability, boundaries. S/P are TWO borrowed definition contexts, zero owned definitions. Do not infer cited source or acceptance.

```lean
noncomputable section
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
'''+ '\n\n'.join(neutral(context['borrowed_definitions'][n]['body']) for n in ['SourceSubdifferential','SourceProper'])+'\n\n'+neutral(load(CONTRACT/'headers.json')['theorem_2_28']['statement'])+'\n```\n\nActual compiled theorem type:\n```text\n'+neutral(primary)+'\n```\n\nActual compiled TWO borrowed definition binder types:\n```text\n'+'\n\n'.join(neutral(t) for t in defs)+'''\n```

EReal has top/bottom and canonical real embeddings; S tests every ambient y and P forbids bottom globally plus supplies one finite witness. Only use the displayed compiled binders. Actual ContinuousLinearMap.adjoint is Mathlib Hilbert adjoint, with completeness supplied by finite-dimensional real inner structure in L. Set.image is full image, subset is one direction. Do not infer convexity/continuity/closedness of f, properness of composite, rank conditions, finite query, support nonemptiness, equality, algorithm/regret/probability/selection or coordinate conversion certificates. Keep any limits/generic improper-context conventions explicit without seeing proof/source.
'''
assert PRE not in packet and 'Orabona' not in packet and 'theorem_2_28' not in packet
write(RUN/'blind-packet-v1.md',packet);generated('blind-generated-before-use-v1.json',[RUN/'blind-packet-v1.md'])
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(RUN/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),unchanged_private_source=True,private_content_not_copied=True,paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',commands_versus_role_file_conventions_distinct=True))
write(RUN/'source-visual-read-v1.json',dict(path='tmp/online-subgradient-sum-source-pdf30-v1.png',sha256=sha('tmp/online-subgradient-sum-source-pdf30-v1.png'),actually_viewed_this_round=True,source='Theorem2.28 printed18/PDF30; proper f,no convexity, actual affine identity, transpose image SUBSET, proof all-y',no_chapter_or_Goal_completion=True))
print('Single native header and actual readiness bound; neutral primary packet ready for distinct decoder.')
