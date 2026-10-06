"""Bind two retained nodes and a neutral packet with all actual definition binders."""
from common_v2 import *
f=fixed()
for label in ['retained-focused-v1-01','actual-types-v1-01','pinned-APIs-v1-01','compiled-ready-graph-v1-01','reference-index-scoped-v1-01']:passed(label)
g=load(RUN/'compiled-ready-graph-v1.json');assert len(g['nodes'])==2 and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==1 and sum(n['kind']=='definition' for n in g['nodes'])==1
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[[PRE+'theorem_2_30',PRE+'subgradient_norm_le_lipschitz_ball'],[PRE+'theorem_2_30',PRE+'subgradient_exists_of_domain_interior'],[PRE+'theorem_2_30','abs_real_inner_le_norm'],[PRE+'theorem_2_30','EReal.coe_toReal']]
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'ready-dependencies-v1.json',dict(status='passed',nodes=2,proof_nodes=1,definition_nodes=1,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-ready-graph-v1.json'),required_value_pairs=required,actual_project_value_pairs=sorted([list(p) for p in pairs if p[1].startswith('BanditRL.')]),full_graph_export=False,source_package_accepted=False))
for n,h in f['headers'].items():
 p=RUN/('native-draft-fences/'+n+'.json');native('draft-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==h
native('retrieval-record-v1','retrieval-record','--task',TASK,'--query','proper convex extended-real finite values ambient interior Lipschitz iff every global supporting vector norm bounded nonnegative constant','--candidate',PRE+'theorem_2_30','--candidate',PRE+'SourceLipschitzOn','--candidate',PRE+'subgradient_norm_le_lipschitz_ball','--candidate',PRE+'subgradient_exists_of_domain_interior','--compiled-scratch',RUN/'actual-types-v1-01.log','--provenance','MLIB-CONVEX-LINALG; actual pinned API/types/compiled producer value edges; no unchecked external library, assumed support existence or theorem wrapper.','--output',RUN/'retrieval-record-v1.json')
context=load(CONTRACT/'scoped-contexts.json');mapping={'SourceLipschitzOn':'B','SourceSubdifferential':'S','SourceProper':'P','effectiveDomain':'D','realEpigraph':'Q','IsConvexExtended':'C','theorem_2_30':'L'}
def neutral(t):
 for n in sorted(mapping,key=len,reverse=True):
  t=re.sub(r'\b'+re.escape(PRE+n)+r'\b',mapping[n],t);t=re.sub(r'\b'+re.escape(n)+r'\b',mapping[n],t)
 return t
actual=(RUN/'actual-types-v1-01.log').read_text(encoding='utf-8');primary=actual[:actual.index('LipschitzProbe.')]
defs=[]
for n in ['SourceLipschitzOn','SourceSubdifferential','SourceProper','effectiveDomain','realEpigraph','IsConvexExtended']:
 m=re.search(r'(?m)^def '+re.escape(PRE+n)+r'\b.*?(?=\n(?:def |$)|\Z)',actual,re.S);assert m,n;defs.append(m.group(0).split(':=',1)[0].rstrip())
packet='''Restricted neutral reconstruction packet. Requested GPT-6 Astra/medium. Read ONLY this packet; no repository/source/history/search/proof body/prior verdict. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to packet, bind exact raw packet/report SHA and actor.task/requested settings, no runtime attestation. Reconstruct ONE owned definition B and ONE theorem L separately in natural language/LaTeX and seven semantic slots (objects, quantifier order, assumptions, conclusion, constants, information/probability, boundaries). Five other definition contexts S/P/D/Q/C are borrowed and not newly owned. Use actual compiled binder types, not blanket ambient assumptions.

```lean
noncomputable section
open Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
'''+ '\n\n'.join(neutral(context['borrowed_definitions'][n]['body']) for n in ['SourceSubdifferential','SourceProper','effectiveDomain','realEpigraph','IsConvexExtended'])+'\n\n'+neutral(context['owned_definitions']['SourceLipschitzOn'])+'\n\n'+neutral(load(CONTRACT/'headers.json')['theorem_2_30']['statement'])+'\n```\n\nActual compiled primary types:\n```text\n'+neutral(primary)+'\n```\n\nActual compiled SIX definition binder types:\n```text\n'+'\n\n'.join(neutral(t) for t in defs)+'''\n```

EReal has top/bottom and real embeddings; B requires genuine finite real witnesses on V before its toReal difference. NNReal is the nonnegative reals INCLUDING0. D tests strict inequality belowtop; P forbids bottom globally with a finite witness; S uses all ambient support tests; Q is a real-height epigraph and C its convexity. Theorem uses AMBIENT interior, not relative interior or closure/boundary/all of D. Norm is the inherited inner-product norm in L; B's own actual inferred binders determine its broader scope. No closedness, differentiability, boundedness, positive constant/positive dimension/nonempty interior or supplied support-existence premise. No source all-real-constant claim, selected-gradient-only conclusion, future algorithm/oracle/regret/probability/feedback/selection certificate. Do not infer cited source or acceptance from this packet.
'''
assert PRE not in packet and 'Orabona' not in packet and 'theorem_2_30' not in packet
write(RUN/'blind-packet-v1.md',packet);generated('blind-generated-before-use-v1.json',[RUN/'blind-packet-v1.md'])
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(RUN/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),unchanged_private_source=True,private_content_not_copied=True,paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',commands_versus_role_file_conventions_distinct=True))
print('Actual two-node readiness',len(g['edges']),'references/four required producer pairs; neutral definition/theorem packet ready.')
