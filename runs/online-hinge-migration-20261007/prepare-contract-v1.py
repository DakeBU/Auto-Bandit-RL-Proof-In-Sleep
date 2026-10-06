"""Bind actual readiness, freeze native headers, and prepare a restricted neutral packet."""
from common_v2 import *
f=fixed()
for label in ['retained-focused-v1-01','actual-types-v1-01','pinned-APIs-v2-01','compiled-ready-graph-v1-01']:passed(label)
g=load(RUN/'compiled-ready-graph-v1.json')
assert len(g['nodes'])==15 and sum(n['kind']=='theorem' for n in g['nodes'])==13 and sum(n['kind']=='definition' for n in g['nodes'])==2 and all(n['has_value'] for n in g['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[('example_2_27',n) for n in ['hinge_subdifferential_hull','hinge_active_negative','hinge_active_positive','hinge_active_zero']]+[('hinge_subdifferential_hull',n) for n in ['theorem_2_26','hinge_max_identity','affine_proper','affine_convex','affine_continuous']]+[('hinge_family_support','affine_subdifferential')]+[(a,b) for a in ['hinge_active_negative','hinge_active_positive','hinge_active_zero'] for b in ['hinge_max_identity','hinge_family_support','hinge_family_false','hinge_family_true']]+[('affine_convex','affine_proper')]
for a,b in required:assert (PRE+a,PRE+b) in pairs,(a,b)
write(RUN/'ready-dependencies-v1.json',dict(status='passed',nodes=15,proof_nodes=13,definition_nodes=2,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-ready-graph-v1.json'),required_value_pairs=[(PRE+a,PRE+b) for a,b in required],actual_project_value_pairs=sorted([list(p) for p in pairs if p[1].startswith('BanditRL.')]),full_graph_export=False,canary_graph=False,source_package_accepted=False))
for n,h in f['headers'].items():
 p=RUN/'native-draft-fences'/(n+'.json');native('draft-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==h
native('retrieval-record-v1','retrieval-record','--task',TASK,'--query','actual two affine components full three-branch maximum subdifferential ordinary segment','--candidate',PRE+'theorem_2_26','--candidate',PRE+'affine_subdifferential','--candidate','convexHull_pair','--candidate','segment_eq_image','--compiled-scratch',RUN/'actual-types-v1-01.log','--provenance','MLIB-CONVEX-LINALG; fourteen pinned API types checked. Existing full producer/local15node graph, no new generic theorem, toolchain upgrade or external library import.','--output',RUN/'retrieval-record-v1.json')
context=load(CONTRACT/'scoped-contexts.json')
mapping={'sourceHinge':'H','hingeFamily':'B','SourceSubdifferential':'S','SourceProper':'P','effectiveDomain':'D','realEpigraph':'Q','IsConvexExtended':'C','SourceFiniteMax':'M','SourceActiveSubgradientUnion':'U',**{n:'L'+str(i+1).zfill(2) for i,n in enumerate(f['proof_names'])}}
def neutral(t):
 for n in sorted(mapping,key=len,reverse=True):
  t=re.sub(r'\b'+re.escape(PRE+n)+r'\b',mapping[n],t);t=re.sub(r'\b'+re.escape(n)+r'\b',mapping[n],t)
 return t
actual=(RUN/'actual-types-v1-01.log').read_text(encoding='utf-8');production=actual[:actual.index('HingeProbe.')]
definitions=[]
for m in re.finditer(r'(?m)^def '+re.escape(PRE)+r'(\w+)\b.*?(?=\n(?:def |$)|\Z)',actual,re.S):
 text=m.group(0);assert ':=' in text;definitions.append(text.split(':=',1)[0].rstrip())
assert len(definitions)==9,(len(definitions),[t.splitlines()[0] for t in definitions])
packet='''Restricted neutral reconstruction packet; requested GPT-6 Astra/medium. Read ONLY this packet. No repository/source/history/search, proof bodies or prior verdict. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to this packet, binding raw packet/report SHA and actor.task. Reconstruct all THIRTEEN proof targets L01-L13 separately in natural language and LaTeX, comparing seven slots: spaces/objects, quantifiers/order, assumptions/regularity, conclusion, constants/normalization, probability/information, boundary. Separate TWO owned definitions H/B from SEVEN borrowed contexts S/P/D/Q/C/M/U. Do not infer numbered source identity, source acceptance, whole-program completion, human/external review or runtime attestation.

Exact definitions and required scoped context:
```lean
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
'''+ '\n\n'.join(neutral(context['borrowed_definitions'][n]['body']) for n in ['SourceSubdifferential','SourceProper','effectiveDomain','realEpigraph','IsConvexExtended','SourceFiniteMax','SourceActiveSubgradientUnion'])+'\n\n'+'\n\n'.join(neutral(context['owned_definitions'][n]) for n in f['definition_names'])+'\n```\n\nExact neutral proof headers:\n```lean\n'+'\n\n'.join(neutral(load(CONTRACT/'headers.json')[n]['statement']) for n in f['proof_names'])+'\n```\n\nActual compiled public types:\n```text\n'+neutral(production)+'\n```\n\nActual compiled types of ALL nine definition contexts (bodies omitted from compiler print):\n```text\n'+'\n\n'.join(neutral(t) for t in definitions)+'''\n```

EReal includes top/bottom; real values are embedded canonically. S tests EVERY ambient y, P is global no-bottom plus a finite witness, D is value<top, C is real epigraph convexity. M is the actual nonempty finite maximum and U the union of every full support set of actual attaining components. Use actual compiled binders rather than imposing all section parameters on every borrowed definition. No claim about proof construction, algorithms, feedback, probability, regret, positive dimension, computable/measurable choice or coordinate conversions follows from this packet.
'''
assert PRE not in packet and 'example_2_27' not in packet and 'Orabona' not in packet and 'theorem_2_26' not in packet
write(RUN/'blind-packet-v1.md',packet);generated('blind-generated-before-use-v1.json',[RUN/'blind-packet-v1.md'])
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(RUN/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),unchanged_private_source=True,private_content_not_copied=True,paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',commands_versus_role_file_conventions_distinct=True))
write(RUN/'source-visual-read-v1.json',dict(path='tmp/online-subgradient-sum-source-pdf30-v1.png',sha256=sha('tmp/online-subgradient-sum-source-pdf30-v1.png'),actually_viewed_this_round=True,source_body_example='Example2.27',printed18_PDF30=True,content='actual hinge max(1-inner(z,x),0), full sets{0}/closed alpha segment[-z,0]/{-z}; no z nonzero assumption',not_canonical_main_live_or_chapter_completion=True))
write(RUN/'readonly-lookup-diagnostics-v1.json',dict(rows=[dict(chunk='21fb91',exit_code=1,reason='Readiness logs were not yet created; queried later after true readiness completed. No gate inference or source mutation.')],source_or_Lean_failure=False))
print('All15 native source fences and actual15node readiness bound; thirteen-target restricted neutral packet ready, CONTRACT pending.')
