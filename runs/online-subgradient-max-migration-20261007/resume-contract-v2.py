from common_v2 import *
f=fixed()
context=load(CONTRACT/'scoped-contexts-v2.json');mapping={'SourceFiniteMax':'M','SourceActiveSubgradientUnion':'U','SourceSubdifferential':'S','SourceProper':'P','effectiveDomain':'D','realEpigraph':'Q','IsConvexExtended':'C',**{n:'C'+str(i+1).zfill(2) for i,n in enumerate(f['proof_names'])}}
def neutral(t):
 for n in sorted(mapping,key=len,reverse=True):
  t=re.sub(r'\b'+re.escape(PRE+n)+r'\b',mapping[n],t);t=re.sub(r'\b'+re.escape(n)+r'\b',mapping[n],t)
 return t
actual=(RUN/'actual-types-v1-01.log').read_text(encoding='utf-8');actual=actual[:actual.index('MaximumProbe.')]
packet='''Restricted neutral reconstruction packet; requested GPT-6 Astra/medium. Read ONLY this packet. No repository/source lookup, proof bodies, source identity, prior verdict or inherited history. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to this packet; bind exact raw packet/report SHA and actor.task. Reconstruct all SEVENTEEN proof targets C01-C17 separately in natural language and LaTeX with seven semantic slots (objects/spaces; quantifiers; assumptions; conclusions; constants; information/probability; boundaries). Separate two owned definitions M/U from five borrowed contexts S/P/D/Q/C. Do not guess numbered source identity, count supporting lemmas as separate source results, or certify source acceptance, whole chapter/Goal, external-human review/runtime model.

```lean
noncomputable section
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
'''+ '\n\n'.join(neutral(context['borrowed_definitions'][n]['body']) for n in ['SourceSubdifferential','SourceProper','effectiveDomain','realEpigraph','IsConvexExtended'])+'\n\n'+'\n\n'.join(neutral(context['owned_definitions'][n]) for n in f['definition_names'])+'\n```\n\nExact neutral headers:\n```lean\n'+'\n\n'.join(neutral(load(CONTRACT/'headers.json')[n]['statement']) for n in f['proof_names'])+'\n```\n\nActual compiled neutral public types:\n```text\n'+neutral(actual)+'''
```

EReal includes top and bottom. S universally tests EVERY ambient y. P prohibits bottom EVERYWHERE and requires an actual finite witness; D uses value<top. C is real epigraph convexity. M is actual nonempty finite maximum, U includes ALL supports of every actual attaining component. Use actual inferred binders: M is on arbitrary E, while U uses real inner-product structure; each proof may retain section classes and some add finite dimensionality explicitly. Norm is that compatible real inner-product norm. Full C17 uses finite-dimensional E; finite NONEMPTY index; every component proper/convex; common finite query; EVERY component AMBIENT EReal ContinuityAt at that query; full ordinary convexHull equality BOTH directions for ALL candidate vectors. No closed hull, merely one-way inclusion, supplied decomposition, assumed direction witness, relative-domain continuity, globally finite function, extra boundedness/closedness/positive dimension/computability/measurable selection/feedback/regret/probability guarantee. Distinguish stronger foundational premise scopes from C17. Reconstruct direction witness C16 from its actual universal g/d, existential active k, and inner-product inequality without seeing proof.
'''
assert 'theorem_2_26' not in packet and 'Orabona' not in packet and PRE not in packet
write(RUN/'blind-packet-v1.md',packet);generated('blind-generated-before-use-v1.json',[RUN/'blind-packet-v1.md'])
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(RUN/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),unchanged_private_source=True,private_content_not_copied=True,paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',commands_versus_role_file_conventions_distinct=True))
write(RUN/'source-visual-read-v1.json',dict(path='tmp/online-subgradient-sum-source-pdf30-v1.png',sha256=sha('tmp/online-subgradient-sum-source-pdf30-v1.png'),actually_viewed_this_round=True,source_formal_result='Theorem2.26',printed18_PDF30=True,content='finite proper convex family; common domain query; each component continuous; actual maximum; actual active set; ordinary convex hull full equality',not_canonical_main_live_or_chapter_completion=True))
event('draft',dict(frozen_headers=f['headers'],retained_proofs=17,retained_definitions=2,new_production_proofs=0,source_formal_results=1,source_package_accepted=False,API_probe_failed_v1_preserved=True,pre_use_context_and_exporter_corrections_preserved=True))
print('Nineteen native fences/1795 actual compiled readiness references/16 required value pairs; restricted neutral packet ready, CONTRACT pending.')
