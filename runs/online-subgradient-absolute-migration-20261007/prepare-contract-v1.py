from common import *
f=fixed();passed('retained-focused-v1-01')
gate('actual-types-v1-01','lake','env','lean',RUN/'leaves/actual-types-v1.lean')
gate('pinned-APIs-v1-01','lake','env','lean',RUN/'leaves/pinned-APIs-v1.lean')
gate('compiled-ready-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-ready-dependencies-v1.lean',RUN/'compiled-ready-graph-v1.json')
g=load(RUN/'compiled-ready-graph-v1.json');assert len(g['nodes'])==4 and all(n['kind']=='theorem' and n['has_value'] for n in g['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[(PRE+'example_2_24',PRE+n) for n in ['abs_subgradient_positive','abs_subgradient_zero','abs_subgradient_negative']]
required.extend((PRE+n,PRE+'SourceSubdifferential') for n in ['abs_subgradient_positive','abs_subgradient_zero','abs_subgradient_negative'])
for pair in required:assert pair in pairs,pair
write(RUN/'ready-dependencies-v1.json',dict(status='passed',nodes=4,proof_nodes=4,definition_nodes=0,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-ready-graph-v1.json'),required_value_pairs=required,actual_project_value_pairs=sorted([list(p) for p in pairs if p[1].startswith('BanditRL.')]),full_graph_export=False,source_package_accepted=False))
for n,h in f['headers'].items():
 p=RUN/'native-draft-fences'/(n+'.json')
 native('draft-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p)
 assert load(p)['statement_hash']==h
native('local-declaration-search-v1','list-lean-decls','abs_subgradient','--statement')
native('local-memory-search-v1','search-memory','SourceSubdifferential')
native('retrieval-record-v1','retrieval-record','--task',TASK,'--query','scalar absolute global subdifferential/full closed zero interval','--candidate',PRE+'example_2_24','--candidate',PRE+'abs_subgradient_zero','--candidate','EReal.coe_add','--candidate','EReal.coe_le_coe_iff','--compiled-scratch',str(RUN/'actual-types-v1-01.log'),'--provenance','MLIB-ORDER-ALGEBRA; frozen local bodies and actual scalar abs/EReal API lookup; no new generic lemma or global reference-index rewrite','--output',str(RUN/'retrieval-record-v1.json'))
image=Path('tmp/online-subgradient-sum-source-pdf30-v1.png');assert sha(image)=='c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd'
write(RUN/'source-render-binding-v1.json',dict(source_pdf_sha256=load(CONTRACT/'source-card.json')['sha256'],image=image.as_posix(),image_sha256=sha(image),PDF_page=30,printed_page=18,current_actual_view_image=True,current_page_extraction_sha256=sha(RUN/'source-printed18-pdf30.txt'),visual='Actual cached page viewed this run: Ex2.24 full scalar threecase formula and inclusive [-1,1]; neighboring Ex2.25 and numbered2.26/2.28 distinct required obligations.'))
mapping={'SourceSubdifferential':'S',**{n:'N0'+str(i+1) for i,n in enumerate(f['headers'])}}
def neutral(t):
 for n in sorted(mapping,key=len,reverse=True):t=re.sub(r'\b'+re.escape(PRE+n)+r'\b',mapping[n],t);t=re.sub(r'\b'+n+r'\b',mapping[n],t)
 return t
context=load(CONTRACT/'scoped-contexts.json');typed=(RUN/'actual-types-v1-01.log').read_text(encoding='utf-8');typed=typed[:typed.index('AbsoluteZeroProbe.')]
packet='''Restricted neutral decoder packet. Requested GPT-6 Astra / medium. Read ONLY this packet, no source identity, proofs, repository searches, prior verdicts or other current files. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json in this run; receipt binds raw packet/report SHA and honest restricted input/history limits. Seven semantic slots for ALL FOUR exact targets. Distinct decoder actor; no source/package/Goal/human/external/runtime-model certification.

Neutral context: scalar ℝ with intrinsic real inner product; real values embed in EReal. S below is a GLOBAL predicate testing every ambient point and can accept arbitrary EReal functions. Actual four targets use a fixed function y↦coe(|y|), finite everywhere. There are no additional E/FiniteDimensional/CompleteSpace parameters or convexity/differentiability/domain qualifications in their actual signatures. All constants are exact; real Icc is inclusive, singleton equality characterizes every element. Deterministic static assertion.

Complete borrowed support definition (not new local owned definition):
```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
'''+neutral(context['borrowed_definition'])+'\n```\n\nExact neutral headers:\n```lean\n'+'\n\n'.join(neutral(r['statement']) for r in load(CONTRACT/'headers.json').values())+'\n```\n\nActual neutral types:\n```text\n'+neutral(typed)+'''\n```

Reconstruct allx terminal and sign leaves, necessity AND sufficiency for every slope, full zero interval and closed endpoints, nested conditional's final branch, exact allambient support test. Do any statements choose only one slope or assume a supporting inequality? Do not infer algorithms, differentiability at zero, a multidimensional norm result, probability, measurable/computable selection or chapter coverage. Describe generic S versus the fixed finite function without identifying a source.
'''
write(RUN/'blind-packet-v1.md',packet);generated('blind-generated-before-use-v1.json',[RUN/'blind-packet-v1.md'])
event('draft',dict(frozen_headers=f['headers'],retained_proofs=4,new_production_proofs=0,source_result_count=1,source_cases=3,source_package_accepted=False))
print('Four exact source targets/scalar @types/actual readiness',len(g['edges']),'direct refs; neutral blind packet ready. Distinct CONTRACT pending.')
