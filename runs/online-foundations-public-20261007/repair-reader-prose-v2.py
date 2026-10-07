from common_v1 import *
import ast
fixed(True)
for p in ['website/content/readings.json','website/content/highlights.json']:
 write(RUN/'snapshots'/(p.replace('/','--')+'-reader-v1.raw'),Path(p).read_bytes())
p=Path('website/content/readings.json');d=load(p)
x=next(a for a in d['readings'] if a['slug']==ROUTE)
x['source_theorems'][0]['local_status']['boundary']='Existing Lemma 1.2 has been rechecked with seven named validation proofs. It compares supplied feasible hindsight minimizers; it does not construct a causal learner or establish a regret rate. The arbitrary-type extension and horizon boundaries are explained below. This bounded package does not complete Chapter 1 or its integration into main.'
original=load(RUN/'snapshots/website--content--readings.json.raw')
old=next(a for a in original['readings'] if a['slug']==ROUTE)
x['worked_example']['boundary']=old['worked_example']['boundary']+' This FTL example uses strict-past predictions. The separate Be-the-Leader validation compares current-prefix hindsight minimizers; those are different sequences. Chapter 1 coverage and source reconciliation remain open.'
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p=Path('website/content/highlights.json');d=load(p);x=next(a for a in d['highlights'] if a['full_name']==PRE+'lemma_1_2')
x['lean_notes']='The source uses a subset V of real Euclidean space and losses defined on V. Lean permits any ambient type X and total real loss functions; restricting them to V recovers the source. For every positive prefix n <= T, leader n must belong to V and minimize the prefix loss against every u in V. These minimizers are supplied; their existence is not proved. No geometry or probability assumption is needed. The leader includes the current loss, so it is a hindsight object rather than a strict-past FTL prediction. At T = 0 the conclusion is the empty-sum extension; T = 1 has identical sides. Seven named tests include changing feasible minimizers with strict inequality -2 < 0, a feasible nonoptimal sequence reversing the comparison, and an ambient-domain sequence showing why membership is necessary. The last sequence is not admissible when source losses are defined only on V. This package revalidates one existing source lemma and adds validation proofs, not new book results. Theorem 1.3 and the causal FTL chain are separate. Chapter 1 source reconciliation and integration into main remain open; all nine main-relative contributor gaps are retained in the audit. No merge or publication is claimed.'
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'reader-prose-repair-v2.json',dict(status='Reader prose repaired before FINAL; new capture and review pending',reason='Actual v1 source-card status and worked-example scope repeated technical audit details; public technical note was unnecessarily tall.',preserved_v1_snapshots=True,changed_fields=['one source-card local_status.boundary','one worked_example.boundary','one public-note lean_notes'],all_math_headers_bodies_other_cards_notes_unchanged=True,mathematical_contract_version=1,new_public_math=0,chapter_complete=False,goal_complete=False))
for name in ['verify-registry-v1.py','capture-reader-v1.py','capture-reader-v1.cjs','continue-site-v2.py']:
 text=(RUN/name).read_text(encoding='utf-8')
 text=text.replace('site-v1','site-v2').replace('site-build-v1','site-build-v2').replace('site-check-v1','site-check-v2').replace('registry-v1','registry-v2').replace('formula-render-v1','formula-render-v2').replace('capture-reader-v1','capture-reader-v2').replace('playwright-v1-profile','playwright-v2-profile')
 # Capture image file names use their own v1 suffix.
 if name.endswith('.cjs'):text=text.replace('-v1.png','-v2.png')
 dest=name.replace('verify-registry-v1','verify-registry-v2').replace('capture-reader-v1','capture-reader-v2').replace('continue-site-v2','continue-site-reader-v3')
 write(RUN/dest,text)
 if dest.endswith('.py'):ast.parse(text)
p=RUN/'prepare-final-review-v1.py';text=p.read_text(encoding='utf-8')
text=text.replace('formula-render-v1','formula-render-v2').replace('registry-v1','registry-v2').replace('site-v1','site-v2').replace('site-build-v1','site-build-v2').replace('site-check-v1','site-check-v2')
text=text.replace('all five','all five')
text=text.replace('Publication helper v1 prepared binding retained historically;', 'Actual v1 reader snapshots/images are historical and preserved. A prose-only readability repair shortened repeated audit prose in the one-card status, worked-example scope and one public technical note; original source/math/other cards/notes unchanged. Current v2 pixels must actually be viewed. Publication helper v1 prepared binding retained historically;')
p.write_bytes(text.encode('utf-8'));ast.parse(text)
prior=load(RUN/'publication-tools-before-FINAL-v2.json')
write(RUN/'publication-tools-before-FINAL-v3.json',dict(scope='Before FINAL, bind new current v2-reader preparation; historical helper tables and v1 captures preserved.',rows=[dict(path=a['path'],sha256=sha(a['path'])) for a in prior['rows']]+[dict(path=p.as_posix(),sha256=sha(p))],source_math_contract_version=1,new_public_math=0,actual_FINAL_not_executed=True))
fixed(True)
print('Prose-only current reader repair prepared; current site/pixel/FINAL gates pending.')
