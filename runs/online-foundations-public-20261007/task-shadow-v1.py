from common_v1 import *
fixed(True)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
own=[t for t in trials if t.get('task')==TASK];assert len(own)==2 and {t['status'] for t in own}=={'compiled','failed'}
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in own))
digest='Persistent Chapters1-16 ACTIVE. Current '+TASK+' existing public Lemma1.2 revalidated, seven new named validation proofs/zero public source math. CONTRACT/BODY accepted; actual selected8kernel/8guards4VALUE686refs, complete targets unchanged, both failed neutral layout and canary normalization evidence kept. Eight OTHERChapter1 migrations/whole chapter reconciliation mandatory; Chapter2null/incomplete;3-16unenumerated/necessaryappendices. Current site/pixels/FINAL/native acceptance/PR pending. No merge/live.'
write(RUN/'memory-digest-candidate-v1.md',digest)
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; current Be-the-Leader source reuse and named tests','--leaf',TASK,'--kind','lean','--statement',(CONTRACT/'native-header-v1.txt').read_text(encoding='utf-8').strip(),'--declaration',PRE+'lemma_1_2','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','candidate','--dependency','lean:Finset.sum_range_succ:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
shadow=json.loads((RUN/'candidate-frontier-shadow-v1.log').read_text(encoding='utf-8'));assert not shadow['mismatches'] and not shadow['would_mutate']
fixed(True);print('Own candidate shadow PASS; globalSGB unchanged, failed attempt retained.')
