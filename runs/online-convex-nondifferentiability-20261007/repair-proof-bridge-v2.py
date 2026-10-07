"""Respect existing three-to-five-step reader schema; conserve all mathematical explanations."""
from common_v4 import *
fixed(True,True);assert load(RUN/'site-build-v1-01-exit.json')['exit_code']==1
assert 'reading online-lipschitz has an incomplete proof bridge' in (RUN/'site-build-v1-01.log').read_text(encoding='utf-8')
p=Path('website/content/readings.json');write(RUN/'snapshots/readings-before-proof-bridge-repair-v2.txt',p.read_bytes())
d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE);steps=x['proof_bridge']['steps'];assert len(steps)==7
cards=x['source_theorems'];oldroute={k:v for k,v in x.items() if k!='proof_bridge'}
def merge(a,b,title):
 return dict(title=title,detail=a['detail']+' '+b['detail'],math=r'\begin{gathered}'+a['math']+r'\\'+b['math']+r'\end{gathered}',fallback=a['fallback']+' '+b['fallback'])
x['proof_bridge']['steps']=[merge(steps[0],steps[1],'Forward: finite values and perturb every support'),merge(steps[2],steps[3],'Reverse: produce both supports and bound both differences'),*steps[4:]]
assert len(x['proof_bridge']['steps'])==5 and oldroute=={k:v for k,v in x.items() if k!='proof_bridge'}
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'proof-bridge-reader-repair-v2.json',dict(failed_attempt='site-build-v1-01',reason='Existing reader schema permits three to five bridge steps; additive candidate had seven',repair='Consolidate earlier forward pair and reverse pair without removing any detail/fallback/formula; retain all three new actual producer steps',source_cards_unchanged=True,all_other_reader_fields_unchanged=True,old_raw_snapshot='snapshots/readings-before-proof-bridge-repair-v2.txt',current_reader_sha256=sha(p),site_generator_schema_unchanged=True,Lean_math_unchanged=True,mathematical_repairs=[]))
t=(RUN/'bind-integrated-gates-v2.py').read_text(encoding='utf-8').replace('contributor-exact-v2-01','contributor-exact-v3-01').replace('scoped-diff-v1-01','scoped-diff-v2-01').replace('site-build-v1-01','site-build-v2-01')
t=t.replace("'Exact contributor v1 rejected Tests in production-surface list; existing schema retained, tests remain in explicit owned-test fields, exact v2 recheck'","'Exact contributor v1 rejected Tests in production-surface list; existing schema retained, tests remain in explicit owned-test fields, exact v2/v3 rechecks','Site build v1 rejected seven bridge steps; existing 3-to-5-step schema preserved, earlier forward/reverse pairs consolidated without losing explanations/formulas, all three new producer steps retained'")
write(RUN/'bind-integrated-gates-v3.py',t);compile(t,str(RUN/'bind-integrated-gates-v3.py'),'exec')
fixed(True,True);print('Reader-only five-step consolidation; mathematical/source cards and existing schema fixed. Actual site v2 build pending.')
