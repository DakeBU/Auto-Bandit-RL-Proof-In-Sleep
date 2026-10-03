import json,subprocess
from pathlib import Path
def show(stage,path):return subprocess.check_output(['git','show',':'+str(stage)+':'+path]).decode('utf-8')
report={'purpose':'Combine exact PR130 dependency with current main, preserving both shared libraries; not a merge into canonical main','imports':{},'manual_semantic_choices':[]}
for path in ['BanditRLProof.lean','Tests.lean']:
 ours=show(2,path);theirs=show(3,path)
 for s in [ours,theirs]:assert all(not l.strip() or l.startswith('import ') for l in s.splitlines()),path
 oi=[l for l in ours.splitlines() if l.startswith('import ')];ti=[l for l in theirs.splitlines() if l.startswith('import ')]
 out=ti+[l for l in oi if l not in ti]
 assert set(out)==set(oi)|set(ti)
 Path(path).write_text('\n'.join(out)+'\n',encoding='utf-8')
 report['imports'][path]={'PR130':len(oi),'main':len(ti),'union':len(out),'lost':[]}
p='website/content/books.json';base=json.loads(show(1,p));ours=json.loads(show(2,p));theirs=json.loads(show(3,p))
def merge(b,o,t,path=''):
 if o==t:return o
 if o==b:return t
 if t==b:return o
 if isinstance(b,dict) and isinstance(o,dict) and isinstance(t,dict):
  return {k:merge(b.get(k),o.get(k),t.get(k),path+'/'+k) for k in dict.fromkeys(list(b)+list(o)+list(t))}
 if isinstance(b,list) and all(isinstance(x,dict) and 'id' in x for x in b+o+t):
  bm={x['id']:x for x in b};om={x['id']:x for x in o};tm={x['id']:x for x in t}
  return [merge(bm.get(k),om.get(k),tm.get(k),path+'/'+k) for k in dict.fromkeys(list(bm)+list(om)+list(tm))]
 if isinstance(b,list) and all(isinstance(x,str) for x in b+o+t):return list(dict.fromkeys(o+t))
 if path=='/books/online-learning/summary':
  report['manual_semantic_choices'].append(path)
  return o+' Adjacent online-learning frontier questions are indexed separately from core Bandit/RL open problems.'
 raise RuntimeError(('Unreviewed conflict',path,b,o,t))
out=merge(base,ours,theirs)
Path(p).write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
report['parents']={k:subprocess.check_output(['git','rev-parse',k]).decode().strip() for k in ['HEAD','MERGE_HEAD']}
Path('runs/online-shared-base-20261003/resolution.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
