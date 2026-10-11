"""Read-only exact approved source/content chain; no site/gate acceptance."""
import copy, hashlib, json, subprocess
from pathlib import Path
from collections import Counter
HEAD='ceef2d303da1398bd543d144930e3ec7e1b58263'
BASE='48ca57cd497a3dcebbeedeb2d54ef3bcefdcd937'
LOCAL='3db67ccf41c1c5a312c625b7ed9a2440f1183b7f'
MERGE='5bff23f88ff5b9633d8e3126096df979ea1771d6'
SUPPORT='BanditRL.OnlineConvex.stronglyConvex_support_growth'
def h(b): return hashlib.sha256(b).hexdigest()
def need(x,msg):
 if not x: raise ValueError(msg)
def raw(r,c,p): return subprocess.check_output(['git','-c','core.longpaths=true','show',c+':'+p],cwd=r)
def load(p): return json.loads(p.read_bytes())
def unique(xs,k,v):
 ys=[x for x in xs if x.get(k)==v];need(len(ys)==1,'unique '+str(v));return ys[0]
def check(r,spec):
 for p,sha in spec['bindings'].items():need(h((r/p).read_bytes())==sha,'pin '+p)
 plan=load(r/spec['main_plan']);need(len(plan['changes'])==60,'exact 60 corrections')
 docs={};fields={'books':'id','chapters':'slug','readings':'slug','highlights':'full_name'}
 for name in fields:
  p='website/content/'+name+'.json';docs[p]=json.loads(raw(r,BASE,p));need(docs[p]==json.loads(raw(r,LOCAL,p)),'growth/local full equality '+p)
 for n,c in enumerate(plan['changes']):
  p=c['locator'].split('.json/',1)[0]+'.json';parts=c['locator'].split('.json/',1)[1].split('/',2);key,field=parts[:2]
  family=Path(p).stem;row=unique(docs[p][family],fields[family],key)
  if field=='source_theorems':
   label=parts[2];card=unique(row[field],'label',label);need(card==c['before'],'before card '+str(n));row[field][row[field].index(card)]=copy.deepcopy(c['after'])
  else:
   need(row.get(field)==c['before'],'before field '+str(n));row[field]=copy.deepcopy(c['after'])
 for p,d in docs.items():need(d==json.loads(raw(r,MERGE,p)),'exact replay60 equals actual merge '+p)
 for repair in plan['semantic_parent_card_repairs']:
  cards=unique(docs['website/content/readings.json']['readings'],'slug',repair['slug'])['source_theorems']
  need(len(cards)==1 and cards[0]['label']==repair['new_label'],'single corrected parent card '+repair['slug'])
 # Whole-object lists stay ordered. No dict conversion of duplicate highlights.
 before=copy.deepcopy(docs)
 app=load(r/spec['support_plan'])
 for item in app['files']:
  need(h((r/item['candidate']['path']).read_bytes())==item['candidate']['sha256'],'reviewed support candidate '+item['target'])
  need((r/item['target']).read_bytes()==(r/item['candidate']['path']).read_bytes(),'installed candidate exact '+item['target'])
 new={p:load(r/p) for p in docs}
 b=before['website/content/highlights.json']['highlights'];a=new['website/content/highlights.json']['highlights']
 need(len(b)==503 and len(a)==504 and a[:-1]==b and a[-1]['full_name']==SUPPORT,'one appended highlight, old sequence/multiplicity exact')
 enc=lambda x:json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':'))
 need(Counter(map(enc,a))-Counter(map(enc,b))==Counter([enc(a[-1])]),'exact multiset addition')
 docs['website/content/highlights.json']['highlights'].append(copy.deepcopy(a[-1]))
 oldogd=unique(docs['website/content/readings.json']['readings'],'slug','online-ogd');newogd=unique(new['website/content/readings.json']['readings'],'slug','online-ogd')
 need(len(oldogd['source_theorems'])==24 and len(newogd['source_theorems'])==25,'24 to25 source cards');oldogd['source_theorems'].append(copy.deepcopy(newogd['source_theorems'][-1]))
 oldchapter=unique(docs['website/content/chapters.json']['chapters'],'slug','online-ogd');oldchapter['module_globs'].append('BanditRLProof/OnlineStrongConvexSupport.lean')
 oldbook=unique(docs['website/content/books.json']['books'],'id','online-learning');newbook=unique(new['website/content/books.json']['books'],'id','online-learning')
 need(newbook['summary'].startswith(oldbook['summary']) and len(newbook['summary'])>len(oldbook['summary']),'literal support Book suffix');oldbook['summary']=newbook['summary']
 for p,d in docs.items():need(d==new[p],'only reviewed support appends, no extra JSON differences '+p)
 need(len(docs['website/content/chapters.json']['chapters'])==40,'40 routes')
 need(len(newbook['chapter_refs'])==33,'33 total Book references')
 for p in ['BanditRLProof/OnlineConstraintFiniteLoss.lean','BanditRLProof/OnlineConvexMinorant.lean']:
  a=raw(r,LOCAL,p);b=raw(r,MERGE,p);need(a!=b and a.split(b'-/',1)[1]==b.split(b'-/',1)[1],'two initial comment-only changes '+p);need((r/p).read_bytes()==b,'current comment correction exact '+p)
 for p,imp in [('BanditRLProof.lean',b'import BanditRLProof.OnlineStrongConvexSupport'),('Tests.lean',b'import Tests.OnlineStrongConvexSupportCanary')]:
  # RAW prefix comes from independently reviewed application plan, not Git EOL conversion.
  candidate=(r/next(x['candidate']['path'] for x in app['files'] if x['target']==p)).read_bytes();need(candidate.count(imp)==1,'one shared root import '+p)
 core=r/'BanditRLProof/OnlineStrongConvexSupport.lean';canary=r/'Tests/OnlineStrongConvexSupportCanary.lean'
 need(h(core.read_bytes())=='f3a475b58661a4efefdb33b9715852a08008940bd437e1cb3ad64862b772d1e5','reviewed support core RAW')
 need(h(canary.read_bytes())=='62163851ea2edb131a6f365d624de4523aa19d16e62ad16a598db66386afa01c','reviewed support canary RAW')
 c2=next(x for x in load(r/'docs/contracts/online-book-v1/coverage.json')['chapters'] if x['chapter']==2)
 need(c2['accepted'] is False and c2['mandatory_count'] is None and c2['status'].startswith('partial') and c2['required_open_forward_containers']==7 and c2['required_future_mathematical_claims_open_unenumerated']==6,'C2partial/7+6/null')
 return {'status':'source preparation checks passed only','exact_main_corrections':60,'comment_only_changes':2,'highlight_counts':[503,504],'OGD_card_counts':[24,25],'routes':40,'book_references':33,'support_declaration':SUPPORT,'site_or_pixels_verified':False}
