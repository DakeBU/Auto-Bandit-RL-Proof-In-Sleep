from pathlib import Path
import copy,hashlib,json,zipfile
ROOT=Path(__file__).resolve().parents[2];BASE=Path(__file__).resolve().parent
OUT=BASE/'resolution-candidates-v1';OUT.mkdir(exist_ok=False)
def load(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
paths=['BanditRLProof.lean','Tests.lean','tools/test_book_registry.py','website/content/books.json',
 'website/content/chapters.json','website/content/highlights.json','website/content/readings.json']
z=zipfile.ZipFile(ROOT/'tmp/online-ch2-b4-strong-convex-growth-gates-20261011/full-harness-v2/pre-selected-source-raw.zip')
rows=[]
for name in paths:
 raw=z.read(name);candidate=raw;before=None;after=None
 if name=='website/content/books.json':
  before=json.loads(raw);after=copy.deepcopy(before)
  book=next(x for x in after['books'] if x['id']=='online-learning')
  old='extended convexity and supporting gradients';new='extended convexity, closure constructions and supporting gradients'
  assert book['summary'].count(old)==1;book['summary']=book['summary'].replace(old,new)
  assert len(book['chapter_refs'])==len(set(book['chapter_refs'])) and 'teaching:online-convex-closures' in book['chapter_refs']
 if name=='website/content/readings.json':
  before=json.loads(raw);after=copy.deepcopy(before)
  incoming=load(BASE/'incoming-main/website/content/readings.json')
  own={x['slug']:x for x in after['readings']};inc={x['slug']:x for x in incoming['readings']}
  growth='BanditRL.OnlineConvex.stronglyConvex_minimum_growth'
  route=own['online-ogd']['teaching_route'];assert route.count(growth)==1 and len(route)==5
  own['online-ogd']['teaching_route']=[x for x in route if x!=growth]
  assert len(own['online-ogd']['teaching_route'])==4
  assert growth in str(own['online-ogd']['source_theorems']), 'Growth source card remains'
  oldbridge=own['online-convex']['proof_bridge'];newbridge=inc['online-convex']['proof_bridge']
  assert {k:v for k,v in oldbridge.items() if k!='boundary'}=={k:v for k,v in newbridge.items() if k!='boundary'}
  oldbridge['boundary']=newbridge['boundary']
  assert 'proof_bridge' not in own['online-convex-closures']
  own['online-convex-closures']['proof_bridge']=copy.deepcopy(inc['online-convex-closures']['proof_bridge'])
  own['online-convex-closures']['primary']=copy.deepcopy(inc['online-convex-closures']['primary'])
  assert len(own)==len(after['readings'])==40
 if after is not None:candidate=(json.dumps(after,ensure_ascii=False,indent=2)+'\n').encode()
 dest=OUT/name;dest.parent.mkdir(parents=True,exist_ok=True)
 with dest.open('xb') as f:f.write(candidate)
 current=ROOT/name
 conflict_snapshot=BASE/'automatic-merge-working'/name;conflict_snapshot.parent.mkdir(parents=True,exist_ok=True)
 with conflict_snapshot.open('xb') as f:f.write(current.read_bytes())
 rows.append({'source_path':name,'premerge_RAW_sha256':sha(raw),'candidate_path':dest.relative_to(ROOT).as_posix(),
  'candidate_sha256':sha(candidate),'changed_from_premerge_RAW':raw!=candidate,'automatic_merge_snapshot':conflict_snapshot.relative_to(ROOT).as_posix()})
manifest={'parent_HEAD':'cbfb3fd15d2c5e3cbd1063e5d4d595ea2f91b4c5','incoming_main':'1225baf19f8d247ea4b071a3cd4fd7e483b14deb',
 'author':'/root','candidates':rows,'scope':'Resolve seven three-way conflicts/semantic duplicate risks without discarding richer local source; all imported main math modules/canaries already byte-identical in local branch.',
 'exact_semantic_deltas':['Book summary explicitly adds closure constructions; every owned/shared chapter ref preserved without duplicate.',
 'online-ogd curated teaching_route returns to original four; new growth highlight/source-card/declaration/module/Book graph and proof remain. This list is a bounded navigation shortlist, not theorem inventory.',
 'online-convex proof_bridge adopts exactly main boundary wording; all existing bridge steps/source cards unchanged.',
 'online-convex-closures adopts main source primary pp10-11 and full new proof_bridge, including exercise provenance, empty-family convention, general carriers, upper-addition/scalar convention and library-proof attribution. Both preexisting closure source cards stay exact.',
 'Both complete roots, all tests/code, all 503 highlight whole objects/multiplicities and all chapters remain exact premerge RAW; main closure imports and module code already covered. New accepted-main native contract/RUN receipt retained.'],
 'preservation':'All premerge RAW recovered from actual full-harness-v2 ZIP. All original incoming/current Git blobs and automatic merge outputs separately retained. No theorem/hypothesis/target removal.',
 'site_failure':'site-preflight-v2 actual1 receipt2a8a1e297eb11df737cf8db697f34a0dd67b5e2c90a3c4bb3eaef03104415447, cap1-4 unchanged; no checker weakening.',
 'Goal':'ACTIVE','chapter2_accepted':False,'production_applied':False}
p=BASE/'resolution-candidate-manifest-v1.json'
with p.open('x',encoding='utf-8') as f:json.dump(manifest,f,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':sha(p.read_bytes()),'files':len(rows),'changed_from_premerge':[x['source_path'] for x in rows if x['changed_from_premerge_RAW']]},indent=2))
