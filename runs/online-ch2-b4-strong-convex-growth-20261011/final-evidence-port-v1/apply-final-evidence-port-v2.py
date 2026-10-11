from pathlib import Path
import hashlib,json,subprocess,datetime,os
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'tmp/online-ch2-b4-strong-convex-growth-final-port-20261011'
PLAN=OUT/'final-evidence-port-plan-v2.json'
RUN=ROOT/'runs/online-ch2-b4-strong-convex-growth-20261011/final-evidence-port-v1'
def lp(p):
 prefix=chr(92)*2+'?'+chr(92);s=str(p.resolve())
 return Path(s if s.startswith(prefix) or os.name!='nt' else prefix+s)
def sha(p):return hashlib.sha256(lp(p).read_bytes()).hexdigest()
plan=json.loads(PLAN.read_bytes());source='48ca57cd497a3dcebbeedeb2d54ef3bcefdcd937'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip()==plan['source_git']['HEAD']==source
assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=ROOT)
review=ROOT/'tmp/online-ch2-b4-strong-convex-growth-final-acceptance-20261011/final-independent-leaf-review-v1.json'
assert sha(review)=='f805ab755a985e4d4c55e1995c4b041c7ba87573605689062928d2ae06b5a4ae'
v=json.loads(review.read_bytes());assert v['blockers']==[] and v['verdict']=='PASS_BOUNDED_MINIMUM_GROWTH_LEAF_ACCEPTANCE'
rows=plan['new_unique_copies'];destinations={x['destination'] for x in rows};expected={x['destination']:x for x in rows}
assert len(rows)==len({x['destination'].lower() for x in rows})
existing=[]
for q in lp(RUN).rglob('*'):
 if not q.is_file():continue
 normal=RUN/q.relative_to(lp(RUN));name=normal.relative_to(ROOT).as_posix();assert name in expected,name
 row=expected[name];assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256'] and q.stat().st_size==row['bytes'];existing.append(name)
for x in rows:
 src=ROOT/x['source'];dst=ROOT/x['destination']
 assert sha(src)==x['sha256'] and lp(src).stat().st_size==x['bytes']
 assert RUN in dst.parents and ROOT in dst.resolve().parents
 assert not any(t.startswith('profile-') for t in src.parts)
 assert x['bytes']<100_000_000
 if lp(dst).exists():assert sha(dst)==x['sha256'] and lp(dst).stat().st_size==x['bytes']
for x in plan['rows']:
 if x['canonical_copy'] not in destinations:
  p=ROOT/x['canonical_copy'];assert sha(p)==x['sha256'] and lp(p).stat().st_size==x['bytes']
created=0
for x in rows:
 src=ROOT/x['source'];dst=ROOT/x['destination']
 if lp(dst).exists():continue
 lp(dst.parent).mkdir(parents=True,exist_ok=True)
 with lp(dst).open('xb') as f:f.write(lp(src).read_bytes())
 assert sha(dst)==x['sha256'];created+=1
for label,file in [('v1',OUT/'final-evidence-port-plan-v1.json'),('v2',PLAN)]:
 with lp(RUN/('exact-port-manifest-'+label+'.json')).open('xb') as f:f.write(file.read_bytes())
record={'applied_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_HEAD':source,'plan_SHA256':sha(PLAN),'emitter_SHA256':sha(Path(__file__)),'independent_leaf_review_SHA256':sha(review),'new_unique_files':len(rows),'existing_exact_files_retained':len(existing),'missing_files_created':created,'all_port_rows':len(plan['rows']),'exact_copy_verified':True,'long_path_v1_actual_failure_retained':True,'not_contemporaneous_run_origins':True,'profiles_retained_locally_not_exported':True,'production_changed':False,'chapter2_accepted':False,'Goal':'ACTIVE'}
with lp(RUN/'port-application-receipt-v2.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
with lp(RUN/'apply-final-evidence-port-v2.py').open('xb') as f:f.write(Path(__file__).read_bytes())
print(json.dumps(record,indent=2))
