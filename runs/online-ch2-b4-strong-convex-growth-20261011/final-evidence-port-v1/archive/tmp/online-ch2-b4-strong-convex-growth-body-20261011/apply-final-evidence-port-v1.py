from pathlib import Path
import hashlib,json,subprocess,datetime
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'tmp/online-ch2-b4-strong-convex-growth-final-port-20261011'
PLAN=OUT/'final-evidence-port-plan-v1.json'
RUN=ROOT/'runs/online-ch2-b4-strong-convex-growth-20261011/final-evidence-port-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads(PLAN.read_bytes())
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip()==plan['source_git']['HEAD']=='48ca57cd497a3dcebbeedeb2d54ef3bcefdcd937'
assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=ROOT)
assert not RUN.exists()
review=ROOT/'tmp/online-ch2-b4-strong-convex-growth-final-acceptance-20261011/final-independent-leaf-review-v1.json'
assert review.exists()
rows=plan['new_unique_copies']
assert len(rows)==len({x['destination'].lower() for x in rows})
for x in rows:
 src=ROOT/x['source'];dst=ROOT/x['destination']
 assert sha(src)==x['sha256'] and src.stat().st_size==x['bytes']
 assert RUN in dst.parents and ROOT in dst.resolve().parents and not dst.exists()
 assert not any(t.startswith('profile-') for t in src.parts)
 assert x['bytes']<100_000_000,'A file would exceed GitHub single-file limits'
for x in plan['rows']:
 if x['canonical_copy'] not in {v['destination'] for v in rows}:
  p=ROOT/x['canonical_copy'];assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes']
for x in rows:
 src=ROOT/x['source'];dst=ROOT/x['destination'];dst.parent.mkdir(parents=True,exist_ok=True)
 with dst.open('xb') as f:f.write(src.read_bytes())
 assert sha(dst)==x['sha256']
RUN.mkdir(parents=True,exist_ok=True)
with (RUN/'exact-port-manifest-v1.json').open('xb') as f:f.write(PLAN.read_bytes())
record={'applied_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_HEAD':plan['source_git']['HEAD'],'plan_SHA256':sha(PLAN),'emitter_SHA256':sha(Path(__file__)),'independent_leaf_review_SHA256':sha(review),'new_unique_files':len(rows),'all_port_rows':len(plan['rows']),'exact_copy_verified':True,'not_contemporaneous_run_origins':True,'profiles_retained_locally_not_exported':True,'production_changed':False,'chapter2_accepted':False,'Goal':'ACTIVE'}
with (RUN/'port-application-receipt-v1.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
with (RUN/'apply-final-evidence-port-v1.py').open('xb') as f:f.write(Path(__file__).read_bytes())
print(json.dumps(record,indent=2))
