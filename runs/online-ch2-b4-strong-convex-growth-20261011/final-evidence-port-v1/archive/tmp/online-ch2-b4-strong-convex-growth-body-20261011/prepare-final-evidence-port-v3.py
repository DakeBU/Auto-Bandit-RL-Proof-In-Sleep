from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'tmp/online-ch2-b4-strong-convex-growth-final-port-20261011'
SOURCE_HEAD='48ca57cd497a3dcebbeedeb2d54ef3bcefdcd937'
RUN=ROOT/'runs/online-ch2-b4-strong-convex-growth-20261011'
DEST=RUN/'final-evidence-port-v1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def state():return {k:subprocess.check_output(['git',*v],cwd=ROOT).decode().strip() for k,v in {'HEAD':['rev-parse','HEAD'],'branch':['branch','--show-current'],'status':['status','--porcelain=v1']}.items()}
pre=state();assert pre['HEAD']==SOURCE_HEAD and pre['status']==''
OUT.mkdir(exist_ok=False)
roots=['online-ch2-b4-strong-convex-growth-body-20261011','online-ch2-b4-strong-convex-growth-body-review-20261011',
 'online-ch2-b4-strong-convex-growth-canary-20261011','online-ch2-b4-strong-convex-growth-canary-review-20261011',
 'online-ch2-b4-strong-convex-growth-reader-review-20261011','online-ch2-b4-strong-convex-growth-installed-audit-20261011',
 'online-ch2-b4-strong-convex-growth-gates-20261011','online-main-reconciliation-reader-qa-20261011',
 'online-main-reconciliation-structural-qa-20261011','online-main-reconciliation-helper-independent-review-20261011',
 'online-main-reconciliation-mobile-status-fix-20261011','online-main-reconciliation-gates-20261011',
 'online-main-1225-reconciliation-20261011','online-ch2-b4-strong-convex-growth-push-20261011',
 'online-ch2-b4-strong-convex-growth-final-acceptance-20261011']
catalog={}
for root in (ROOT/'runs/online-main-reconciliation-20261011',RUN):
 for p in sorted(root.rglob('*')):
  if p.is_file():catalog.setdefault((sha(p),p.stat().st_size),p.relative_to(ROOT).as_posix())
rows=[];new=[]
for name in roots:
 for p in sorted((ROOT/'tmp'/name).rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or any(x.startswith('profile-') for x in p.parts):continue
  assert not p.is_symlink() and ROOT in p.resolve().parents
  key=(sha(p),p.stat().st_size);rel=p.relative_to(ROOT).as_posix()
  existing=key in catalog
  if not existing:
   dest=(DEST/'archive'/rel).relative_to(ROOT).as_posix();catalog[key]=dest
   new.append({'source':rel,'destination':dest,'sha256':key[0],'bytes':key[1]})
  rows.append({'historical_source':rel,'canonical_copy':catalog[key],'sha256':key[0],'bytes':key[1],
   'storage':'existing canonical or earlier identical planned copy' if existing else 'new exact unique-byte copy'})
plan={'source_git':pre,'roots':roots,'excluded':['browser profile-* directories (retained locally; contain private browser state)','__pycache__'],
 'port_boundary':'Historical tmp origins remain retained. Canonical copies are later copies, never contemporaneous RUN executions. Every file source/size/SHA and dedup target is explicit.',
 'rows':rows,'new_unique_copies':new,'source_rows':len(rows),'new_unique_files':len(new),'new_bytes':sum(x['bytes'] for x in new),
 'accepted':False,'chapter2_accepted':False,'Goal':'ACTIVE'}
out=OUT/'final-evidence-port-plan-v1.json'
with out.open('x',encoding='utf-8') as f:json.dump(plan,f,ensure_ascii=False,indent=2);f.write('\n')
assert state()==pre
print(json.dumps({'plan':out.relative_to(ROOT).as_posix(),'sha256':sha(out),'source_rows':len(rows),'new_unique_files':len(new),'new_bytes':plan['new_bytes'],'production_changed':False},indent=2))
