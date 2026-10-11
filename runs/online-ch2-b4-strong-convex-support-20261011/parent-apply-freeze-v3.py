from pathlib import Path
import argparse,hashlib,json,subprocess,datetime
r=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser();p.add_argument('--head',required=True);p.add_argument('--authorization',required=True);a=p.parse_args()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git','-c','core.longpaths=true',*args],cwd=r)
def state():return {'HEAD':git('rev-parse','HEAD').decode().strip(),'branch':git('branch','--show-current').decode().strip(),'status_hex':git('status','--porcelain=v1','-z').hex()}
d=r/'tmp/online-b4-support-freeze-20261011';planpath=d/'canonical-freeze-plan-v1.json';review=d/'independent-prebody-review-v1.json';authpath=r/a.authorization
assert h(planpath)=='c61d0e61652a3ef3773444269e25a2627743aa6a4751a6b2717e4857f14a9bc3'
assert h(review)=='1cc2c63428d352c7fcfd7d75c0b14a4aac9cc99a05b38f8796024ba456c56207'
plan=json.loads(planpath.read_bytes());auth=json.loads(authpath.read_bytes());pre=state()
assert pre['HEAD']==a.head==auth['application_HEAD'] and pre['status_hex']==''
assert auth['scope']=='CANONICAL_FREEZE_ONLY_NO_BODY' and auth['BODY_authorized'] is False
assert auth['emitter_SHA256']==h(Path(__file__)) and auth['plan_SHA256']==h(planpath) and auth['review_SHA256']==h(review)
roots=[r/x for x in plan['approved_roots_proposed']]
assert len(roots)==2 and all(not x.exists() for x in roots)
# Full original source snapshot continuity to the completed preceding-leaf source gate.
prior=r/'tmp/online-ch2-b4-strong-convex-growth-gates-20261011/full-harness-v3/pre-source-inputs.json'
raw=json.loads(prior.read_bytes())
for row in raw:assert h(r/row['path'])==row['raw_sha256'],row['path']
rows=[]
for x in plan['doc_files']+plan['run_archive_rows']:
 src=x.get('source');source=r/src['path'] if src else planpath
 if src:assert h(source)==src['sha256'] and source.stat().st_size==src['bytes']
 rows.append((source,r/x['destination']))
rows += [(review,roots[1]/'review/independent-prebody-review-v1.json'),(d/'independent-prebody-review-v1.md',roots[1]/'review/independent-prebody-review-v1.md'),(authpath,roots[0]/'parent-freeze-only-authorization-v1.json'),(Path(__file__),roots[1]/'parent-apply-freeze-v3.py')]
for root in roots:rows.append((None,root/'.gitattributes'))
receiptpath=roots[0]/'freeze-application-receipt-v1.json'
allpaths=[dest for _,dest in rows]+[receiptpath]
assert len(allpaths)==len({str(x).lower() for x in allpaths})
for dest in allpaths:
 assert not dest.exists() and any(root==dest.parent or root in dest.parents for root in roots)
 assert r in dest.resolve().parents and not dest.is_symlink()
 for parent in dest.parents:
  if parent==r:break
  assert not parent.is_symlink() and not (parent.exists() and parent.is_junction()),str(parent)
# Validate all content and destinations before create-only mutation.
payloads=[(src,dest,src.read_bytes() if src else plan['preserve_exact_bytes']['attributes_each_root'].encode()) for src,dest in rows]
assert state()==pre
copied=[]
for src,dest,data in payloads:
 dest.parent.mkdir(parents=True,exist_ok=True)
 with dest.open('xb') as f:f.write(data)
 assert h(dest)==hashlib.sha256(data).hexdigest()
 copied.append({'historical_source':str(src.relative_to(r)).replace('\\','/') if src else 'exact-byte attributes literal','destination':str(dest.relative_to(r)).replace('\\','/'),'sha256':h(dest),'bytes':len(data)})
header=roots[0]/'neutral-frozen-header-v1.txt'
receipt={'status':'CANONICAL_FREEZE_APPLIED_NO_BODY_AUTHORIZATION','application_parent_HEAD':a.head,'baseline_gate_source_HEAD':'48ca57cd497a3dcebbeedeb2d54ef3bcefdcd937','authorized_utc':auth['utc'],'copied_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'statement_fingerprint_SHA256':h(header),'plan_SHA256':h(planpath),'review_SHA256':h(review),'authorization_SHA256':h(authpath),'emitter_SHA256':h(Path(__file__)),'prior_gate_RAW_rows_unchanged':len(raw),'rows':copied,'BODY_authorized':False,'chapter2_accepted':False,'Goal':'ACTIVE','receipt_hash_boundary':'Receipt does not recursively hash itself; the subsequent Git commit binds the receipt bytes.'}
with receiptpath.open('x',encoding='utf-8',newline='\n') as f:json.dump(receipt,f,indent=2);f.write('\n')
assert git('rev-parse','HEAD').decode().strip()==a.head
print(json.dumps({'copied_files':len(copied),'receipt':str(receiptpath.relative_to(r)),'receipt_SHA256':h(receiptpath),'statement_fingerprint_SHA256':h(header),'no_BODY':True},indent=2))
