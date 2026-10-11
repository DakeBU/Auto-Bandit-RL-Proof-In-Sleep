from pathlib import Path
import datetime,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'tmp/online-ch2-b4-strong-convex-growth-installed-audit-20261011'
BASE.mkdir(exist_ok=False)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def state():return {k:subprocess.check_output(['git',*v],cwd=ROOT).decode().strip() for k,v in {'HEAD':['rev-parse','HEAD'],'branch':['branch','--show-current'],'status':['status','--porcelain=v1']}.items()}
gate=json.loads((ROOT/'tmp/online-ch2-b4-strong-convex-growth-gates-20261011/shared-Tests-v1/receipt.json').read_text(encoding='utf-8'))
assert gate['actual_exit']==0 and gate['capture_integrity_ok']
assert state()['HEAD']=='cf1a424f2312e7c5b730717cf0a96d65837894bd' and state()['status']==''
old=ROOT/'tmp/online-ch2-b4-strong-convex-growth-canary-20261011/PublicProbe.lean'
text=old.read_text(encoding='utf-8')
assert text.count('import Canary')==1
text=text.replace('import Canary','import Tests.OnlineStrongConvexMinimumCanary')
oldout='tmp/online-ch2-b4-strong-convex-growth-canary-20261011/compiled-type-value-v1.json'
newout='tmp/online-ch2-b4-strong-convex-growth-installed-audit-20261011/compiled-type-value-v1.json'
assert text.count(oldout)==1;text=text.replace(oldout,newout)
probe=BASE/'InstalledConsumersProbe-v1.lean';probe.write_text(text,encoding='utf-8')
inputs=[probe,ROOT/'Tests/OnlineStrongConvexMinimumCanary.lean',ROOT/'Tests.lean',ROOT/'BanditRLProof/OnlineStrongConvexMinimum.lean',
 ROOT/'.lake/build/lib/lean/Tests/OnlineStrongConvexMinimumCanary.olean',ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineStrongConvexMinimum.olean']
before={str(p.relative_to(ROOT)):h(p) for p in inputs};gs=state()
argv=['lake','env','lean',str(probe.relative_to(ROOT))]
start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(argv,cwd=ROOT,capture_output=True);end=datetime.datetime.now(datetime.timezone.utc).isoformat()
(BASE/'stdout.raw').write_bytes(p.stdout);(BASE/'stderr.raw').write_bytes(p.stderr)
after={str(p.relative_to(ROOT)):h(p) for p in inputs}
record={'argv':argv,'cwd':str(ROOT),'actual_exit':p.returncode,'start_utc':start,'end_utc':end,'pre_git':gs,'post_git':state(),
 'pre_RAW':before,'post_RAW':after,'inputs_unchanged':before==after,'stdout_sha256':h(BASE/'stdout.raw'),'stderr_sha256':h(BASE/'stderr.raw'),
 'status':'INSTALLED_PUBLIC_CONSUMER_PROBE_ONLY','full_leaf_accepted':False,'Goal':'ACTIVE'}
(BASE/'receipt.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
assert p.returncode==0 and before==after and record['post_git']==gs,p.stdout.decode('utf-8','replace')
actual=json.loads((ROOT/newout).read_text(encoding='utf-8'))
expected=json.loads((ROOT/oldout).read_text(encoding='utf-8'))
assert actual==expected,'Compiled installed TYPE/VALUE differs from reviewed public candidate'
comparison={'actual_exit':0,'installed_TYPE_VALUE_equal_reviewed_candidate':True,'actual_sha256':h(ROOT/newout),'expected_sha256':h(ROOT/oldout),
 'declarations':[r['declaration'] for r in actual],'each_VALUE_contains_core':all('BanditRL.OnlineConvex.stronglyConvex_minimum_growth' in r['VALUE'] for r in actual),
 'receipt_sha256':h(BASE/'receipt.json'),'chapter2_accepted':False,'Goal':'ACTIVE'}
(BASE/'comparison-v1.json').write_text(json.dumps(comparison,indent=2)+'\n',encoding='utf-8');print(json.dumps(comparison,indent=2))
