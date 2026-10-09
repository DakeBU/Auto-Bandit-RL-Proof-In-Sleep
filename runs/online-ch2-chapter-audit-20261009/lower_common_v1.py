from common_v1 import *
import base64
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
PRODUCTION=ROOT/'BanditRLProof/OnlineNonsmoothExamples.lean'
REVIEW_SHA='0695897e40d4c7533cd19c168e528f752ed53d534b8e84007d97745cf4db113e'
REPORT_SHA='15778967012075d7773e1341c76b34213b21cce4b7d9322737356b6eb1c10bc7'
def reviewed():
 fixed()
 assert sha(RUN/'source-contract-repair-review-v1.json')==REVIEW_SHA
 assert sha(RUN/'source-contract-repair-review-v1.md')==REPORT_SHA
 r=load(RUN/'source-contract-repair-review-v1.json')
 assert not r['required_blocking_repairs'] and not r['required_mathematical_repairs']
 assert r['source_inventory_verdict']['sha256']==sha(CONTRACT/'complete-source-reconciliation-draft-v3.json')
 for q in r['raw_input_checks']:
  assert sha(q['path'])==q['before_sha256']==q['after_sha256'],q['path']
 d=load(CONTRACT/'nonsmooth-targets-draft-v1.json')
 assert [t['statement_hash'] for t in d['targets']]==[t['statement_hash'] for t in r['target_verdicts']]
 return d
def capture(label,*args,required=True):
 tick=time.monotonic();p=subprocess.run(list(map(str,args)),cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(RUN/(label+'.json'),dict(command=list(map(str,args)),cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-tick,
  stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 print(label,'actual exit',p.returncode,flush=True)
 if required:assert p.returncode==0,label
 return p.returncode,p.stdout.decode('utf8',errors='replace')
def event(label,event,payload):
 return capture(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','lifecycle-event','--session',TASK,'--event',event,'--payload-json',json.dumps(payload,separators=(',',':')))
def headers(count):
 d=reviewed();result=[]
 for t in d['targets'][:count]:
  h=lean_declaration_header(PRODUCTION,t['declaration'])
  assert statement_hash(h)==t['statement_hash'],t['declaration']
  result.append(dict(declaration=t['declaration'],native_header=h,statement_hash=statement_hash(h)))
 return result
