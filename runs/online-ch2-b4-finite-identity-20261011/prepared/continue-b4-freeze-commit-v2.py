import hashlib,json,subprocess
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path.cwd();DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1');RUN=Path('runs/online-ch2-b4-finite-identity-20261011');OUT=Path('tmp/online-ch2-b4-finite-identity-freeze-commit-v2-20261011')
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def put(p,b):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),str(p);p.write_bytes(b)
def js(p,o):put(p,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
def cmd(tag,argv):
 start=now();r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 put(OUT/(tag+'.stdout.raw'),r.stdout);put(OUT/(tag+'.stderr.raw'),r.stderr);js(OUT/(tag+'.receipt.json'),{'argv':argv,'cwd':str(ROOT),'startUTC':start,'endUTC':now(),'actual_exit':r.returncode,'stdout_sha256':sha(r.stdout),'stderr_sha256':sha(r.stderr)})
 assert r.returncode==0,(tag,r.returncode);return r.stdout
seal=json.loads((DOC/'leaf-freeze-receipt-v1.json').read_bytes())
assert all(sha(Path(r['path']).read_bytes())==r['sha256'] for r in seal['frozen_inputs'])
assert subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()=='b8a4b13ca96709b1adff0d1907814dc3d3d76cc8'
repair=RUN/'byte-preserving-diff-repair-v1'
put(repair/'.gitattributes',b'* -text\n*.raw -diff\n')
ports=[]
src=Path('tmp/online-ch2-b4-finite-identity-freeze-commit-20261011')
for p in sorted(src.glob('*')):
 if p.is_file():
  q=repair/'actual-failed-freeze-stage-v1'/p.name;put(q,p.read_bytes());ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p.read_bytes())})
put(RUN/'header-proposal/.gitattributes',b'# Captured raw streams retain exact bytes, including CRLF.\n*.raw -diff\n')
put(RUN/'prepared/continue-b4-freeze-commit-v2.py',Path(__file__).read_bytes())
js(repair/'receipt.json',{'UTC':now(),'failure_class':'ENV_BLOCKED','actual_failed_command':['git','diff','--cached','--check'],'actual_exit':2,'reason':'Captured read-only retrieval stdout has original CRLF; whitespace lint treats CR as trailing whitespace. Preserve exact stream bytes instead of normalizing captured evidence.','ports':ports,'seal_v1_unchanged_sha256':sha((DOC/'leaf-freeze-receipt-v1.json').read_bytes()),'all_v1_frozen_input_hashes_unchanged':True,'repair':'Two new scoped .gitattributes files mark only captured *.raw as non-diff text, inheriting -text byte preservation. No existing frozen file changed. Exact RAW versus staged verification still mandatory for every own file.','new_transport_attribute':'runs/online-ch2-b4-finite-identity-20261011/header-proposal/.gitattributes','mathematical_header_source_or_BODY_change':False,'salvage':'All original failure streams/actual exit/stage-byte audit retained; no discarded mathematical or tooling evidence. New transport files/addendum captured in full actual preproof context and independently reviewed before BODY.'})
cmd('git-add',['git','add','--',DOC.as_posix(),RUN.as_posix()])
names=[x for x in cmd('staged-files',['git','diff','--cached','--name-only','-z']).decode().split('\0') if x]
assert names and all(x.startswith(DOC.as_posix()+'/') or x.startswith(RUN.as_posix()+'/') for x in names)
audit=[]
for n in names:
 b=Path(n).read_bytes();assert b==subprocess.check_output(['git','show',':'+n]),n;audit.append({'path':n,'sha256':sha(b),'RAW_equal_staged':True})
js(OUT/'stage-byte-audit-v2.json',audit)
assert all(sha(Path(r['path']).read_bytes())==r['sha256'] for r in seal['frozen_inputs'])
cmd('diff-check',['git','diff','--cached','--check'])
cmd('commit',['git','commit','-m','Seal finite cumulative-potential identity before proof'])
head=cmd('HEAD-after',['git','rev-parse','HEAD']).decode().strip()
assert cmd('status-after',['git','status','--porcelain'])==b''
js(OUT/'receipt.json',{'UTC':now(),'HEAD':head,'files':len(names),'all_RAW_equal_stage':True,'all_original_seal_inputs_unchanged':True,'diff_check_exit':0,'clean_after':True,'core_and_canary_absent':not Path('BanditRLProof/OnlineCumulativePotential.lean').exists() and not Path('Tests/OnlineCumulativePotentialCanary.lean').exists(),'authorization':'No BODY until actual clean preproof context and independent review.'})
print('freeze-committed',head,'files',len(names),'sealSHA',sha((DOC/'leaf-freeze-receipt-v1.json').read_bytes()))
