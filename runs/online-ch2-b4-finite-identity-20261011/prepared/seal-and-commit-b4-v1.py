import hashlib,json,subprocess
from datetime import datetime,timezone
from pathlib import Path

ROOT=Path.cwd();DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1');RUN=Path('runs/online-ch2-b4-finite-identity-20261011');OUT=Path('tmp/online-ch2-b4-finite-identity-freeze-commit-20261011')
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def put(p,b):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),str(p);p.write_bytes(b)
def js(p,o):put(p,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
def row(p):p=Path(p);b=p.read_bytes();return {'path':p.as_posix(),'sha256':sha(b),'bytes':len(b)}
def command(tag,argv):
 start=now();r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 put(OUT/(tag+'.stdout.raw'),r.stdout);put(OUT/(tag+'.stderr.raw'),r.stderr)
 js(OUT/(tag+'.receipt.json'),{'argv':argv,'cwd':str(ROOT),'startUTC':start,'endUTC':now(),'actual_exit':r.returncode,'stdout_sha256':sha(r.stdout),'stderr_sha256':sha(r.stderr)})
 assert r.returncode==0,(tag,r.returncode);return r.stdout
reviewdir=Path('tmp/online-ch2-b4-finite-identity-freeze-review-20261011')
contract_review=json.loads((reviewdir/'fresh-independent-contract-freeze-review-v1.json').read_bytes())
assert contract_review['verdict']=='accepted-for-bounded-contract-freeze-only' and not contract_review['blocking_repairs']
assert contract_review['approved_contract_sha256']==sha((DOC/'source-contract-proposal-v1.json').read_bytes())
helper_review=json.loads((reviewdir/'prepared-preproof-helper-review-v3.json').read_bytes())
assert 'accepted' in helper_review['verdict'] and not helper_review.get('blocking_repairs',[])
assert sha(Path('tmp/capture-b4-preproof-context-v3.py').read_bytes())=='1dbe6223983e06367405b6c20e37a88ea001d545b1383748f6e7b071d2d47efa'
assert command('HEAD-before',['git','rev-parse','HEAD']).decode().strip()=='b8a4b13ca96709b1adff0d1907814dc3d3d76cc8'
assert command('branch-before',['git','branch','--show-current']).decode().strip()=='codex/research-online-ch2-b4-finite-identity'
assert not command('tracked-diff-before',['git','diff','--name-only'])
assert not command('staged-diff-before',['git','diff','--cached','--name-only'])
assert not Path('BanditRLProof/OnlineCumulativePotential.lean').exists() and not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
ports=[]
for p in sorted(reviewdir.glob('*')):
 if p.is_file():
  q=RUN/'independent-freeze'/p.name;put(q,p.read_bytes());ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size})
js(RUN/'independent-freeze-port-v1.json',{'UTC':now(),'rows':ports,'exact_bytes_verified':all(Path(x['original']).read_bytes()==Path(x['destination']).read_bytes() for x in ports),'self_excluded':True})
put(RUN/'prepared/seal-and-commit-b4-v1.py',Path(__file__).read_bytes())
frozen=[row(p) for folder in [DOC,RUN] for p in sorted(folder.rglob('*')) if p.is_file()]
seal={'UTC':now(),'task':'ONLINE-CH2-B4-FINITE-IDENTITY-20261011','decision':'STATEMENT_SEALED and SOURCE_TOPOLOGY_REVIEWED for exact finite-real algebra subclause before any BODY; prospective proof authorization remains separate','pre_freeze_HEAD':'b8a4b13ca96709b1adff0d1907814dc3d3d76cc8','branch':'codex/research-online-ch2-b4-finite-identity','requested_model_effort':'GPT-6 Astra / medium; runtime not independently attested','frozen_inputs':frozen,'independent_contract_review':row(RUN/'independent-freeze/fresh-independent-contract-freeze-review-v1.json'),'independent_prepared_helper_review':row(RUN/'independent-freeze/prepared-preproof-helper-review-v3.json'),'exact_header_sha256':'92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67','source_topology_sha256':'d7d6051f3788797b53a19d5d80f163bdca80491281ec13be998b4c2d106ad8bc','sole_public_declaration':'BanditRL.OnlineCumulativePotential.finite_regret_identity','planned_core':'BanditRLProof/OnlineCumulativePotential.lean','semantic_scope':'Arbitrary carrier; total real psi/loss; exact inclusive cumulative identity with arbitrary unscored terminal splice and full terminal gap; positive T. No new public proof ingredients as assumptions.','both_whole_parent_repairs':'OPEN; frozen original parent rows preserved, no whole7.47/15.31 performance bound accepted.','canaries':'Only ignored future proposals; require distinct blind/source reviews, exact later freeze after production BODY acceptance and clean pre-canary context before Test BODY.','current':{'required_open_forward_containers':7,'future_claims_open':6,'chapter2_status':'partial','chapter2_accepted':False,'mandatory_count':None,'Goal':'ACTIVE'},'purification':'pending','authorization':'Parent must capture actual clean committed preproof context, obtain independent verification then explicitly authorize production BODY. This receipt alone gives no BODY authority.'}
js(DOC/'leaf-freeze-receipt-v1.json',seal)
command('git-add',['git','add','--',DOC.as_posix(),RUN.as_posix()])
names=command('staged-files',['git','diff','--cached','--name-only','-z']).decode().split('\0');names=[n for n in names if n]
assert names and all(n.startswith(DOC.as_posix()+'/') or n.startswith(RUN.as_posix()+'/') for n in names)
stage_rows=[]
for n in names:
 raw=Path(n).read_bytes();stage=subprocess.check_output(['git','show',':'+n]);assert raw==stage,n
 stage_rows.append({'path':n,'sha256':sha(raw),'RAW_equal_staged':True})
js(OUT/'stage-byte-audit-v1.json',stage_rows)
command('diff-check',['git','diff','--cached','--check'])
command('commit',['git','commit','-m','Seal finite cumulative-potential identity before proof'])
head=command('HEAD-after',['git','rev-parse','HEAD']).decode().strip()
assert command('status-after',['git','status','--porcelain'])==b''
js(OUT/'receipt.json',{'UTC':now(),'HEAD':head,'branch':'codex/research-online-ch2-b4-finite-identity','staged_files':len(names),'all_RAW_equal_stage':True,'diff_check_exit':0,'clean_after':True,'seal':row(DOC/'leaf-freeze-receipt-v1.json'),'core_and_canary_absent':True,'authorization':'Freeze committed only. No BODY authority until actual preproof independent verification.'})
print('freeze-committed',head,'files',len(names),'sealSHA',sha((DOC/'leaf-freeze-receipt-v1.json').read_bytes()))
