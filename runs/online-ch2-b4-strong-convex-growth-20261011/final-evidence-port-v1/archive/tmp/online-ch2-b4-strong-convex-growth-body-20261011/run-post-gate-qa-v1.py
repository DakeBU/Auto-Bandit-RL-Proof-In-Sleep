from pathlib import Path
import datetime,hashlib,json,subprocess,sys,urllib.request
ROOT=Path(__file__).resolve().parents[2]
HEAD='cf1a424f2312e7c5b730717cf0a96d65837894bd'
GATES=ROOT/'tmp/online-ch2-b4-strong-convex-growth-gates-20261011'
SITE=ROOT/'tmp/online-ch2-b4-strong-convex-growth-site-20261011-v1'
QA=ROOT/'tmp/online-main-reconciliation-reader-qa-20261011'
STRUCT=ROOT/'tmp/online-main-reconciliation-structural-qa-20261011'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def state():return {k:subprocess.check_output(['git',*v],cwd=ROOT).decode().strip() for k,v in {'HEAD':['rev-parse','HEAD'],'branch':['branch','--show-current'],'status':['status','--porcelain=v1']}.items()}
summary=load(GATES/'parent-nine-gates-summary-v1.json')
assert len(summary['gates'])==9 and all(x['actual_exit']==0 and x['capture_integrity_ok'] and x['HEAD']==HEAD for x in summary['gates'])
assert state()['HEAD']==HEAD and state()['status']==''
gate=GATES/'full-harness-v1/receipt.json'
reviews=ROOT/'tmp/online-main-reconciliation-helper-independent-review-20261011'
assert h(reviews/'independent-helper-review-v6.json')=='e158ce7bca18e57e4d7ed7abfe5ec75504607aea7d2f9df76a550dcbf46aec8b'
assert not load(reviews/'independent-helper-review-v6.json')['blockers']
assert h(reviews/'independent-structural-v4-review-v1.json')=='9701b627fa4fadef1dd3581de131951d75d65ecaa3bceecc3d743984d2faa14d'
assert not load(reviews/'independent-structural-v4-review-v1.json')['blockers']
def run(argv,base,label,helper,review):
 pre=state();start=datetime.datetime.now(datetime.timezone.utc).isoformat()
 proc=subprocess.run(argv,cwd=ROOT,capture_output=True)
 end=datetime.datetime.now(datetime.timezone.utc).isoformat();post=state()
 out=base/(label+'.stdout.raw');err=base/(label+'.stderr.raw')
 with out.open('xb') as f:f.write(proc.stdout)
 with err.open('xb') as f:f.write(proc.stderr)
 row={'argv':argv,'start_utc':start,'end_utc':end,'actual_exit_code':proc.returncode,'helper_sha256':h(helper),
  'independent_review_sha256':h(review),'pre_git':pre,'post_git':post,'input_git_unchanged':pre==post,
  'stdout_sha256':h(out),'stderr_sha256':h(err),'scope':'Actual local QA only. Original-pixel/final semantic adjudication remain separate; no live or chapter acceptance.'}
 receipt=base/(label+'.json')
 with receipt.open('x',encoding='utf-8') as f:json.dump(row,f,indent=2);f.write('\n')
 print(json.dumps({'label':label,'actual_exit':proc.returncode,'receipt_sha256':h(receipt)}),flush=True)
 assert pre==post and proc.returncode==0,proc.stderr.decode('utf-8','replace')
checker=STRUCT/'check-reconciliation-structure-v4.py';spec=STRUCT/'input-spec-execution-v5.json'
assert h(checker)=='22a27138cb7855c2ee0fcb2e3d98036bf611d5286df1439d1ed63040ab0f9a76'
assert h(spec)=='6626e16dbb3d21d33647d16aaf38e5dae766d0348998ba8ca7400ab5d74536eb'
run([sys.executable,'-B','-X','utf8',str(checker),'--root',str(ROOT),
 '--baseline',str(ROOT/'tmp/online-ch2-b4-finite-identity-site-20261011-v1/books/registry.json'),
 '--site',str(SITE),'--gate',str(gate),'--spec',str(spec),'--output',str(STRUCT/'actual-growth-v1.json'),
 '--spec-sha256',h(spec),'--gate-sha256',h(gate),'--head',HEAD],STRUCT,'execution-receipt-growth-v1',checker,reviews/'independent-structural-v4-review-v1.json')
url='http://127.0.0.1:8895/chapters/online-ogd/'
with urllib.request.urlopen(url,timeout=10) as response:served=response.read()
assert served==(SITE/'chapters/online-ogd/index.html').read_bytes(),'Local server does not serve actual new-source site'
helper=QA/'capture-reconciliation-reader-v11.cjs'
assert h(helper)=='b4702922b98007ad1dedeadb2c5d60771975d8575cb057c9cb062fbcc2a5844a'
run(['C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe',str(helper),url,
 str(QA/'actual-growth-v1'),str(QA/'profile-growth-v1'),str(SITE/'books/registry.json'),str(ROOT),str(SITE),str(gate),h(gate),HEAD],
 QA,'execution-receipt-growth-v1',helper,reviews/'independent-helper-review-v6.json')
print('STRUCTURAL_AND_ACTUAL_READER_CAPTURE_PASSED_NOT_FINAL_ACCEPTANCE',flush=True)
