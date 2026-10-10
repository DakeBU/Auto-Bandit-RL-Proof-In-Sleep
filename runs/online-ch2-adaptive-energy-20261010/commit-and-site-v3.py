from common import *
import re

TEST=ROOT/'Tests/OnlineAdaptiveEnergyCanary.lean'
SITE=ROOT/'tmp/online-ch2-adaptive-energy-site-v1'
DELIVERY=ROOT/'tmp/online-ch2-adaptive-energy-candidate-v3'
assert not SITE.exists() and not DELIVERY.exists()
assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
format_review=load(RUN/'CRLF-format-review-v1.json')
assert format_review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not format_review['required_repairs']
assert sha(format_review['report'])==format_review['report_sha256']
assert format_review['approved_plan_sha256']==sha(RUN/'CRLF-format-plan-v1.json')
format_plan=load(RUN/'CRLF-format-plan-v1.json')
assert sha(format_plan['path'])==format_plan['after_sha256']==sha(format_plan['after_snapshot'])
for row in format_plan['unchanged_metadata']: assert sha(row['path'])==row['sha256']
doc_review=load(RUN/'native-doc-LF-review-v1.json')
assert doc_review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not doc_review['required_repairs']
assert sha(doc_review['report'])==doc_review['report_sha256']
assert doc_review['approved_plan_sha256']==sha(RUN/'native-doc-LF-plan-v1.json')
for row in load(RUN/'native-doc-LF-plan-v1.json')['rows']:
    assert sha(row['path'])==row['after_sha256']==sha(row['after_snapshot'])
    assert Path(row['path']).read_bytes()==base64.b64decode(row['before_RAW_base64']).replace(b'\r\n',b'\n')
plan=load(CONTRACT/'exact-integration-plan-v2.json')
r=load(RUN/'integration-review-v1.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
assert sha(r['report'])==r['report_sha256'] and r['approved_plan_sha256']==sha(CONTRACT/'exact-integration-plan-v2.json')
for row in plan['rows']:
    assert sha(row['path'])==row['after_sha256']==sha(row['after_snapshot'])
assert sha(PUBLIC)==plan['production_sha256'] and sha(TEST)==plan['Test_sha256']
assert sha(ROOT/plan['new_manifest'])==plan['prospective_manifest_sha256']
eof=load(RUN/'EOF-repair-review-v1.json')
assert eof['verdict'] in ['accepted','accepted-with-explicit-delta'] and not eof['required_repairs']
assert sha(eof['report'])==eof['report_sha256'] and eof['approved_plan_sha256']==sha(RUN/'EOF-repair-plan-v1.json')
for row in load(RUN/'EOF-repair-plan-v1.json')['rows']:
    raw=base64.b64decode(row['before_RAW_base64'])
    assert hashlib.sha256(raw).hexdigest()==row['before_sha256']
    assert Path(row['path']).read_bytes()==raw[:-1]
    assert sha(row['path'])==row['after_sha256']==sha(row['after_snapshot'])
gate=load(RUN/'full-harness-inspected-v1.json')
assert gate['actual_exit']==0 and gate['actual_check_passed'] and gate['actual_ProofGraphExport_compile_present']
receipt=RUN/'combined-full-harness-v1.json'
assert sha(receipt)==gate['command_receipt_sha256']
actual=load(receipt);outbytes=base64.b64decode(actual['stdout_base64']);out=outbytes.decode('utf8')
assert actual['actual_exit']==0 and actual['command'][-2:]==['tools/bandit.py','check'] and actual['cwd']==ROOT.as_posix()
assert hashlib.sha256(outbytes).hexdigest()==actual['stdout_sha256']
assert 'check passed' in out and 'tools/ProofGraphExport.lean' in out
assert re.search(r'Build completed successfully \(\d+ jobs\)',out) and re.search(r'Ran \d+ tests in ',out) and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out)
assert all(s not in out for s in ['error: build failed','Lean exited with code 1','forbidden placeholder scan failed'])
for key,p in [('production_sha256',PUBLIC),('Test_sha256',TEST),('root_sha256',ROOT/'BanditRLProof.lean'),('Test_root_sha256',ROOT/'Tests.lean')]: assert sha(p)==gate[key]
for p,h in gate['source_pins'].items(): assert sha(ROOT/p)==h
roots=load(RUN/'combined-root-Tests-inspected-v1.json')
assert roots['root_Tests_passed'] and {x['target'] for x in roots['rows']}=={'BanditRLProof','Tests'}
for row in roots['rows']:
    assert row['actual_exit']==0 and row['cached_inclusive_jobs']
    rp=RUN/('combined-root-v1.json' if row['target']=='BanditRLProof' else 'combined-Tests-v1.json')
    assert sha(rp)==row['receipt_sha256'] and load(rp)['actual_exit']==0

scope=[str(PUBLIC.relative_to(ROOT)).replace('\\','/'),str(TEST.relative_to(ROOT)).replace('\\','/'),
       'conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','tasks/'+TASK+'.md',
       'research-wiki/retrieval-index/'+TASK+'.md',plan['new_manifest'],
       RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix()]+plan['old_allowed']
def allowed(p): return any(p==s or p.startswith(s+'/') for s in scope)
status=subprocess.check_output(['git','status','--porcelain=v1','-z']).decode('utf8').split('\0')
for entry in status:
    if entry:
        assert entry[:2] in [' M','M ','MM','A ','AM','??'],entry
        assert allowed(entry[3:].rstrip('/')),entry
DELIVERY.mkdir(parents=True)
def tmpcapture(label,*args):
    t=time.monotonic();p=subprocess.run(list(map(str,args)),cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    write(DELIVERY/(label+'.json'),dict(command=list(map(str,args)),cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-t,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
    assert p.returncode==0,(label,p.stdout.decode('utf8',errors='replace'))
    print(label,'actual exit',p.returncode,flush=True)
    return p.stdout
capture('candidate-scoped-stage-v3','git','add','--',*scope)
capture('candidate-fullBASE-whitespace-v3','git','diff','--check',BASE)
tmpcapture('candidate-scoped-stage-final-v3','git','add','--',*scope)
changed=subprocess.check_output(['git','diff','--cached','--name-only','-z',BASE]).decode('utf8').split('\0')
staged=[]
for p in filter(None,changed):
    assert allowed(p),p
    blob=subprocess.check_output(['git','show',':'+p]);raw=(ROOT/p).read_bytes()
    assert blob==raw,p
    staged.append(dict(path=p,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),index_equals_RAW=True))
assert PUBLIC.relative_to(ROOT).as_posix() in [x['path'] for x in staged]
tmpcapture('candidate-commit-v3','git','commit','-m','feat(online): prove adaptive cumulative energy bound with zero prefixes')
head=tmpcapture('candidate-head-v3','git','rev-parse','HEAD').decode().strip()
assert tmpcapture('candidate-clean-status-v3','git','status','--porcelain=v1','-z')==b''
binding=dict(actual_head=head,stacked_base=BASE,actual_clean_at_site_start=True,
    applicable_full_harness_receipt_sha256=sha(receipt),production_sha256=sha(PUBLIC),Test_sha256=sha(TEST),
    all_staged_blobs=staged,local_site_output=SITE.as_posix(),new_helper_execution_hashes=rows([RUN/'integration_guard_v1.py',RUN/'apply-integration-v1.py',Path(__file__).resolve()]),
    EOF_original_execution_transition=sha(RUN/'EOF-repair-plan-v1.json'),deployed=False,chapter_complete=False,whole_Goal='active')
write(DELIVERY/'clean-site-start-binding-v1.json',binding)
capture('site-build-v1',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE)
m=load(SITE/'site-manifest.json')
assert m['lean_verified'] and not m['source_dirty'] and m['source_commit']==head
write(RUN/'clean-candidate-site-binding-v1.json',binding)
capture('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
for label,base in [('contributor-stack-candidate-v1',BASE),('contributor-main-candidate-v1','origin/main')]:
    code,out=capture(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base,required=False)
    assert code==0 and 'OnlineAdaptiveEnergy.lean' in out and 'not applicable' not in out.lower(),out
print('Ordinary source candidate committed; clean local lean-verified site and two NONEMPTY committed contributor checks passed.',flush=True)
