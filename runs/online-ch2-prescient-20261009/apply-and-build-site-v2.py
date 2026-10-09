from publication_guard_v2 import *
import re
fixed();review=RUN/'reader-link-repair-review-v3.json'
assert sha(review)=='8a19c46c9e007c03b8c3604110c7cfe43e42c52e7601a3bcc5a949afe06b3a0d'
r=load(review);assert not r['required_repairs']
for row in load(RUN/'reader-link-repair-review-inputs-v3.json')['rows']:assert sha(row['path'])==row['sha256']
d=r['approved_materialization'];p=Path(d['mutable_path']);assert sha(p)==d['before_sha256']
p.write_bytes(Path(d['after_snapshot']).read_bytes())
from publication_guard_v3 import fixed as current_fixed,SITE
current_fixed()
probe=load(RUN/'nondegenerate-public-API-values-v1.json');out=base64.b64decode(probe['stdout_base64']).decode('utf8');assert probe['actual_exit']==0
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",out,re.S);assert len(found)==3
for n,ax in found:assert set(re.findall(r'[A-Za-z_.]+',ax))=={'propext','Classical.choice','Quot.sound'}
write(RUN/'nondegenerate-public-API-inspected-v1.json',dict(actual_kernel_exit=0,receipt_sha256=sha(RUN/'nondegenerate-public-API-values-v1.json'),probe_sha256=sha(RUN/'NondegeneratePublicAPIProbe.lean'),actual_axioms=[dict(name=n,axioms=re.findall(r'[A-Za-z_.]+',ax)) for n,ax in found],semantics='Three literal public production VALUE calls at active constrained2rounds: sharp bound-7/2, weaker sourcebound-13/4, actual selected proximal objective with offset3. Uses exact actual Test trajectory/state arithmetic; supplements five public Tests without adding source results or canonical Book nodes.',package_accepted=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'reader-links-applied-v3.json',dict(actual_review_sha256=sha(review),actual_materialization=d,full_compiled_graph_unchanged=True,all_Lean_Test_root_pins_unchanged=True,first_failed_site_receipt_sha256=sha(RUN/'site-build-v1.json'),fresh_output=SITE.as_posix(),site_gate_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
manifest=load(CONTRIBUTION)
manifest['verification']['independent_review']+=' Exact registry-addressability repair reader-link-v3 accepted8a19c46c9e007c03b8c3604110c7cfe43e42c52e7601a3bcc5a949afe06b3a0d: retain actual unaddressable projection/equation constants in text and fullgraph; only broken link entries removed. First actual site failure retained; second actual site pending.'
manifest['verification']['focused_checks'].append('Three additional literal nondegenerate public production VALUE instances at actual clipped2round trajectory and nonzero affineoffset compile, standard-only axioms; these are audit values, not new source theorems/Book nodes.')
CONTRIBUTION.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
stage=load(RUN/'candidate-stage-plan-v1.json')['stage'];subprocess.run(['git','add',*stage],cwd=ROOT,check=True)
code,out=capture('repair-full-package-diff-check-v2','git','diff',BASE,'--check',required=False)
expected={Path(x['path']).relative_to(ROOT).as_posix() for x in load(RUN/'reader-status-and-RAW-review-v2.json')['approved_RAW_EOF_exceptions']}
actual={line.split(':',1)[0] for line in out.splitlines() if ': new blank line at EOF.' in line}
assert code==2 and actual==expected and ': trailing whitespace.' not in out,(code,out)
capture('repair-scoped-package-diff-check-v2','git','diff',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)])
rawrows=[]
for rel in subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines():
    p=ROOT/rel;raw=p.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(p),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-v2.json',dict(rows=rawrows,prior_snapshot_sha256=sha(RUN/'exact-RAW-line-ending-snapshots-v1.json'),scope='Actual new repair staged RAW/blob differences only; earlier25 exact RAW preserved in immutablev1.'))
subprocess.run(['git','add',*stage],cwd=ROOT,check=True)
pending=[]
def clean_capture(label,command):
    command=list(map(str,command));start=time.monotonic();p=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    rec=dict(command=command,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'))
    write(ROOT/'tmp'/(TASK+'-'+label+'.json'),rec);pending.append((label,rec));print(label,'actual exit',p.returncode,flush=True)
    if p.returncode!=0:print(p.stdout.decode('utf8',errors='replace')[-14000:])
    assert p.returncode==0,label
    return p.stdout.decode('utf8',errors='replace')
clean_capture('candidate-repair-commit-v2',['git','commit','-m','Repair prescient reader dependency links with exact provenance'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
for label,base in [('contributor-stack-v2',BASE),('contributor-main-v2','origin/main')]:
    out=clean_capture(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
current_fixed();assert not SITE.exists()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
clean_capture('site-build-v2',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE])
for label,rec in pending:write(RUN/(label+'.json'),rec)
write(RUN/'clean-candidate-site-binding-v2.json',dict(actual_head=head,stacked_base=BASE,actual_clean_at_site_start=True,applicable_full_harness_receipt_sha256=sha(RUN/'full-harness-inspected-v1.json'),two_nonempty_contributor_bases=True,local_site_output=SITE.as_posix(),earlier_failed_site_preserved=True,no_fresh_build_at_later_evidence_head_claim=True,deployed=False,FINAL_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
capture('registry-command-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v3.py')
current_fixed();print('Actual clean repaired site/check/exact registry passed; DOM/pixels/FINAL/native/delivery pending.')
