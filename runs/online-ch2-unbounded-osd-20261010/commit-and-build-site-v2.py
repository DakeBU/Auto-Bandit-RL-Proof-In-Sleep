from publication_guard_v2 import *
fixed()
assert load(RUN/'full-harness-inspected-v1.json')['actual_check_passed']
assert load(RUN/'shadow-inspected-v1.json')['actual_report']['mismatches']==[]
stage=[PUBLIC.relative_to(ROOT).as_posix(),TEST.relative_to(ROOT).as_posix(),
 'BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix()]
stage += [d+'/'+TASK+'.md' for d in ['conversion-windows','proof-obligations','research-wiki/retrieval-index']]
assert load(RUN/'candidate-stage-plan-v1.json')['stage']==stage
capture('candidate-stage-v2','git','add',*stage)
changed=subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines()
baseline={Path(r['path']).relative_to(ROOT).as_posix() for r in load(RUN/'baseline-v1.json')['rows']}
allowed={Path(r['path']).relative_to(ROOT).as_posix() for r in load(CONTRACT/'exact-publication-plan-v1.json')['rows']}
assert set(changed)&baseline==allowed
for path in changed:assert any(path==a or path.startswith(a+'/') for a in stage),path
capture('candidate-full-package-diff-v2','git','diff','--cached',BASE,'--check')
rawrows=[]
for rel in changed:
    p=ROOT/rel;raw=p.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(p),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-candidate-v2.json',dict(rows=rawrows,scope='Exact RAW bytes differing from Git LF filtering, not reserialization.'))
write(RUN/'candidate-diff-audit-v2.json',dict(actual_full_whitespace_exit=0,changed_paths=changed,only_five_old_paths_changed=True,all_other_baseline_immutable=True))
pending=[]
def clean_capture(label,args):
    start=time.monotonic();args=list(map(str,args));p=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    rec=dict(command=args,cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'))
    write(ROOT/'tmp'/(TASK+'-'+label+'.json'),rec);pending.append((label,rec))
    print(label,'actual exit',p.returncode,flush=True)
    assert p.returncode==0,(label,p.stdout.decode('utf8',errors='replace')[-16000:])
    return p.stdout.decode('utf8',errors='replace')
clean_capture('candidate-final-stage-v1',['git','add',*stage])
assert not subprocess.check_output(['git','diff','--name-only'],encoding='utf8').strip()
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard'],encoding='utf8').strip()
clean_capture('candidate-final-diff-v1',['git','diff','--cached',BASE,'--check'])
clean_capture('candidate-commit-v1',['git','commit','-m','Prove causal unbounded OSD lower bound and source coefficient'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
for label,base in [('contributor-stack-v1',BASE),('contributor-main-v1','origin/main')]:
    out=clean_capture(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
fixed();assert not SITE.exists()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
clean_capture('site-build-v1',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',SITE])
for label,rec in pending:write(RUN/(label+'.json'),rec)
write(RUN/'clean-candidate-site-binding-v1.json',dict(actual_head=head,stacked_base=BASE,actual_clean_at_site_start=True,
    applicable_full_harness_receipt_sha256=sha(RUN/'full-harness-inspected-v1.json'),production_sha256=sha(PUBLIC),Test_sha256=sha(TEST),
    two_nonempty_contributor_bases=True,local_site_output=SITE.as_posix(),fresh_site_at_later_evidence_head=False,deployed=False,FINAL_pending=True,chapter_complete=False,whole_Goal='ACTIVE'))
capture('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
capture('registry-command-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed()
print('Clean candidate site/check/shared registry passed; browser/original-pixel/FINAL/native/delivery pending.')
