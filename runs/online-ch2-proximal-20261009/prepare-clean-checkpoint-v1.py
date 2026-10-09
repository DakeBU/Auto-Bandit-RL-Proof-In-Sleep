from publication_guard_v1 import *
fixed()
full=load(RUN/'full-harness-inspected-v1.json');assert full['actual_check_passed']
assert load(RUN/'shadow-inspected-v1.json')['actual_report']['mismatches']==[]
review=RUN/'publication-status-review-v2.json'
assert sha(review)=='8ea3f8c6cc779abc9cc619d7a8fa83e55e5420a7c178e81d32e42913887f0eb3'
r=load(review);assert not r['required_repairs']
for row in load(RUN/'publication-status-review-inputs-v2.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
delta=r['approved_materialization'];p=Path(delta['path']);assert sha(p)==delta['before_sha256']
p.write_bytes(Path(delta['after_snapshot']).read_bytes())
from publication_guard_v2 import fixed as current_fixed
current_fixed()
write(RUN/'reader-status-applied-v2.json',dict(actual_review_sha256=sha(review),exact_materialization=delta,applicable_full_Lean_gate_sha256=sha(RUN/'full-harness-inspected-v1.json'),all_production_Test_root_pin_bytes_unchanged=True,only_change='Transient one card status label; semantic source/formula/proof/assumption bytes unchanged.',site_contributor_FINAL_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
own=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
retrieval=ROOT/'research-wiki/retrieval-index'/(TASK+'.md')
write(RUN/'pre-checkpoint-own-metadata-v1.json',dict(rows=[dict(path=q.as_posix(),sha256=sha(q),raw_base64=base64.b64encode(q.read_bytes()).decode('ascii')) for q in [CONTRIBUTION,retrieval,*own]]))
c=load(CONTRIBUTION)
c['verification']['bandit_check']='Actual combined shared root9108/Tests9276 cached-inclusive jobs and full tools/bandit.py check exit0, compiler/unittest/exporter/check-passed markers separately inspected: RUN/full-harness-inspected-v1.json. Job counts are not new theorem counts.'
c['verification']['independent_review']+=' Exact one-label clarification and two SHA-bound immutable received decoder EOF exceptions separately accepted in publication-status-review-v2.json. Actual full/scoped diff, site/registry/pixels/FINAL/native/delivery pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nCurrent candidate: one frozen production comparison and three frozen canaries actualcompiled/BODY accepted, including B1 numeric proof-route repair. Actual shared root9108/Tests9276 and full harness compiler/unittest/exporter/check-passed markers, OWNshadow passed. Exact one-label reader status clarification separately reviewed. Clean site/registry/DOM/pixels/two nonempty contributor bases/FINAL/native/delivery pending. All eight Chapter2 forwards and general prescient source REQUIRED/OPEN; chapter proof denominatornull, wholeGoalACTIVE.\n'
for q in [retrieval,*own]:q.write_bytes(q.read_bytes()+suffix.encode('utf8'))
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean',CONTRACT.relative_to(ROOT).as_posix(),RUN.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),retrieval.relative_to(ROOT).as_posix(),'website/content/chapters.json','website/content/readings.json','website/content/highlights.json',*[q.relative_to(ROOT).as_posix() for q in own]]
allowed=set(stage)
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
    rel=line[3:];assert rel in allowed or rel.startswith(CONTRACT.relative_to(ROOT).as_posix()+'/') or rel.startswith(RUN.relative_to(ROOT).as_posix()+'/'),rel
capture('candidate-stage-v1','git','add',*stage)
code,out=capture('candidate-full-diff-check-v1','git','diff','--cached',BASE,'--check',required=False)
expected={Path(x['path']).relative_to(ROOT).as_posix() for x in r['approved_RAW_EOF_exceptions']}
actual={line.split(':',1)[0] for line in out.splitlines() if ': new blank line at EOF.' in line}
assert code==2 and actual==expected and ': trailing whitespace.' not in out,(code,actual,expected,out)
capture('candidate-scoped-diff-check-v1','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+q for q in sorted(expected)])
write(RUN/'candidate-diff-audit-v1.json',dict(actual_full_exit=code,actual_full_report_sha256=sha(RUN/'candidate-full-diff-check-v1.json'),exact_RAW_EOF_exceptions=r['approved_RAW_EOF_exceptions'],scoped_whitespace_gate_passed=True,scoped_exemptions_only_received_decoder_reports=True,production_Test_reader_contract_exemptions=False,distinct_exception_review_sha256=sha(review),chapter_complete=False,whole_Goal_status='ACTIVE'))
rawrows=[]
for rel in subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines():
    q=ROOT/rel;raw=q.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(q),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-v1.json',dict(rows=rawrows,scope='Actual reviewed RAW versus staged Git blob; every differing RAW preserved exactly, no reserialization claim.'))
write(RUN/'candidate-stage-plan-v1.json',dict(stage=stage,actual_full_whitespace_exit=code,scoped_whitespace_exit=0,RAW_snapshots_sha256=sha(RUN/'exact-RAW-line-ending-snapshots-v1.json'),only_CRLF_differences=len(rawrows),commit_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('candidate-final-stage-v1','git','add',*stage)
current_fixed();print('Actual scoped staged candidate/2exact received EOF diagnostics/RAW preservation inspected.')
