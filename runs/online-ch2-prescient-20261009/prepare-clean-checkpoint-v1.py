from publication_guard_v1 import *
fixed();full=load(RUN/'full-harness-inspected-v1.json');assert full['actual_check_passed']
assert load(RUN/'shadow-inspected-v1.json')['actual_report']['mismatches']==[]
review=RUN/'reader-status-and-RAW-review-v2.json'
assert sha(review)=='2c5fe701af837b64a2488e4979bb356ecdcb741acbeaba0fc6daf9ccf9c6084e'
r=load(review);assert not r['required_repairs']
for row in load(RUN/'reader-status-and-RAW-review-inputs-v2.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
delta=r['approved_materialization'];p=Path(delta['path']);assert sha(p)==delta['before_sha256']
p.write_bytes(Path(delta['after_snapshot']).read_bytes())
from publication_guard_v2 import fixed as current_fixed
current_fixed()
write(RUN/'reader-status-applied-v2.json',dict(actual_review_sha256=sha(review),exact_materialization=delta,applicable_full_Lean_gate_sha256=sha(RUN/'full-harness-inspected-v1.json'),all_production_Test_root_pin_bytes_unchanged=True,source_formula_statement_proof_unchanged=True,change='Only transient appended card label; current semantic status remains compiled-local/general-source-open. Full Lean gate applies to exact unchanged proof context; site/contributor run on actual new reader bytes.',chapter_complete=False,whole_Goal_status='ACTIVE'))
manifest=load(CONTRIBUTION)
manifest['verification']['bandit_check']='Actual current root9107/Tests9274 cached-inclusive jobs and full tools/bandit.py check exit0,472tests/7existing skips, compiled ProofGraphExport and check-passed markers inspected. RUN/full-harness-inspected-v1.json; job counts are not new theorem counts.'
manifest['verification']['independent_review']+=' Separate exact one-field status-label and2immutable RAW EOF exception review2c5fe701af837b64a2488e4979bb356ecdcb741acbeaba0fc6daf9ccf9c6084e accepted; full actual diff still required and no mathematical exemption.'
CONTRIBUTION.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
own=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
write(RUN/'pre-checkpoint-own-task-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in own]))
own[0].write_bytes(('# '+TASK+'\n\nStatus candidate:7frozen affine Euclidean prescient producer bodies plus5canaries actualcompiled, distinct source/CONTRACT/BODY/reader reviews accepted. Root9107/Tests9274/fullharness472tests7skips/exporter/checkpassed and ownshadowpassed. Clean site/registry/pixels/nonemptycontributor/FINAL/native/delivery pending. Full general sourcecontainer and all8Chapter2forwards remain REQUIRED/OPEN. WholeGoalACTIVE; not Chapter2complete/main/live.\n').encode('utf8'))
own[1].write_bytes(('# Bounded prescient obligations\n\n'+'\n'.join('- '+t['declaration']+': actualcompiled/BODYaccepted; fixedheader '+t['statement_hash'] for t in load(CONTRACT/'stabilized-v1.json')['targets'])+'\n\nFive complementary canaries actualcompiled/BODYaccepted. These12 selected proof targets are not a source-result/chapter denominator. Current root Tests fullharness ownshadow passed; clean site/registry/pixels/contributor/FINAL/native/delivery remain pending. Actual general prescient source theorem and all8Chapter2forward containers REQUIRED/OPEN, proof totalnull, wholeGoalACTIVE.\n').encode('utf8'))
index=ROOT/'research-wiki/retrieval-index'/('ONLINE-CH2-PRESCIENT-20261009.md')
with index.open('a',encoding='utf8',newline='') as f:f.write('\nActual current shared root9107/Tests9274/fullharness472tests7skips/ProofGraphExport/checkpassed and ownshadowmismatches[] passed. Exact one-field readerstatus clarification approved/applied; frozen Lean/root/pins unchanged. Clean site/registry/DOM/pixels/nonempty contributor/FINAL/native/delivery pending. WholeGoalACTIVE.\n')
stage=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),'BanditRLProof.lean','Tests.lean',CONTRACT.relative_to(ROOT).as_posix(),RUN.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),index.relative_to(ROOT).as_posix(),'website/content/chapters.json','website/content/readings.json','website/content/highlights.json',*[p.relative_to(ROOT).as_posix() for p in own]]
allowed=set(stage)
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
    rel=line[3:];assert rel in allowed or rel.startswith(CONTRACT.relative_to(ROOT).as_posix()+'/') or rel.startswith(RUN.relative_to(ROOT).as_posix()+'/'),rel
capture('candidate-stage-v1','git','add',*stage)
code,out=capture('candidate-full-diff-check-v1','git','diff','--cached','--check',required=False)
expected={Path(x['path']).relative_to(ROOT).as_posix() for x in r['approved_RAW_EOF_exceptions']}
actual=set()
for line in out.splitlines():
    if ': new blank line at EOF.' in line:actual.add(line.split(':',1)[0])
    elif ': trailing whitespace.' in line:raise AssertionError(line)
assert code==2 and actual==expected,(code,actual,expected,out)
capture('candidate-scoped-diff-check-v1','git','diff','--cached','--check','--','.',*[':(exclude)'+p for p in sorted(expected)])
write(RUN/'candidate-diff-audit-v1.json',dict(actual_full_exit=code,actual_full_report_sha256=sha(RUN/'candidate-full-diff-check-v1.json'),exact_RAW_EOF_exceptions=r['approved_RAW_EOF_exceptions'],scoped_whitespace_gate_passed=True,scoped_exemptions_only_received_decoder_reports=True,production_Test_reader_contract_exemptions=False,distinct_exception_review_sha256=sha(review),chapter_complete=False,whole_Goal_status='ACTIVE'))
# Preserve exact reviewed RAW bytes whenever Git's configured CRLF filter changes them.
rawrows=[]
for rel in subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines():
    p=ROOT/rel;raw=p.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(p),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-v1.json',dict(rows=rawrows,scope='Actual staged blob versus reviewed on-disk RAW audit before candidate commit; every differing RAW durably preserved, no reserialization claim.'))
write(RUN/'candidate-stage-plan-v1.json',dict(stage=stage,actual_full_whitespace_exit=code,scoped_whitespace_exit=0,RAW_snapshots_sha256=sha(RUN/'exact-RAW-line-ending-snapshots-v1.json'),only_CRLF_differences=len(rawrows),commit_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('candidate-final-stage-v1','git','add',*stage)
current_fixed();print('Actual scoped candidate staging/2exact RAW EOF diagnostics/CRLF preservation inspected; commit pending.')
