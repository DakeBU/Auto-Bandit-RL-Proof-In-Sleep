from common_integrated_v1 import *
fixed_integrated()
r=load(RUN/'Asymptotic-metadata-repair-receipt-v3.json');proposal=load(RUN/'Asymptotic-metadata-repair-proposal-v3.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
assert sha(r['report'])==r['report_sha256']
assert r['required_reader_corrections']==load(RUN/'stabilized-contract-v1.json')['original_reader_requirements']
assert all(not r[k] for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs'])
for row in r['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path']
allowed=r['allowed_source_append'];assert allowed['live_path']==proposal['live_path'] and allowed['exact_prefix_preserved'] and not allowed['applied']
for k in ['original_sha256','proposed_sha256','addition_sha256']:assert allowed[k]==proposal[k]
old=Path(allowed['live_path']);old_bytes=old.read_bytes();addition=Path(proposal['addition_path']).read_bytes();proposed=Path(proposal['proposed_path']).read_bytes()
assert proposed==old_bytes+addition and len(old_bytes)==1407 and len(addition)==677
write(RUN/'snapshots/Asymptotic-review-manifest-v3.json.raw',MANIFEST.read_bytes())
# Create a versioned guard. Original receipt-bound helpers are left byte-identical.
s=(RUN/'common_integrated_v1.py').read_text(encoding='utf8')
insert='''
APPEND_PATH='BanditRLProof/OnlineLearningAsymptotic.lean'
def approved_append_fixed():
 r=load(RUN/'Asymptotic-metadata-repair-receipt-v3.json');a=r['allowed_source_append']
 assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
 assert sha(r['report'])==r['report_sha256']
 assert a['exact_prefix_preserved'] and a['live_path']==APPEND_PATH
 original=RUN/'snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw'
 addition=RUN/'Asymptotic-source-comment-addition-v3.txt'
 assert sha(original)==a['original_sha256'] and sha(addition)==a['addition_sha256']
 assert Path(APPEND_PATH).read_bytes()==original.read_bytes()+addition.read_bytes()
 assert sha(APPEND_PATH)==a['proposed_sha256']
 reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
 for row in load(RUN/'Asymptotic-metadata-repair-inputs-v3.json')['rows']:
  p=Path(row['path']);assert reviewed[row['path']]==row['sha256']
  if sha(p)!=row['sha256']:
   local=p.resolve().relative_to(ROOT).as_posix()
   if local==APPEND_PATH:p=original
   elif local==MANIFEST.as_posix():p=RUN/'snapshots/Asymptotic-review-manifest-v3.json.raw'
   else:raise AssertionError(row['path'])
  assert sha(p)==row['sha256'],row['path']
def reviewed_append_fixed():
 approved_append_fixed();assert sha(PDF)==PDF_SHA
 for p,h in load(RUN/'draft-baseline-v1.json')['fixed_files'].items():
  actual=RUN/'snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw' if p==APPEND_PATH else Path(p)
  assert sha(actual)==h,p
 frozen=load(RUN/'stabilized-contract-v1.json')
 assert sha(CONTRACT/'targets-v1.json')==frozen['targets_sha256'] and sha(CONTRACT/'public-context-v1.lean')==frozen['context_sha256']
 resolutions={x['original']:x for x in load(RUN/'contract-review-baseline-resolutions-v1.json')}
 for name in ['source-contract-receipt-v1.json','source-repair-receipt-v1.json']:
  r=load(RUN/name);assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
  assert sha(r['report'])==r['report_sha256'] and r['required_reader_corrections']==frozen['original_reader_requirements']
  reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
  for row in load(RUN/'source-contract-inputs-v1.json')['rows']:
   p=row['path'];h=row['sha256'];assert reviewed[p]==h
   if sha(p)!=h:
    if Path(p).resolve()==Path(APPEND_PATH).resolve():actual=RUN/'snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw'
    else:
     old=resolutions[p];assert h==old['original_sha256']==old['snapshot_sha256'];actual=Path(old['snapshot'])
    assert sha(actual)==h,p
'''
s=s.replace('def body_fixed():',insert+'\ndef body_fixed():',1)
s=s.replace(' reviewed_fixed()\n',' reviewed_append_fixed()\n',1)
s=s.replace("   if local in ALLOWED_INTEGRATION:p=", "   if local==APPEND_PATH:p=RUN/'snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw'\n   elif local in ALLOWED_INTEGRATION:p=",1)
write(RUN/'common_integrated_v2.py',s)
old.write_bytes(proposed)
write(RUN/'Asymptotic-source-append-applied-v3.json',dict(approved_receipt_sha256=sha(RUN/'Asymptotic-metadata-repair-receipt-v3.json'),original_snapshot=proposal['original_snapshot'],original_sha256=sha(proposal['original_snapshot']),live_path=old.as_posix(),live_sha256=sha(old),exact_prefix_preserved=True,old_mathematical_tokens_bodies_types_unchanged=True,old73_and371_baselines_resolved_only_to_exact_original_snapshot=True,combined_gates_rerun_required=True,chapter_complete=False,goal_complete=False))
owned=load(RUN/'owned-commit-paths-v1.json');assert old.as_posix() not in owned
write(RUN/'owned-commit-paths-v2.json',owned+[old.as_posix()])
s=(RUN/'audit-scope-v2.py').read_text(encoding='utf8').replace('from common_integrated_v1 import *','from common_integrated_v2 import *').replace("owned-commit-paths-v1.json","owned-commit-paths-v2.json")
write(RUN/'audit-scope-v3.py',s)
s=(RUN/'build-clean-site-v1.py').read_text(encoding='utf8').replace('from common_integrated_v1 import *','from common_integrated_v2 import *').replace("integrated-gates-v1.json","integrated-gates-v3.json").replace("site-build-v1.log","site-build-v2.log").replace("site-build-v1-exit.json","site-build-v2-exit.json").replace("online-no-regret-site-build-v1.log","online-no-regret-site-build-v2.log").replace("site-check-v1","site-check-v2").replace("registry-check-v1","registry-check-v2").replace("current-reader-capture-v1","current-reader-capture-v2").replace("verify-registry-v1.py","verify-registry-v2.py").replace("capture-reader-v1.py","capture-reader-v2.py").replace("combined-root-v1/combined-Tests-v1/full-harness-v1","combined-root-v2/combined-Tests-v2/full-harness-v2").replace("contributor-exact-base-v1","contributor-committed-exact-base-v3")
write(RUN/'build-clean-site-v2.py',s)
for oldname,newname in [('verify-registry-v1.py','verify-registry-v2.py'),('capture-reader-v1.py','capture-reader-v2.py')]:
 write(RUN/newname,(RUN/oldname).read_text(encoding='utf8').replace('from common_integrated_v1 import *','from common_integrated_v2 import *'))
sys.path.insert(0,str(RUN));from common_integrated_v2 import fixed_integrated as verify
verify();print('Exact separately reviewed source comment applied; all old proofs/types unchanged, original bindings preserved by versioned guard. New combined gates required.')
