from publication_guard_v3 import *

fixed()
post=RUN/'post-native-review-v1.json'
assert sha(post)=='72631c85b955d178eb3524ef2ac736573ba23ac5fcbff4cce2f638feded5744e'
r=load(post);assert r['native_verdict']==r['metadata_verdict']==r['prospective_publication_prose_verdict']=='accepted-with-explicit-delta'
assert [x['id'] for x in r['required_repairs']]==['D1']
old=(RUN/'deliver-v1.py').read_text(encoding='utf8')
first="post=RUN/'post-native-review-v1.json';r=load(post)\nassert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']\nassert r['FINAL_sha256']==sha(RUN/'FINAL-review-v1.json')\nfor row in load(RUN/'post-native-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']"
new="""post=RUN/'post-native-review-v1.json';r=load(post)
assert sha(post)=='72631c85b955d178eb3524ef2ac736573ba23ac5fcbff4cce2f638feded5744e'
assert r['native_verdict']==r['metadata_verdict']==r['prospective_publication_prose_verdict']=='accepted-with-explicit-delta'
assert r['FINAL_sha256']==sha(RUN/'FINAL-review-v1.json')
repair=load(RUN/'delivery-helper-review-v2.json')
assert repair['verdict']=='accepted-with-explicit-delta' and not repair['required_repairs']
for packet in ['post-native-inputs-v1.json','delivery-helper-inputs-v2.json']:
    for row in load(RUN/packet)['rows']:assert sha(row['path'])==row['sha256'],row['path']"""
assert old.count(first)==1;s=old.replace(first,new)
start=s.index("# Terminal observations go to ignored tmp")
end=s.index("parent=json.loads(observe(",start)
observe=s[start:end].replace('delivery-v1','delivery-v2')
s=s[:start]+s[end:]
marker="scope()\ncapture('acceptance-stage-v1','git','add',*stage)"
assert s.count(marker)==1;s=s.replace(marker,"scope()\n"+observe+"capture('acceptance-stage-v2','git','add',*stage)")
s=s.replace("capture('acceptance-full-package-diff-v1'","capture('acceptance-full-package-diff-v2'")
s=s.replace("capture('acceptance-scoped-package-diff-v1'","capture('acceptance-scoped-package-diff-v2'")
stage_line="capture('acceptance-final-stage-v1','git','add',*stage)\nfixed();scope()"
final_stage="""observe('acceptance-final-stage',['git','add',*stage])
fixed();scope()
# No RUN writes from here onward. All actual terminal receipts are ignored tmp.
full=observe('final-package-diff-full',['git','diff','--cached',BASE,'--check'],required=False)
full_receipt=load(delivery/'final-package-diff-full.json')
actual_final={line.split(':',1)[0] for line in full.splitlines() if ': new blank line at EOF.' in line}
assert full_receipt['actual_exit']==2 and actual_final==expected and ': trailing whitespace.' not in full
observe('final-package-diff-scoped',['git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)]])
staged=observe('final-staged-scope',['git','diff','--cached','--name-only']).splitlines()
for rel in staged:
    assert rel in stage or any(rel.startswith(prefix+'/') for prefix in [RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix()]),rel
assert staged"""
assert s.count(stage_line)==1;s=s.replace(stage_line,final_stage)
s=s.replace("pr['body'].replace('\\r\\n','\\n').rstrip()==Path(plan['body_path']).read_text(encoding='utf8').rstrip()","pr['body'].replace('\\r\\n','\\n').removesuffix('\\n')==Path(plan['body_path']).read_text(encoding='utf8').removesuffix('\\n')")
s=s.replace("actual_clean=True,applicable_site_source_commit=","actual_clean=True,body_comparison='CRLF to LF and at most one final LF; no other whitespace normalized',applicable_site_source_commit=")
compile(s,'deliver-v2.py','exec')
write(RUN/'deliver-v2.py',s)
write(RUN/'delivery-helper-repair-v2.json',dict(kind='prospective-static-ordering-repair-not-actual-command-failure',required_repair='D1',old_helper_sha256=sha(RUN/'deliver-v1.py'),new_helper_sha256=sha(RUN/'deliver-v2.py'),prior_native_review_sha256=sha(post),changes=['Preserve v1; final-stage receipt and all later terminal observations now ignored tmp','Actually inspect final staged scope/full exact2exceptions/scoped0 after all final additions','PR body comparison preserves all whitespace except CRLF and at most one final LF'],native_not_rerun=True,source_math_Test_reader_unchanged=True,execution_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'delivery-helper-inputs-v2.json',dict(rows=rows([RUN/'deliver-v1.py',RUN/'deliver-v2.py',RUN/'prepare-delivery-helper-repair-v2.py',RUN/'delivery-helper-repair-v2.json',post,RUN/'post-native-review-v1.md',RUN/'post-native-inputs-v1.json',RUN/'PR-plan-v1.json',RUN/'PR-body-v1.md',RUN/'publication_guard_v3.py',RUN/'FINAL-review-v1.json']),phase='Separate D1 helper repair review; no publication execution',chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Prospective D1 v2 ready; native not rerun, old helper/inputs retained.')
