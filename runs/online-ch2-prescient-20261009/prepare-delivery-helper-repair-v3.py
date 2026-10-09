from publication_guard_v3 import *

fixed()
prior=RUN/'delivery-helper-review-v2.json'
assert sha(prior)=='f244bc1ddb5fa0842bad21b37634e00826d1562cdbe927ce328a93f8110b5966'
old=(RUN/'deliver-v2.py').read_text(encoding='utf8')
s=old.replace("repair=load(RUN/'delivery-helper-review-v2.json')","repair=load(RUN/'delivery-helper-review-v3.json')")
s=s.replace("'delivery-helper-inputs-v2.json'","'delivery-helper-inputs-v2.json','delivery-helper-inputs-v3.json'")
s=s.replace('delivery-v2','delivery-v3').replace('acceptance-stage-v2','acceptance-stage-v3').replace('acceptance-full-package-diff-v2','acceptance-full-package-diff-v3').replace('acceptance-scoped-package-diff-v2','acceptance-scoped-package-diff-v3')
needle="assert pr['title']==plan['title'] and pr['body'].replace('\\r\\n','\\n').removesuffix('\\n')==Path(plan['body_path']).read_text(encoding='utf8').removesuffix('\\n')"
replacement="""def body_normalized(s):
    s=s.replace('\\r\\n','\\n')
    return s[:-1] if s.endswith('\\n') else s
assert pr['title']==plan['title'] and body_normalized(pr['body'])==body_normalized(Path(plan['body_path']).read_text(encoding='utf8'))"""
assert s.count(needle)==1;s=s.replace(needle,replacement)
assert '.removesuffix(' not in s
compile(s,'deliver-v3.py','exec');write(RUN/'deliver-v3.py',s)
probe='''import json,sys
def body_normalized(s):
    s=s.replace('\\r\\n','\\n')
    return s[:-1] if s.endswith('\\n') else s
cases=[('body\\r\\n','body'),('body\\n','body'),('body','body'),('body \\n','body '),('body\\n\\n','body\\n'),('a\\r\\nb\\r\\n','a\\nb')]
for raw,expected in cases:assert body_normalized(raw)==expected
assert body_normalized('body \\n')!=body_normalized('body\\n')
assert body_normalized('body\\n\\n')!=body_normalized('body\\n')
print(json.dumps(dict(actual_executable=sys.executable,actual_version=sys.version,case_count=len(cases),trailing_space_preserved=True,second_trailing_newline_preserved=True,all_passed=True)))
'''
write(RUN/'delivery-body-normalization-probe-v3.py',probe)
_,out=capture('delivery-body-normalization-probe-v3',sys.executable,'-B','-X','utf8',RUN/'delivery-body-normalization-probe-v3.py')
result=json.loads(out);assert result['all_passed']
write(RUN/'delivery-helper-repair-v3.json',dict(kind='prospective-Python38-compatibility-repair-not-actual-publication-failure',repair='D2',prior_rejected_review_sha256=sha(prior),old_helper_sha256=sha(RUN/'deliver-v2.py'),new_helper_sha256=sha(RUN/'deliver-v3.py'),actual_string_probe=result,probe_receipt_sha256=sha(RUN/'delivery-body-normalization-probe-v3.json'),changes='Only explicit 3.8-compatible normalization, versioned helper/review/receipt/output paths; v1/v2 immutable, no native replay or source/proof/reader change.',execution_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'delivery-helper-inputs-v3.json',dict(rows=rows([RUN/'deliver-v2.py',RUN/'deliver-v3.py',RUN/'prepare-delivery-helper-repair-v3.py',RUN/'delivery-helper-repair-v3.json',RUN/'delivery-helper-inputs-v2.json',prior,RUN/'delivery-helper-review-v2.md',RUN/'delivery-body-normalization-probe-v3.py',RUN/'delivery-body-normalization-probe-v3.json',RUN/'PR-plan-v1.json',RUN/'PR-body-v1.md',RUN/'publication_guard_v3.py']),phase='Separate D2 Python38 repair review; actual pure-string probe passed, publication not executed',chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Prospective v3 ready; actual Python38 pure-string probe passed, native not replayed.')
