"""Repair only the explanatory comment's accidental Lean nested-comment token."""
from common import *
assert load(RUN/'integrate-reader-v1-01-exit.json')['exit_code']!=0
assert load(RUN/'body-binding-audit-v1.json')['status']=='passed'
raw=PUBLIC.read_bytes();old=Path(next(r['snapshot'] for r in load(RUN/'historical-raw-supersession-v1.json')['rows'] if r['path']==PUBLIC.as_posix())).read_bytes()
assert raw.endswith(old) and raw.count(b'tests +/-1')==1
snap=[]
for p in [PUBLIC.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','research-wiki/contribution-contracts/online-subgradient-absolute-migration-20261007.json']:
 dest=RUN/('snapshots/integration-v1-before-comment-repair-'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes());snap.append(dict(path=p,raw_sha256=sha(p),snapshot=dest.as_posix(),authorized_delta='Leading ordinary comment lexical token repair only; source proof suffix/header/reader mathematics retained.'))
write(RUN/'historical-raw-supersession-integration-v1.json',dict(rows=snap,source_target_repair=False))
PUBLIC.write_bytes(raw.replace(b'tests +/-1',b'tests plus/minus1'))
f=fixed(True)
write(RUN/'public-comment-qualification-v2.json',dict(path=PUBLIC.as_posix(),original_sha256=hashlib.sha256(old).hexdigest(),qualified_sha256=sha(PUBLIC),exact_original_raw_suffix=True,delta='ordinary leading comment only; +/-1 accidentally contains Lean nested-comment opener /-; plus/minus1 fixes lexical token, all mathematical bytes and frozen targets unchanged',supersedes_comment_v1=True))
event('repair',dict(scope='explanatory ordinary comment lexical token',failure='integrate-reader-v1-01.log native header locator error; not a compiler result',mathematical_statement_repair=False,original_math_raw_suffix_fixed=True,source_package_accepted=False))
for n,h in f['headers'].items():native('integrated-safe-'+n+'-v2','safe-verify','--fence',RUN/'native-public-fences'/(n+'.json'),'--lean-file',PUBLIC,'--lean-file',CANARY)
write(RUN/'integrated-public-guard-audit-v2.json',dict(status='passed',native_guards=4,all_original_module_raw_bytes_retained=True,headers_unchanged=True,whole_canary_shareddeps_roots_pins_fixed=True,borrowedS_unchanged=True,old_real_failure_preserved=True,mathematical_repairs=[]))
write(RUN/'repair-comment-decision-v2.md','Actual integration-v1 declaration locator failed because explanatory tests +/-1 includes the Lean nested-comment opening token /-. This is a lexical comment defect, not a changed theorem or failed mathematical tactic. Preserve complete bad commented source/reader/manifest snapshots and raw failed log. Replace only that ASCII spelling with plus/minus1; original module raw suffix, allfour normalized headers, wholethreecanaries, borrowedS/pins/roots remain fixed and four native guards now pass. Reader data/manifest integration was already written and retained exactly. Current rootTests/fullharness still must execute. Separate prepare-delivery-helpers-v1 failed at Python parse time due nested template quotes with no executed body; v2 preserves and repairs only helper quoting. Neither failure is hidden or counted as mathematical progress.\n')
print('Actual comment locator failure repaired; four frozen headers/guards/raw math suffix PASS. Postcomment project gates still pending.')
