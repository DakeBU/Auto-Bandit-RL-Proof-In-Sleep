from commit_owned_v1 import *
import re

post_fixed();stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check',BASE]
code=gate('accepted-full-diff-v1',*command,required=False);assert code in [0,2]
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',
    (RUN/'accepted-full-diff-v1.log').read_text(encoding='utf8'),re.M))
bound={x['path']:x['sha256'] for x in load(RUN/'post-native-review-inputs-v1.json')['rows']}
exceptions=[]
for rel in sorted(bad):
    p=ROOT/rel
    assert rel.startswith(RUN.relative_to(ROOT).as_posix()+'/') and p.suffix in ['.log','.raw'],rel
    assert bound[p.as_posix()]==sha(p),rel
    exceptions.append(dict(path=rel,sha256=sha(p),reason='Exact reviewed RAW log/snapshot retained byte-for-byte'))
if code:
    assert bad
    exceptions.append(dict(path=(RUN/'accepted-full-diff-v1.log').relative_to(ROOT).as_posix(),
        sha256=sha(RUN/'accepted-full-diff-v1.log'),reason='Actual RAW whitespace diagnostic'))
write(RUN/'accepted-diff-raw-exceptions-v1.json',dict(full_unexcluded_actual_exit=code,
    full_unexcluded_passed=code==0,exceptions=exceptions,production_Test_reader_contract_exceptions=0))
stage_owned()
gate('accepted-scoped-diff-v1',*command,'--','.',*[':(exclude)'+x['path'] for x in exceptions])
post_fixed()
receipt=commit_owned('Record reviewed actual FTL limit acceptance and shared reader evidence','accepted-commit-v1')
write(RUN/'accepted-source-commit-v1.json',dict(receipt,branch=BRANCH,stacked_base=BASE,basePR=200,
    actual_native_acceptance=True,actual_post_native_review=True,draft_delivery_pending=True,
    chapter_complete=False,goal_complete=False,merged=False,live=False))
write(RUN/'accepted-commit-v1.log',Path(receipt['log_path']).read_bytes())
