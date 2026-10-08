from commit_owned_v1 import *
post_fixed()
stage_owned()
code=gate('accepted-full-diff-v1','git','diff','--cached','--check',required=False);excluded=[]
if code:
    for line in (RUN/'accepted-full-diff-v1.log').read_text(encoding='utf8').splitlines():
        if ': trailing whitespace.' not in line and ': new blank line at EOF.' not in line:continue
        p=line.split(':',1)[0];assert p.startswith(RUN.relative_to(ROOT).as_posix()+'/') and Path(p).suffix in ['.log','.raw'],p
        if p not in excluded:excluded.append(p)
    assert excluded
    gate('accepted-scoped-diff-v1','git','diff','--cached','--check','--','.',*[':(exclude)'+p for p in excluded])
else:gate('accepted-scoped-diff-v1','git','diff','--cached','--check')
write(RUN/'accepted-diff-raw-exceptions-v1.json',dict(actual_full_exit=code,full_unexcluded_zero=(code==0),
    exact_RAW_exceptions=rows([ROOT/p for p in excluded]),production_Test_reader_contract_exemptions=False,
    scoped_gate_zero=True,reason='Exact RAW output/baseline bytes retained; only OWN .log/.raw exceptions, reviewed diagnostic scope.'))
receipt=commit_owned('Record reviewed bounded FTL proof acceptance and validation evidence','accepted-commit-v1')
write(RUN/'accepted-source-commit-v1.json',dict(receipt,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    accepted_endpoints=4,chapter_complete=False,goal_complete=False,merged=False,live=False))
write(RUN/'accepted-commit-v1.log',Path(receipt['log_path']).read_bytes())
