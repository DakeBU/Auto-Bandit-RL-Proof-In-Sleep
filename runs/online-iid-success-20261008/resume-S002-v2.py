from leaf_tools_v1 import *
headers_fixed(1)
source=(RUN/'prove-S002-v1.py').read_text(encoding='utf8')
exec(compile(source[:source.index('row=start_leaf')],str(RUN/'prove-S002-v1.py')+'#definitions','exec'))
write(RUN/'S002-writer-repair-v2.json',dict(actual_error="TypeError: write_text() got an unexpected keyword argument 'newline'",
    actual_old_exit=1,production_body_not_written_before_error=True,
    error_evidence='actual exec_command output, not separately captured rawstderr',
    repair='Use explicit UTF8 write_bytes; prior native runningtrial/snapshot retained, not replayed',
    target_changed=False))
prior=PUBLIC.read_text(encoding='utf8')
rows=load(CONTRACT/'targets-v1.json')['targets']
assert prior.endswith('end BanditRL.OnlineLearning\n')
PUBLIC.write_bytes((prior[:-len('end BanditRL.OnlineLearning\n')]+
    '/-- '+description+' -/\n'+rows[1]['header']+' := by\n'+body.rstrip()+'\n\n'+
    'end BanditRL.OnlineLearning\n').encode('utf8'))
write(RUN/'leaves'/'S002-body-v2.lean',PUBLIC.read_bytes())
headers_fixed(2)
gate('S002-focused-build-v2','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
finish_leaf(1,'v2',description)
