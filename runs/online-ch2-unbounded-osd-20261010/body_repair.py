from leaf_driver import *

def repair(name,version,replacements,failure,change):
    guard()
    prior=version-1
    assert sha(PUBLIC)==sha(RUN/(name+'-attempt-v'+str(prior)+'.lean'))
    assert load(RUN/(name+'-focused-build-v'+str(prior)+'.json'))['actual_exit']!=0
    tag=name+'-v'+str(version)
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
    write(RUN/(tag+'-repair-exact-before.json'),dict(public=rows([PUBLIC]),native=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))
    event(tag+'-repair','repair',dict(task=TASK,leaf=targets[name]['name'],failure=failure,change=change,statement_changed=False,definitions_changed=False,prior_attempt=rows([RUN/(name+'-attempt-v'+str(prior)+'.lean'),RUN/(name+'-focused-build-v'+str(prior)+'.json')])))
    text=PUBLIC.read_text(encoding='utf8')
    for old,new in replacements:
        assert text.count(old)==1,old
        text=text.replace(old,new)
    PUBLIC.write_bytes(text.encode('utf8'))
    guard()
    assert PUBLIC.read_bytes().startswith(base64.b64decode(load(RUN/(name+'-exact-before-v1.json'))['public_raw_base64']))
    write(RUN/(name+'-attempt-v'+str(version)+'.lean'),PUBLIC.read_bytes())
    code,out=capture(name+'-focused-build-v'+str(version),'lake','build','BanditRLProof.OnlineUnboundedOSD',required=False)
    write(RUN/(name+'-focused-inspected-v'+str(version)+'.json'),dict(actual_exit=code,actual_stdout=out,build_completed_marker='Build completed successfully' in out,source=rows([PUBLIC]),body_only_repair=True,statement_and_definitions_unchanged=True,source_algorithm_lower_bound_open=True))
    assert code==0 and 'Build completed successfully' in out
    row=targets[name]
    capture(name+'-native-fence-v'+str(version),sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/(name+'-native-extracted-v'+str(version)+'.json'))
    actual=load(CONTRACT/(name+'-native-extracted-v'+str(version)+'.json'));frozen=load(CONTRACT/('frozen-'+name+'-v1.json'))
    assert actual['statement_hash']==frozen['statement_hash']
    write(RUN/(name+'-fence-compared-v'+str(version)+'.json'),dict(actual_native_hash=actual['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True,body_only_repair=True))
    guard()
