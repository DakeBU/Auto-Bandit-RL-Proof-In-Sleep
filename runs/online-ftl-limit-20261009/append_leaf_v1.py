from common_proving_v1 import *

def append_leaf(leaf,body,requires=()):
    s=proving_fixed()
    target=next(t for t in s['targets'] if t['id']==leaf)
    for parent in requires:
        assert load(RUN/(parent+'-attempt-v1.json'))['actual_build_exit']==0
    text=PUBLIC.read_text(encoding='utf8')
    assert target['name'].split('.')[-1] not in text
    assert text.endswith('end BanditRL.OnlineLearning\n')
    native(leaf+'-proving-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
        json.dumps(dict(run_id=RUN.name,leaf=leaf,dependency_ready=True,requires=list(requires),
            statement_hash=target['statement_hash'],single_lower_route=True,terminal_edit_allowed=False)))
    PUBLIC.write_bytes((text.rsplit('end BanditRL.OnlineLearning',1)[0]+ '\n'+target['header']+
        ' := by\n'+body.rstrip()+'\n\nend BanditRL.OnlineLearning\n').encode('utf8'))
    proving_fixed()
    write(RUN/(leaf+'-attempt-v1.lean.raw'),PUBLIC.read_bytes())
    code=gate(leaf+'-focused-v1','lake','build','BanditRLProof.OnlineFTLLimitSemantics',required=False)
    write(RUN/(leaf+'-attempt-v1.json'),dict(leaf=leaf,statement_hash=target['statement_hash'],
        actual_build_exit=code,status='compiled' if code==0 else 'repair',
        source_snapshot_sha256=sha(RUN/(leaf+'-attempt-v1.lean.raw')),package_accepted=False,chapter_complete=False,goal_complete=False))
    gate(leaf+'-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
        '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
        '--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),
        '--statement-hash',target['statement_hash'],'--attempt-id',leaf+'-v1',
        '--verifier-evidence',(RUN/(leaf+'-focused-v1-exit.json')).as_posix(),
        '--notes','Actual focused module compile result; frozen terminal unchanged; source/body acceptance pending.',
        '--progress-class','unreviewed','--obligations-before','5','--obligations-after','5')
    assert code==0,'Failed body retained; repair same exact target before dependent leaf.'
    native(leaf+'-fence-v1','statement-fence','--declaration',target['name'],'--file',PUBLIC.relative_to(ROOT).as_posix(),
        '--source-assumption','(y : ℕ → ℝ)','--output',(RUN/('fences/'+leaf+'-v1.json')).relative_to(ROOT).as_posix())
    native(leaf+'-safe-v1','safe-verify','--fence',(RUN/('fences/'+leaf+'-v1.json')).relative_to(ROOT).as_posix())
    print(leaf,'actual focused compile/fence successful, semantic acceptance pending.',flush=True)
