from common_proving_v1 import *
def append_leaf(i,body,helpers=''):
    s=proving_fixed();t=s['targets'][i];leaf=t['id']
    native('proving-'+leaf+'-lifecycle-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
        json.dumps(dict(run_id=RUN.name,leaf=leaf,dependency_ready=True,statement_hash=t['statement_hash'],
            allowed_file=PUBLIC.relative_to(ROOT).as_posix(),terminal_edit_allowed=False,single_lower_route=True)))
    before=PUBLIC.read_bytes();footer=b'\nend BanditRL.OnlineLearning\n'
    assert before.endswith(footer)
    text=before[:-len(footer)].decode('utf8')+'\n\n'+helpers+'\n'+t['header']+body+footer.decode('utf8')
    PUBLIC.write_bytes(text.encode('utf8'));assert PUBLIC.read_bytes().startswith(before[:-len(footer)])
    proving_fixed();write(RUN/(leaf+'-attempt-v1.lean.raw'),PUBLIC.read_bytes())
    code=gate(leaf+'-focused-v1','lake','build','BanditRLProof.OnlineFTLOscillation',required=False)
    write(RUN/(leaf+'-attempt-v1.json'),dict(leaf=leaf,statement_hash=t['statement_hash'],
        public_before_sha256=hashlib.sha256(before).hexdigest(),source_snapshot_sha256=sha(RUN/(leaf+'-attempt-v1.lean.raw')),
        preceding_proof_bytes_unchanged=True,actual_build_exit=code,status='compiled' if code==0 else 'repair',
        package_accepted=False,chapter_complete=False,goal_complete=False))
    gate(leaf+'-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
        '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
        '--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',t['statement_hash'],
        '--attempt-id',leaf+'-v1','--verifier-evidence',RUN/(leaf+'-focused-v1-exit.json'),
        '--progress-class','unreviewed','--obligations-before','4','--obligations-after','4',
        '--notes','Actual frozen leaf focused build; preceding proof bytes preserved; BODY/canary/full acceptance pending.')
    assert code==0,'Retain failure and repair same target.'
    native(leaf+'-fence-v1','statement-fence','--declaration',t['name'],'--file',PUBLIC.relative_to(ROOT),
        '--output',RUN/('fences/'+leaf+'-v1.json'))
    native(leaf+'-safe-v1','safe-verify','--fence',RUN/('fences/'+leaf+'-v1.json'))
    print('Actual frozen '+leaf+' body/fence passed; package acceptance pending.',flush=True)
