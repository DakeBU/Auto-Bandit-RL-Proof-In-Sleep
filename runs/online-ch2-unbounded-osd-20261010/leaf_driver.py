from common import *
fixed()
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
st=load(CONTRACT/'stabilized-v1.json');targets={r['name'].rsplit('.',1)[1]:r for r in st['targets']}
assert load(RUN/'selector-focused-build-v2.json')['actual_exit']==0
assert load(RUN/'selector-fence-compared-v2.json')['unchanged']
defs=(CONTRACT/'definitions-draft-v1.lean').read_bytes()
assert PUBLIC.read_bytes().startswith(defs)
def guard():
    fixed()
    assert PUBLIC.read_bytes().startswith(defs)
    text=PUBLIC.read_text(encoding='utf8')
    for name,row in targets.items():
        if 'theorem '+name+' ' in text or 'theorem '+name+' :' in text:
            assert lifecycle.statement_hash(lifecycle.lean_declaration_header(PUBLIC,row['name']))==load(CONTRACT/('frozen-'+name+'-v1.json'))['statement_hash']
def lower(name,body,dependencies):
    guard();row=targets[name];before=PUBLIC.read_bytes()
    assert 'theorem '+name not in before.decode('utf8')
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
    write(RUN/(name+'-exact-before-v1.json'),dict(public_sha256=sha(PUBLIC),public_raw_base64=base64.b64encode(before).decode('ascii'),native=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))
    event(name+'-proving-v1','proving',dict(task=TASK,leaf=row['name'],dependencies_ready=dependencies,allowed_file=PUBLIC.relative_to(ROOT).as_posix(),frozen_statement_hash=load(CONTRACT/('frozen-'+name+'-v1.json'))['statement_hash'],full_source_lower_bound='required/open'))
    addition='\n'+row['context']+'\n'+row['header']+' := by\n'+body+'\nend BanditRL.OnlineUnboundedOSD\n'
    PUBLIC.write_bytes(before+addition.encode('utf8'))
    guard();assert PUBLIC.read_bytes().startswith(before)
    write(RUN/(name+'-attempt-v1.lean'),PUBLIC.read_bytes())
    code,out=capture(name+'-focused-build-v1','lake','build','BanditRLProof.OnlineUnboundedOSD',required=False)
    write(RUN/(name+'-focused-inspected-v1.json'),dict(actual_exit=code,actual_stdout=out,build_completed_marker='Build completed successfully' in out,source=rows([PUBLIC]),exact_old_public_prefix_preserved=True,scope='Focused leaf only; source theorem and package gates remain open'))
    assert code==0 and 'Build completed successfully' in out
    capture(name+'-native-fence-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/(name+'-native-extracted-v1.json'))
    actual=load(CONTRACT/(name+'-native-extracted-v1.json'));frozen=load(CONTRACT/('frozen-'+name+'-v1.json'))
    assert actual['statement_hash']==frozen['statement_hash']
    write(RUN/(name+'-fence-compared-v1.json'),dict(actual_native_hash=actual['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True))
    guard()
