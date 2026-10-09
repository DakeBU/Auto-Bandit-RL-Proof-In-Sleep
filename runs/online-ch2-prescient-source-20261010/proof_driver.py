from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle

def native_snapshot(label):
    paths=[RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'own-artifact-journal.md',RUN/'trials.jsonl']
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.relative_to(ROOT).as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in paths],provenance='Contemporaneous exact bytes before actual native metadata mutation.'))

def append_proof(index, label, body):
    fixed()
    row=load(CONTRACT/'stabilized-v1.json')['six_targets'][index]
    old=PUBLIC.read_bytes()
    assert ('theorem '+row['name'].rsplit('.',1)[1]) not in old.decode('utf8')
    native_snapshot(label+'-native-before')
    event(label+'-proving-event','proving',dict(task=TASK,leaf=row['name'],allowed_file=PUBLIC.relative_to(ROOT).as_posix(),terminal_statement_unchanged=True))
    write(RUN/(label+'-exact-before.json'),dict(path=PUBLIC.relative_to(ROOT).as_posix(),sha256=sha(PUBLIC),before_raw_base64=base64.b64encode(old).decode('ascii')))
    namespace=row['context'].splitlines()[0].split('namespace ',1)[1]
    addition='\n'+row['context']+'\n'+row['header']+' := by\n'+body.rstrip()+'\n\nend '+namespace+'\n'
    PUBLIC.write_bytes(old+addition.encode('utf8'))
    write(RUN/(label+'-source.lean'),PUBLIC.read_bytes())
    return build_existing(index,label)

def build_existing(index,label):
    row=load(CONTRACT/'stabilized-v1.json')['six_targets'][index]
    actual=lifecycle.lean_declaration_header(PUBLIC,row['name'])
    fence=load(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'))
    assert lifecycle.statement_hash(actual)==fence['statement_hash']
    code,out=capture(label+'-focused-build','lake','build','BanditRLProof.OnlinePrescientBregmanSource',required=False)
    built=code==0 and 'Built BanditRLProof.OnlinePrescientBregmanSource' in out and 'Build completed successfully' in out
    write(RUN/(label+'-inspected.json'),dict(actual_exit=code,actual_stdout=out,source=rows([PUBLIC]),declaration=row['name'],frozen_statement_hash=fence['statement_hash'],actual_statement_hash=lifecycle.statement_hash(actual),compiled_module_markers=built,package_accepted=False))
    if not built:
        native_snapshot(label+'-repair-native-before')
        event(label+'-repair-event','repair',dict(task=TASK,leaf=row['name'],failure_record=label+'-inspected.json',statement_changed=False))
        return False
    capture(label+'-native-fence',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/(label+'-native-fence.json'))
    assert load(CONTRACT/(label+'-native-fence.json'))['statement_hash']==fence['statement_hash']
    return True
