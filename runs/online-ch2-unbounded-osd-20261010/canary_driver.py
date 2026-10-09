from leaf_driver import *
TEST=ROOT/'Tests/OnlineUnboundedOSDCanary.lean'
canaries=load(CONTRACT/'canary-headers-draft-v2.json')

def native_snapshot(label):
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))

def canary_guard():
    guard()
    assert sha(PUBLIC)==sha(RUN/'full-body-source-v1.lean')
    assert TEST.read_bytes().startswith(canaries['prefix'].encode('utf8'))
    for row in canaries['targets']:
        if row['header'] in TEST.read_text(encoding='utf8'):
            assert lifecycle.statement_hash(lifecycle.lean_declaration_header(TEST,row['name']))==load(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'))['statement_hash']

def build_canary(index,version):
    row=canaries['targets'][index];name=row['name'].rsplit('.',1)[1]
    canary_guard()
    write(RUN/(name+'-attempt-v'+str(version)+'.lean'),TEST.read_bytes())
    code,out=capture(name+'-focused-build-v'+str(version),'lake','build','Tests.OnlineUnboundedOSDCanary',required=False)
    compiled=code==0 and 'Built Tests.OnlineUnboundedOSDCanary' in out and 'Build completed successfully' in out
    write(RUN/(name+'-focused-inspected-v'+str(version)+'.json'),dict(actual_exit=code,actual_stdout=out,compiled_module_markers=compiled,source=rows([PUBLIC,TEST]),statement_unchanged=True,package_accepted=False))
    assert compiled
    capture(name+'-native-fence-v'+str(version),sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',TEST.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/(name+'-native-extracted-v'+str(version)+'.json'))
    actual=load(CONTRACT/(name+'-native-extracted-v'+str(version)+'.json'));frozen=load(CONTRACT/('frozen-'+name+'-v1.json'))
    assert actual['statement_hash']==frozen['statement_hash']
    write(RUN/(name+'-fence-compared-v'+str(version)+'.json'),dict(actual_native_hash=actual['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True))
    canary_guard()

def lower_canary(index,body):
    row=canaries['targets'][index];name=row['name'].rsplit('.',1)[1]
    canary_guard();before=TEST.read_bytes()
    assert row['header'] not in before.decode('utf8')
    write(RUN/(name+'-exact-before-v1.json'),dict(test_raw_base64=base64.b64encode(before).decode('ascii'),test_sha256=sha(TEST),production=rows([PUBLIC])))
    native_snapshot(name+'-native-before-v1')
    event(name+'-proving-v1','proving',dict(task=TASK,leaf=row['name'],allowed_file=TEST.relative_to(ROOT).as_posix(),statement_frozen=True,source_BODY_accepted=True,canary_BODY_accepted=False,different_horizon_loss_streams=True))
    context='' if index==0 else '\nnamespace BanditRL.OnlineUnboundedOSDCanary\nopen BanditRL.OnlineUnboundedOSD\n'
    TEST.write_bytes(before+(context+'\n'+row['header']+' := by\n'+body+'\nend BanditRL.OnlineUnboundedOSDCanary\n').encode('utf8'))
    assert TEST.read_bytes().startswith(before)
    build_canary(index,1)

def repair_canary(index,version,replacements,failure,change):
    row=canaries['targets'][index];name=row['name'].rsplit('.',1)[1]
    assert sha(TEST)==sha(RUN/(name+'-attempt-v'+str(version-1)+'.lean'))
    assert load(RUN/(name+'-focused-build-v'+str(version-1)+'.json'))['actual_exit']!=0
    native_snapshot(name+'-repair-before-v'+str(version))
    event(name+'-repair-v'+str(version),'repair',dict(task=TASK,leaf=row['name'],failure=failure,change=change,statement_changed=False,definitions_changed=False))
    text=TEST.read_text(encoding='utf8')
    for old,new in replacements:
        assert text.count(old)==1,old
        text=text.replace(old,new)
    TEST.write_bytes(text.encode('utf8'))
    assert TEST.read_bytes().startswith(base64.b64decode(load(RUN/(name+'-exact-before-v1.json'))['test_raw_base64']))
    build_canary(index,version)
