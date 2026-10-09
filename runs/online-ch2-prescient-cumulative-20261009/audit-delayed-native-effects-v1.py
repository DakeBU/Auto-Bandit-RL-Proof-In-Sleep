from publication_guard_v3 import *
fixed()
before=load(RUN/'pre-conversion-native-exact-v1.json')
checks=[]
for row in before['rows']:
    p=Path(row['path']); old=base64.b64decode(row['raw_base64']); now=p.read_bytes()
    assert hashlib.sha256(old).hexdigest()==row['sha256']
    if p.name=='own-artifact-journal.md':
        assert now.startswith(old) and len(now)>len(old)
        suffix=now[len(old):].decode('utf8')
        assert 'bandit.py conversion-window' in suffix and TASK in suffix
        checks.append(dict(path=p.as_posix(),before_sha256=row['sha256'],after_sha256=sha(p),authorized_effect='Actual native conversion-window journal append; exact prefix retained.',actual_appended_UTF8=suffix))
    else:
        assert now==old,p
        checks.append(dict(path=p.as_posix(),before_sha256=row['sha256'],after_sha256=sha(p),authorized_effect='Unchanged; conversion-window does not mutate sessions/state/trials.'))
conversion=ROOT/'conversion-windows'/(TASK+'.md')
assert conversion.read_bytes().startswith((RUN/'conversion-window-native-template-v1.raw').read_bytes())
assert (RUN/'director-architect-draft-v1.md').read_text(encoding='utf8') in conversion.read_text(encoding='utf8')
assert 'did NOT exist at stabilization' in conversion.read_text(encoding='utf8')
write(RUN/'delayed-native-effects-inspected-v1.json',dict(actual_command_exit=load(RUN/'conversion-window-native-materialization-v1.json')['actual_exit'],exact_before_snapshot_sha256=sha(RUN/'pre-conversion-native-exact-v1.json'),actual_effect_checks=checks,filled_conversion_sha256=sha(conversion),native_template_exact_prefix_retained=True,frozen_draft_intent_exactly_appended=True,not_retroactive_stabilization_evidence=True,global_journal_and_SGB_unchanged=True,whole_Goal_status='ACTIVE'))
fixed()
print('Actual delayed native effects checked: OWN journal exact-prefix append only; sessions/state/trials unchanged; native template/frozen intent retained.')
