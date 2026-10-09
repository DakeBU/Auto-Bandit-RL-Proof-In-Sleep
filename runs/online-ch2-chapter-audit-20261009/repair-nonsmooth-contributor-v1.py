from common_nonsmooth_publication_v2 import *
import base64

fixed()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert head=='d6ec4fd9fce5cc9d20936f1ebf372aef07a26a56'
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
    assert line in ['?? runs/online-ch2-chapter-audit-20261009/repair-nonsmooth-contributor-v1.py',
        '?? runs/online-ch2-chapter-audit-20261009/checkpoint-nonsmooth-site-v3.py'],line
for label in ['nonsmooth-candidate-commit-v1','nonsmooth-contributor-stack-v2']:
    source=ROOT/'tmp'/(TASK+'-'+label+'.json')
    write(RUN/(label+'.json'),source.read_bytes())
failed=load(RUN/'nonsmooth-contributor-stack-v2.json')
text=base64.b64decode(failed['stdout_base64']).decode('utf8')
assert failed['actual_exit']==1 and 'not changed protected/production surfaces: Tests.lean, Tests/OnlineNonsmoothExamplesCanary.lean' in text
m=load(CONTRIBUTION);before=sha(CONTRIBUTION)
assert m['verification']['owned_test_files']==['Tests/OnlineNonsmoothExamplesCanary.lean']
assert m['verification']['owned_test_root_files']==['Tests.lean']
assert 'Tests.lean' in m['affected_files'] and 'Tests/OnlineNonsmoothExamplesCanary.lean' in m['affected_files']
m['affected_files']=[p for p in m['affected_files'] if p not in ['Tests.lean','Tests/OnlineNonsmoothExamplesCanary.lean']]
assert len(m['affected_files'])==5
CONTRIBUTION.write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
write(RUN/'nonsmooth-contributor-manifest-repair-v1.json',dict(actual_failed_receipt_sha256=sha(RUN/'nonsmooth-contributor-stack-v2.json'),
    actual_command_exit=1,classification='contributor-manifest-protected-surface-schema',
    before_manifest_sha256=before,after_manifest_sha256=sha(CONTRIBUTION),
    exact_repair='Remove the two Test paths only from affected_files; retain both in existing verification.owned_test_files and owned_test_root_files. Checker defines affected_files as changed protected/production surfaces.',
    production_proof_canary_statement_reader_change=False,full_Lean_gate_still_applicable=True,
    original_failure_retained=True,
    helper_initial_guard_failure='Actual initial helper exit1 before mutations: both freshly created owned helper files were untracked; exact two-file guard corrected. No unrelated path permitted.',
    chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual contributor schema failure retained; only new manifest affected_files corrected, no mathematical/reader changes.')
