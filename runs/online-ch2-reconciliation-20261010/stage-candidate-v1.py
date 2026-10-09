from integration_guard_v2 import *
import fnmatch
fixed()
plan=load(RUN/'candidate-stage-plan-v1.json');stage=plan['stage']
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert not subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
ar=load(RUN/'evidence-attributes-review-v1.json')
assert ar['verdict']=='accepted-with-explicit-delta' and not ar['required_repairs']
assert sha(ar['report'])==ar['report_sha256'] and sha(ar['input_manifest'])==ar['input_manifest_sha256']
for r in load(ar['input_manifest'])['rows']:assert sha(r['path'])==r['sha256']
matched=[]
for p in RUN.rglob('*'):
    if p.is_file():
        rel=p.relative_to(RUN).as_posix()
        if p.suffix=='.raw' or fnmatch.fnmatch(rel,'forward-readonly-retrieval/*.txt') or p.name=='integration_guard_v1.py':
            matched.append(dict(path=p.as_posix(),sha256=sha(p),role='Immutable retained audit artifact; never current executable source.'))
assert all(not r['path'].endswith(('integration_guard_v2.py','materialize-integration-v2.py')) for r in matched)
write(RUN/'candidate-binary-artifacts-bound-v1.json',dict(rows=matched,scope='Actual artifact byte bindings before staging; binary Git diff does not certify original whitespace.'))
capture('candidate-stage-v1','git','add',*stage)
changed=subprocess.check_output(['git','diff','--cached','--name-only',BASE],encoding='utf8').splitlines()
baseline={Path(r['path']).relative_to(ROOT).as_posix() for r in load(RUN/'baseline-v1.json')['rows']}
assert set(changed)&baseline==set(plan['old_changed_paths'])
for p in changed:assert any(p==s or p.startswith(s+'/') for s in stage),p
capture('candidate-active-text-diff-v1','git','diff','--cached',BASE,'--check')
for rel in ['BanditRLProof/OnlineFTLSelector.lean','Tests/OnlineFTLSelectorCanary.lean']:
    assert subprocess.check_output(['git','show',':'+rel])==(ROOT/rel).read_bytes()
write(RUN/'candidate-stage-inspected-v1.json',dict(actual_changed_paths=changed,old_changed_paths=plan['old_changed_paths'],actual_active_text_diff_exit=0,artifacts=sha(RUN/'candidate-binary-artifacts-bound-v1.json'),scope='Staged only; no commit/site/acceptance implied. Full harness retry pending.',chapter_complete=False,whole_Goal='active'))
fixed()
