from common import *
fixed()
st=load(CONTRACT/'canary-stabilized-v1.json'); t=st['targets'][0]; test=ROOT/t['file']
assert load(RUN/'fixed-canary-focused-inspected-v1.json')['actual_exit']==1
old=test.read_bytes(); assert old==(RUN/'fixed-canary-source-attempt-v1.lean').read_bytes()
write(RUN/'pre-fixed-canary-repair-native-exact-v2.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if p.exists()]))
s=old.decode('utf8'); replacements=[]
for name in ['h0','h1','h2']:
    replacements.append(('simpa [x] using '+name,'simpa [V, ψ, loss, f0, f1, x] using '+name))
for name in ['hf0','hf1','hs0','hs1']:
    replacements.append(('simpa [loss, h] using '+name,'simpa [loss, h, V, f0, f1] using '+name))
for a,b in replacements:
    assert s.count(a)==1,a
    s=s.replace(a,b)
assert t['exact_header'] in s
test.write_bytes(s.encode('utf8'))
write(RUN/'fixed-canary-source-attempt-v2.lean',test.read_bytes())
write(RUN/'fixed-canary-failure-repair-v2.json',dict(prior_actual_exit=1,prior_receipt_sha256=sha(RUN/'fixed-canary-focused-build-v1.json'),failure='Simp normalized explicit parent functions/binders (negated coefficient and Icc bounds) while new local let abbreviations stayed opaque, producing four type mismatches.',repair='Expand the same V/psi/loss/f0/f1/x let definitions on BOTH sides when reusing parent states and proper/support facts; same functions and full header, no premise/endpoint change.',exact_replacements=replacements,frozen_header_sha256=t['statement_sha256'],production_sha256=sha(PUBLIC)))
code,out=capture('fixed-canary-focused-build-v2','lake','build','Tests.OnlinePrescientBregmanRegretCanary',required=False)
passed=code==0 and 'Built Tests.OnlinePrescientBregmanRegretCanary' in out and 'Build completed successfully' in out
write(RUN/'fixed-canary-focused-inspected-v2.json',dict(actual_exit=code,compiled=passed,new_Test_Built_marker='Built Tests.OnlinePrescientBregmanRegretCanary' in out,canary_sha256=sha(test),production_sha256=sha(PUBLIC),full_conjunctions=1,numeric_VALUE_audit='pending',frozen_header_unchanged=True,source_container_closed=False,whole_Goal_status='ACTIVE'))
if passed:
    capture('fixed-canary-safe-verify-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'fixed-canary-fence-v1.json')
else:
    print(out[-4000:])
    event('native-fixed-canary-repair-v2','repair',dict(leaf=t['declaration'],actual_exit=code,frozen_header_unchanged=True,evidence='fixed-canary-focused-build-v2.json'))
fixed()
assert passed
print('Fixed full16conjunct canary v2 focused compiled; numeric VALUE/second canary/full gates pending.')
