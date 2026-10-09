from common import *
fixed()
st = load(CONTRACT/'canary-stabilized-v1.json')
t = st['targets'][1]
test = ROOT/t['file']
assert load(RUN/'decreasing-canary-focused-inspected-v1.json')['actual_exit'] == 1
old = test.read_bytes()
assert old == (RUN/'decreasing-canary-source-attempt-v1.lean').read_bytes()
write(RUN/'pre-decreasing-canary-repair-native-exact-v2.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p), raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl', RUN/'lifecycle-state.json', RUN/'trials.jsonl', RUN/'own-artifact-journal.md'] if p.exists()]))
s = old.decode('utf8')
replacements = [
    ("apply Finset.sup'_le_iff.mpr", "apply Finset.sup'_le (by decide) _"),
    ("Finset.le_sup' _ (by decide : 0 ∈ range 2)", "Finset.le_sup' (fun t => divergence ψ (-1 / 2) (x t)) (by decide : 0 ∈ range 2)"),
    ("Finset.le_sup' _ (by decide : 1 ∈ range 2)", "Finset.le_sup' (fun t => divergence ψ (1 / 2) (x t)) (by decide : 1 ∈ range 2)"),
    ("(fun t ht => Finset.le_sup' _ (mem_range.mpr ht))", "(fun t ht => Finset.le_sup' (fun s => divergence ψ u (x s)) (mem_range.mpr ht))"),
    ("simp [x, divergence_self]", "simp [divergence_self]")]
for a, b in replacements:
    assert s.count(a) == (2 if a == "apply Finset.sup'_le_iff.mpr" else 1), a
    s = s.replace(a,b)
assert t['exact_header'] in s
assert s.encode('utf8').startswith((RUN/'pre-decreasing-canary-public-v1.lean').read_bytes()[:-len('end BanditRL.OnlinePrescientBregmanRegretCanary\n'.encode())])
test.write_bytes(s.encode('utf8'))
write(RUN/'decreasing-canary-source-attempt-v2.lean', test.read_bytes())
write(RUN/'decreasing-canary-failure-repair-v2.json', dict(prior_actual_exit=1, prior_receipt_sha256=sha(RUN/'decreasing-canary-focused-build-v1.json'), failure="Finset.sup'_le_iff has explicit nonempty/function parameters; field .mpr was not an instantiated equivalence. Underspecified le_sup' function metavariables failed to elaborate.", repair="Use existing Finset.sup'_le with actual nonempty/function parameters and explicit identical functions in le_sup'. Remove one unused simp argument only. Frozen complete headers, loss, actual recurrence, max domain and all numeric targets unchanged.", exact_replacements=replacements, frozen_header_sha256=t['statement_sha256'], production_sha256=sha(PUBLIC)))
code, out = capture('decreasing-canary-focused-build-v2','lake','build','Tests.OnlinePrescientBregmanRegretCanary',required=False)
passed = code == 0 and 'Built Tests.OnlinePrescientBregmanRegretCanary' in out and 'Build completed successfully' in out
write(RUN/'decreasing-canary-focused-inspected-v2.json', dict(actual_exit=code, compiled=passed, new_Test_Built_marker='Built Tests.OnlinePrescientBregmanRegretCanary' in out, canary_sha256=sha(test), production_sha256=sha(PUBLIC), full_conjunctions=2, first_conjunction_preserved=True, numeric_VALUE_audit='pending', source_container_closed=False, whole_Goal_status='ACTIVE'))
if passed:
    capture('decreasing-canary-safe-verify-v2', sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'decreasing-canary-fence-v1.json')
else:
    print(out[-6000:])
    event('native-decreasing-canary-repair-v2','repair',dict(leaf=t['declaration'],actual_exit=code,frozen_header_unchanged=True,evidence='decreasing-canary-focused-build-v2.json'))
fixed()
assert passed
print('Both full concrete conjunctions compiled; selected numeric VALUE audit and combined acceptance still pending.')
