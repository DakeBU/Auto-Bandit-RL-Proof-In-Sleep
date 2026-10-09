from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
r = load(RUN / 'recursion-attempt-result-v1.json')
assert r['compiled'] and r['actual_exit'] == 0 and r['production_sha256'] == sha(PUBLIC)
probe = 'import BanditRLProof.OnlinePrescientBregman\nopen Set BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman\nnamespace PrescientRecursionAudit\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace \u211d E]\n'
arguments = ['V \u03c8 \u03b7 \u03b7\u0027 loss loss\u0027 x0 t h\u03b7 hloss', 'V \u03c8 \u03b7 loss x0 p t h', 'V \u03c8 \u03b7 loss x0 t k h', 'V \u03c8 \u03b7 loss x0 T hatt']
for t, args in zip(d['targets'][3:7], arguments):
    name = t['declaration'].split('.')[-1]
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
    probe += t['exact_proposed_header'].replace('theorem ' + name, 'theorem public_VALUE_' + name)
    probe += ' :=\n  ' + t['declaration'] + ' ' + args + '\n'
    probe += '#check ' + t['declaration'] + '\n#print ' + t['declaration'] + '\n#print axioms ' + t['declaration'] + '\n#print axioms public_VALUE_' + name + '\n'
probe += 'end PrescientRecursionAudit\n'
write(RUN / 'RecursionPublicAPIProbeV1.lean', probe)
_, out = capture('recursion-public-VALUE-v1', 'lake', 'env', 'lean', RUN / 'RecursionPublicAPIProbeV1.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
no_axioms = re.findall(r'does not depend on any axioms', out)
assert len(axioms) + len(no_axioms) == 8 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
for i, t in enumerate(d['targets'][3:7]):
    _, out = capture('recursion-public-lookup-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', t['declaration'].split('.')[-1], '--statement')
    assert t['declaration'] in out
    fence = (CONTRACT / ('recursion-fence-' + str(i) + '-v1.json')).relative_to(ROOT).as_posix()
    capture('recursion-fence-command-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'statement-fence', '--declaration', t['declaration'], '--file', PUBLIC.relative_to(ROOT).as_posix(), '--output', fence)
    capture('recursion-safe-verify-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'safe-verify', '--fence', fence, '--lean-file', PUBLIC.relative_to(ROOT).as_posix())
    assert load(ROOT / fence)['statement_hash'] == t['statement_hash']
write(RUN / 'recursion-inspected-v1.json', dict(production_sha256=sha(PUBLIC), compiled=True,
    full_generic_public_VALUE=4, standard_only_axiom_outputs=axioms,
    no_axiom_outputs=len(no_axioms), definition_bodies_unchanged=True,
    frozen_headers_unchanged=True, other_proofs_pending=1,
    canaries_PENDING=True, BODY_PENDING=True, combined_gates_PENDING=True,
    package_accepted=False, source_container_closed=False, chapter_complete=False,
    whole_Goal_status='ACTIVE'))
capture('recursion-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled', '--attempt-id', 'PC003-prefix-and-definedness-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', d['targets'][3]['statement_hash'], '--obligations-before', '4', '--obligations-after', '0', '--verifier-evidence', RUN / 'recursion-inspected-v1.json', '--notes', 'Four frozen causal/definedness proofs focused-compiled; generic public VALUE, axiom and native fences inspected. Same-transition terminal selected next by readiness. Package/source cumulative/chapter/Goal remain OPEN.')
fixed()
write(RUN / 'before-transition-selection-v1.lean', PUBLIC.read_bytes())
t = d['targets'][7]
event('transition-selected-native-v1', 'proving', dict(selected_leaves=[dict(declaration=t['declaration'], statement_hash=t['statement_hash'])], dependency_ready='Actual successor specification focused/public/axiom/fence audited; accepted extended proximal theorem unchanged.', source_container_closed=False, chapter_complete=False, goal_complete=False))
capture('transition-running-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running', '--attempt-id', 'PC004-same-produced-transition-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', t['statement_hash'], '--obligations-before', '1', '--obligations-after', '1', '--notes', 'Derive actual one-step loss bound from actual recursion successor; no assumed regret/stability consumer or future-aware algorithm. Sharp cumulative source terminals still open.')
s = PUBLIC.read_text(encoding='utf8')
end = 'end BanditRL.OnlinePrescientBregman\n'
assert s.endswith(end)
prefix = s[:-len(end)]
context = '\nsection InnerProduct\nvariable [InnerProductSpace \u211d E] [CompleteSpace E]\n\n'
body = ''' := by
  obtain \u27e8y, hy, hpV, hm\u27e9 := iterate_succ_some_spec V \u03c8 \u03b7 loss x0 p t hp
  have he : y = x := Option.some.inj (hy.symm.trans hx)
  subst y
  exact proximal_one_step_extended (loss t) V hV hf hs \u03c8 (\u03b7 t) h\u03b7 x p hpV hdx hdp hm
'''
s = prefix + context + t['exact_proposed_header'] + body + '\nend InnerProduct\n' + end
PUBLIC.write_bytes(s.encode('utf8'))
assert PUBLIC.read_bytes().startswith(prefix.encode('utf8'))
for target in d['targets']:
    assert statement_hash(lean_declaration_header(PUBLIC, target['declaration'])) == target['statement_hash']
for x in d['definitions']:
    assert x['exact_definition'] in s
write(RUN / 'transition-attempt-v1.lean', PUBLIC.read_bytes())
rc, out = capture('focused-transition-v1', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-3000:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'transition-attempt-result-v1.json', dict(actual_exit=rc, production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs, selected_proofs=1, total_materialized_proofs=8, materialized_definitions=2, frozen_hashes_unchanged=True, previous_proofs_unchanged=True, source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
