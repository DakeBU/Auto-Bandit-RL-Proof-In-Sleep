from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
r = load(RUN / 'advance-attempt-result-v3.json')
assert r['compiled'] and r['actual_exit'] == 0 and r['production_sha256'] == sha(PUBLIC)
d = load(CONTRACT / 'stabilized-v1.json')
probe = 'import BanditRLProof.OnlinePrescientBregman\nopen Set BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman\nnamespace PrescientAdvanceAudit\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace \u211d E]\n'
arguments = ['V \u03c8 \u03b7 f x p h', 'V \u03c8 \u03b7 f x']
for t, args in zip(d['targets'][1:3], arguments):
    name = t['declaration'].split('.')[-1]
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
    probe += t['exact_proposed_header'].replace('theorem ' + name, 'theorem public_VALUE_' + name)
    probe += ' :=\n  ' + t['declaration'] + ' ' + args + '\n'
    probe += '#check ' + t['declaration'] + '\n#print ' + t['declaration'] + '\n#print axioms ' + t['declaration'] + '\n#print axioms public_VALUE_' + name + '\n'
for x in d['definitions']:
    assert x['exact_definition'] in PUBLIC.read_text(encoding='utf8')
    probe += '#print ' + x['declaration'] + '\n#print axioms ' + x['declaration'] + '\n'
probe += 'end PrescientAdvanceAudit\n'
write(RUN / 'AdvancePublicAPIProbeV3.lean', probe)
_, out = capture('advance-public-VALUE-v3', 'lake', 'env', 'lean', RUN / 'AdvancePublicAPIProbeV3.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
no_axioms = re.findall(r'does not depend on any axioms', out)
assert len(axioms) + len(no_axioms) == 6 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
for i, t in enumerate(d['targets'][1:3]):
    _, out = capture('advance-public-lookup-' + str(i) + '-v3', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', t['declaration'].split('.')[-1], '--statement')
    assert t['declaration'] in out
    fence = (CONTRACT / ('advance-fence-' + str(i) + '-v3.json')).relative_to(ROOT).as_posix()
    capture('advance-fence-command-' + str(i) + '-v3', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'statement-fence', '--declaration', t['declaration'], '--file', PUBLIC.relative_to(ROOT).as_posix(), '--output', fence)
    capture('advance-safe-verify-' + str(i) + '-v3', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'safe-verify', '--fence', fence, '--lean-file', PUBLIC.relative_to(ROOT).as_posix())
    assert load(ROOT / fence)['statement_hash'] == t['statement_hash']
write(RUN / 'advance-inspected-v3.json', dict(production_sha256=sha(PUBLIC), compiled=True,
    full_generic_public_VALUE=2, standard_only_axiom_outputs=axioms,
    no_axiom_outputs=len(no_axioms), definition_bodies_unchanged=True,
    frozen_headers_unchanged=True, other_proofs_pending=5,
    canaries_PENDING=True, BODY_PENDING=True, combined_gates_PENDING=True,
    package_accepted=False, source_container_closed=False, chapter_complete=False,
    whole_Goal_status='ACTIVE'))
capture('advance-compiled-trial-v3', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled', '--attempt-id', 'PC002-current-minimum-specs-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', d['targets'][1]['statement_hash'], '--obligations-before', '2', '--obligations-after', '0', '--verifier-evidence', RUN / 'advance-inspected-v3.json', '--notes', 'Only two current-minimum specifications focused-compiled after two preserved body failures. Exact definitions, full generic public VALUE, axiom and native fence evidence inspected. Five causal/transition proofs, canaries, BODY/combined/reader/site/package acceptance and full source terminals remain OPEN.')
fixed()
