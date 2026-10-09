from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
result = load(RUN / 'first-leaf-attempt-result-v1.json')
assert result['actual_exit'] == 0 and result['compiled'] and sha(PUBLIC) == result['production_sha256']
t = load(CONTRACT / 'stabilized-v1.json')['targets'][0]
assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
probe = 'import BanditRLProof.OnlinePrescientBregman\nopen Set BanditRL.OnlineBregman\nnamespace PrescientLocalityAudit\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace \u211d E]\n'
probe += t['exact_proposed_header'].replace('theorem divergence_extension_eq', 'theorem public_VALUE')
probe += ' :=\n  BanditRL.OnlineBregman.divergence_extension_eq X \u03c8 \u03c6 hEq a b ha hb\n'
probe += '#check ' + t['declaration'] + '\n#print ' + t['declaration'] + '\n#print axioms ' + t['declaration'] + '\n#print axioms public_VALUE\nend PrescientLocalityAudit\n'
write(RUN / 'FirstLeafPublicAPIProbe.lean', probe)
_, out = capture('first-leaf-public-VALUE-v1', 'lake', 'env', 'lean', RUN / 'FirstLeafPublicAPIProbe.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 2 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
_, out = capture('first-leaf-public-lookup-v1', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', 'divergence_extension_eq', '--statement')
assert t['declaration'] in out
fence = (CONTRACT / 'first-leaf-fence-v1.json').relative_to(ROOT).as_posix()
capture('first-leaf-fence-command-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'statement-fence', '--declaration', t['declaration'], '--file', PUBLIC.relative_to(ROOT).as_posix(), '--output', fence)
capture('first-leaf-safe-verify-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'safe-verify', '--fence', fence, '--lean-file', PUBLIC.relative_to(ROOT).as_posix())
assert load(ROOT / fence)['statement_hash'] == t['statement_hash']
write(RUN / 'first-leaf-inspected-v1.json', dict(declaration=t['declaration'], production_sha256=sha(PUBLIC), compiled=True, actual_cached_inclusive_build_jobs=result['actual_cached_inclusive_build_jobs'], full_generic_public_VALUE=1, standard_only_axiom_outputs=axioms, frozen_hash_unchanged=True, other_proofs_pending=7, definitions_unmaterialized=2, canaries_PENDING=True, BODY_PENDING=True, combined_gates_PENDING=True, package_accepted=False, source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('first-leaf-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled', '--attempt-id', 'PC001-extension-locality-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', t['statement_hash'], '--obligations-before', '1', '--obligations-after', '0', '--verifier-evidence', RUN / 'first-leaf-inspected-v1.json', '--notes', 'Only first frozen locality proof focused-compiled, full generic public VALUE/two standard-only axiom outputs/frozen native guard actual0. No canary/BODY/combined/reader/site/package acceptance. Other7proofs/two definitions and fullsource/interior source transport/same-run fixed-variable/all8forwards/Goal remain OPEN.')
fixed()
print('First locality leaf actual focused/public-VALUE/axiom/fence evidence inspected; package remains proving.')
