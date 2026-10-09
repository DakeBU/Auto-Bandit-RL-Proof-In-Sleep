from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
r = load(RUN / 'transition-attempt-result-v2.json')
assert r['compiled'] and r['actual_exit'] == 0 and r['production_sha256'] == sha(PUBLIC)
t = d['targets'][7]
probe = 'import BanditRLProof.OnlinePrescientBregman\nopen Set BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman\nnamespace PrescientTransitionAudit\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace \u211d E] [CompleteSpace E]\n'
probe += t['exact_proposed_header'].replace('theorem iterate_one_step', 'theorem public_VALUE')
probe += ' :=\n  ' + t['declaration'] + ' V hV \u03c8 \u03b7 loss x0 x p t hx hp h\u03b7 hf hs hdx hdp\n'
probe += '#check @' + t['declaration'] + '\n#print ' + t['declaration'] + '\n#print axioms ' + t['declaration'] + '\n#print axioms public_VALUE\nend PrescientTransitionAudit\n'
write(RUN / 'TransitionPublicAPIProbeV2.lean', probe)
_, out = capture('transition-public-VALUE-v2', 'lake', 'env', 'lean', RUN / 'TransitionPublicAPIProbeV2.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 2 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
assert '[NormedSpace' not in out and '[InnerProductSpace' in out and '[CompleteSpace' in out
_, out = capture('transition-public-lookup-v2', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', 'iterate_one_step', '--statement')
assert t['declaration'] in out
fence = (CONTRACT / 'transition-fence-v2.json').relative_to(ROOT).as_posix()
capture('transition-fence-command-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'statement-fence', '--declaration', t['declaration'], '--file', PUBLIC.relative_to(ROOT).as_posix(), '--output', fence)
capture('transition-safe-verify-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'safe-verify', '--fence', fence, '--lean-file', PUBLIC.relative_to(ROOT).as_posix())
assert load(ROOT / fence)['statement_hash'] == t['statement_hash']
for x in d['targets']:
    assert statement_hash(lean_declaration_header(PUBLIC, x['declaration'])) == x['statement_hash']
for x in d['definitions']:
    assert x['exact_definition'] in PUBLIC.read_text(encoding='utf8')
write(RUN / 'transition-inspected-v2.json', dict(production_sha256=sha(PUBLIC), compiled=True,
    full_generic_public_VALUE=1, standard_only_axiom_outputs=axioms,
    actual_context='NormedAddCommGroup + InnerProductSpace + CompleteSpace, no separate NormedSpace',
    all8_frozen_headers_unchanged=True, both_definition_bodies_unchanged=True,
    total_production_proofs=8, definitions=2, canaries_PENDING=True,
    BODY_PENDING=True, combined_gates_PENDING=True, package_accepted=False,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('transition-compiled-trial-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled', '--attempt-id', 'PC004-same-produced-transition-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', t['statement_hash'], '--obligations-before', '1', '--obligations-after', '0', '--verifier-evidence', RUN / 'transition-inspected-v2.json', '--notes', 'Actual same-produced-transition one-step derived after one preserved implementation-context failure; restored exact frozen inner-product context. Eight proofs/two definitions now focused/public/axiom/fence backed only. Canary/BODY/combined/publication/site/FINAL still pending; full source same-run cumulative terminals/chapter/Goal remain OPEN.')
old = (ROOT / 'runs/online-ch2-extended-proximal-20261009/export-production-dependencies-v1.lean').read_text(encoding='utf8')
start = old.index('def targets : Array Name := #[')
end = old.index('\n\ndef moduleName', start)
names = [x['declaration'] for x in d['targets'] + d['definitions']]
text = old[:start] + 'def targets : Array Name := #[\n' + ',\n'.join('`' + n for n in names) + ']' + old[end:]
text = text.replace('BanditRLProof.OnlineBregmanExtended', 'BanditRLProof.OnlinePrescientBregman')
text = text.replace('Three frozen EReal finite-domain bridge proofs, no Test nodes yet.', 'Eight frozen partial-causal/locality/actual-transition proofs and two exact definitions, no Test nodes yet.')
write(RUN / 'export-production-dependencies-v2.lean', text)
capture('production-dependency-command-v2', 'lake', 'env', 'lean', '--run', RUN / 'export-production-dependencies-v2.lean', RUN / 'production-dependency-data-v2.json')
graph = load(RUN / 'production-dependency-data-v2.json')
nodes = {n['name']: n for n in graph['nodes']}
assert set(names) <= set(nodes) and all(n['has_value'] for n in nodes.values())
ps = 'BanditRL.OnlinePrescientBregman.'
pairs = [[ps + 'advance_some_spec', ps + 'advance'],
    [ps + 'advance_none_iff', ps + 'advance'],
    [ps + 'iterate_succ_some_spec', ps + 'advance_some_spec'],
    [ps + 'iterate_complete_of_step_attained', ps + 'advance_none_iff'],
    [ps + 'iterate_one_step', ps + 'iterate_succ_some_spec'],
    [ps + 'iterate_one_step', 'BanditRL.OnlineBregman.proximal_one_step_extended']]
for a, b in pairs:
    assert b in nodes[a]['value_dependencies'], (a, b)
write(RUN / 'production-dependency-inspected-v2.json', dict(selected_nodes=len(nodes),
    requested_canonical_nodes=len(names), additional_compiler_nodes=sorted(set(nodes) - set(names)),
    coalesced_direct_TYPE_VALUE_presences=len(graph['edges']), required_actual_VALUE_pairs=pairs,
    graph_sha256=sha(RUN / 'production-dependency-data-v2.json'), production_sha256=sha(PUBLIC),
    not_full_transitive_graph=True, not_registry_or_source_denominator=True,
    source_container_closed=False, whole_Goal_status='ACTIVE'))
fixed()
print('Eight actual frozen proof bodies/two definitions audited; BODY and canaries remain pending.')
