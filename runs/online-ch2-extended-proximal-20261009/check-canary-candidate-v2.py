from common import *
import re
fixed()
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
build = load(RUN / 'focused-canary-build-v3.json')
assert build['actual_exit'] == 0 and sha(PUBLIC) == d['production_sha256']
old_tails = load(RUN / 'numeric-tail-data-v1.json')
assert all(r['selected_tail_head'] == 'id' for r in old_tails['rows'])
write(RUN / 'numeric-tail-audit-repair-v2.json', dict(
    failed_candidate_validator='check-canary-candidate-v1.py', actual_validator_exit=1,
    raw_selector_output_sha256=sha(RUN / 'numeric-tail-data-v1.json'),
    cause='The let-bound Test result leaves an explicit id wrapper; old selector stopped at whole conjunction.',
    repair='Also peel the explicit two-argument id application, then inline lets and descend rightmost And.intro.',
    does_not_unfold_theorems=True, does_not_use_proof_irrelevance_normalization=True,
    no_individual_numeric_tail_claim_from_v1=True, production_and_Test_unchanged=True,
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
s = (RUN / 'audit-numeric-tail-v1.lean').read_text(encoding='utf8')
assert s.count('    if e.getAppFn.isConstOf ``And.intro') == 1
s = s.replace('    if e.getAppFn.isConstOf ``And.intro',
    '    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then\n      numericTail e.getAppArgs[1]!\n    else if e.getAppFn.isConstOf ``And.intro')
s = s.replace('Inline top-level lets by substitution, remove metadata, descend',
    'Inline top-level lets by substitution, remove metadata and explicit id wrappers, descend')
write(RUN / 'audit-numeric-tail-v2.lean', s)
capture('numeric-tail-command-v2', 'lake', 'env', 'lean', '--run', RUN / 'audit-numeric-tail-v2.lean', RUN / 'numeric-tail-data-v2.json')
tails = load(RUN / 'numeric-tail-data-v2.json')
assert all(t['public_helper_in_selected_tail'] and t['selected_tail_head'] == 'Eq.mp' for t in tails['rows'])
out = base64.b64decode(load(RUN / 'canary-public-VALUE-kernel-v1.json')['stdout_base64']).decode('utf8')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 4
suffix = (RUN / 'check-canary-candidate-v1.py').read_text(encoding='utf8').split("old = (RUN / 'export-production-dependencies-v1.lean')", 1)[1]
suffix = "old = (RUN / 'export-production-dependencies-v1.lean')" + suffix
suffix = suffix.replace('numeric-tail-data-v1.json', 'numeric-tail-data-v2.json')
suffix = suffix.replace("assert len(nodes) == 5 and len(pairs) == 12", "assert len(nodes) >= 5 and len(pairs) == 12")
suffix = suffix.replace("    'Three frozen EReal finite-domain bridge proofs and two full public infinity-domain canary conjunctions.')", "    'Three frozen EReal finite-domain bridge proofs and two full public infinity-domain canary conjunctions, including referenced generated Test auxiliaries.')\nold = old.replace('dep.toString.startsWith \\\"_private.Tests.OnlineBregmanExtendedCanary.\\\"', '(dep.toString.startsWith \\\"_private.Tests.OnlineBregmanExtendedCanary.\\\" || dep.toString.startsWith \\\"BanditRL.OnlineBregmanExtendedCanary.\\\")')")
suffix = suffix.replace("    coalesced_direct_TYPE_VALUE_presences=len(graph['edges']), required_actual_VALUE_pairs=pairs,", "    coalesced_direct_TYPE_VALUE_presences=len(graph['edges']), required_actual_VALUE_pairs=pairs,\n    generated_Test_auxiliaries=[n for n in nodes if n not in {t['declaration'] for t in d['targets']} and n.startswith('BanditRL.OnlineBregmanExtendedCanary.')],")
suffix = suffix.replace("print('Actual two public canary VALUEs/four standard axiom outputs/two individual Eq.mp helper tails/five-node graph inspected.')", "print('Actual public canary VALUEs/axioms and individual Eq.mp helper tails inspected; selected graph includes referenced generated Test auxiliaries.')")
exec(compile(suffix, str(RUN / 'check-canary-candidate-v1.py') + ':repaired-validator-suffix-v2', 'exec'))
