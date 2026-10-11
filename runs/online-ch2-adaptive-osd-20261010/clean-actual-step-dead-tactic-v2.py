from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
before = public.read_bytes()
assert before == (RUN/'actual-step-group-D-body-attempt-v1.lean.txt').read_bytes()
assert load(RUN/'actual-step-group-D-focused-build-v1.json')['actual_exit'] == 0
dead = b'        <;> ring\n'
assert before.count(dead) == 1
after = before.replace(dead, b'', 1)
public.write_bytes(after)
headers = load(CONTRACT/'actual-step-stabilized-v1.json')['exact_headers']
for name, row in headers.items():
    assert statement_hash(lean_declaration_header(public, name)) == row['normalized_statement_hash']
write(RUN/'actual-step-group-D-body-attempt-v2.lean.txt', after)
write(RUN/'actual-step-dead-tactic-cleanup-v2.json', dict(
    before_sha256=hashlib.sha256(before).hexdigest(), after_sha256=sha(public),
    previous_actual_exit=0, compiler_failure=False,
    only_change='Delete the one unused/unreachable ring after field_simp already closed the final algebraic goal.',
    headers_unchanged=True, prior_group_C_prefix_preserved=True,
    boundary='Lint cleanup in current unreviewed group D BODY only; original successful source/full output retained.'))
code, out = capture('actual-step-group-D-focused-build-v2', 'lake', 'build',
    'BanditRLProof.OnlineAdaptiveOSD', required=False)
print('\n'.join(out.splitlines()[-10:]), flush=True)
sys.exit(code)
