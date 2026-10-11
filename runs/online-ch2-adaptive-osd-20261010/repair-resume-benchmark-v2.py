from common import *
import ast
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

review = load(RUN/'specialization-BODY-benchmark-CONTRACT-review-v1.json')
assert sha(RUN/'specialization-BODY-benchmark-CONTRACT-review-v1.json') == 'be46ad291de3d6ea9fba1b8f19a6a2791757747322d673ee7d6ebe122d3c9fb7'
for row in review['raw_input_checks']:
    assert sha(row['path']) == row['expected_sha256'] == row['before_sha256'] == row['after_sha256']
assert sha(review['report']) == review['report_sha256']
window = review['approved_conditional_edit_window']
public = Path(window['path'])
headers = load(CONTRACT/'benchmark-fingerprints-draft-v1.json')['headers']
original = RUN/'prove-benchmark-v1.py'
tree = ast.parse(original.read_text(encoding='utf8'))
bodies = next(ast.literal_eval(node.value) for node in tree.body if isinstance(node, ast.Assign)
    and any(isinstance(t, ast.Name) and t.id == 'bodies' for t in node.targets))
failed = RUN/'benchmark-benchmark_isGLB-body-attempt-v1.lean.txt'
assert public.read_bytes() == failed.read_bytes()
failure = load(RUN/'benchmark-benchmark_isGLB-focused-build-v1.json')
assert failure['actual_exit'] != 0
old = '          field_simp [ne_of_gt hDpos, ne_of_gt hbpos]\n'
assert bodies['benchmark_isGLB'].count(old) == 1
bodies['benchmark_isGLB'] = bodies['benchmark_isGLB'].replace(old, old+'          ring\n')
write(RUN/'benchmark-local-algebra-repair-v2.json', dict(
    classification='Local tactic algebra closure; no mathematical or representation change.',
    failure_receipt_sha256=sha(RUN/'benchmark-benchmark_isGLB-focused-build-v1.json'),
    failed_snapshot_sha256=sha(failed), original_driver_sha256=sha(original),
    edit='Append ring after field_simp only in first theorem BODY.',
    residual='b ^ 2 + D ^ 2 * 0 = b ^ 2', unchanged_headers=headers,
    permission='Already reviewed BODY-only repair window; downstream append requires success.'))
prefix = Path(window['context_path']).read_bytes()
end = b'end BanditRL.OnlineAdaptiveBenchmark\n'
completed = []
for index, name in enumerate(n for group in window['ordered_groups'] for n in group):
    version = 'v2' if index == 0 else 'v1'
    if index:
        assert public.read_bytes() == prefix+end
        event('benchmark-'+name+'-proving-event-'+version, 'proving', dict(
            current_leaf=name, preceding_focused_successes=completed, allowed_file=public.as_posix()))
    addition = b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
    public.write_bytes(prefix+addition+end)
    assert public.read_bytes().startswith(prefix)
    assert statement_hash(lean_declaration_header(public, name)) == headers[name]['normalized_statement_hash']
    write(RUN/('benchmark-'+name+'-body-attempt-'+version+'.lean.txt'), public.read_bytes())
    label = 'benchmark-'+name+'-focused-build-'+version
    code, out = capture(label, 'lake', 'build', 'BanditRLProof.OnlineAdaptiveBenchmark', required=False)
    print(out if code else '\n'.join(out.splitlines()[-7:]), flush=True)
    if code:
        capture('benchmark-'+name+'-failed-trial-'+version, sys.executable, '-B', '-X', 'utf8',
            RUN/'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt',
            '--status', 'failed', '--attempt-id', 'benchmark-'+name+'-body-'+version,
            '--harness', 'hierarchical', '--obligations-before', '5', '--obligations-after', str(5-index),
            '--verifier-evidence', RUN/(label+'.json'),
            '--notes', 'Actual focused failure and full snapshot retained; stop downstream append. Exact frozen header/context unchanged.')
        sys.exit(code)
    assert 'Build completed successfully' in out
    write(RUN/('benchmark-'+name+'-compiled-local-'+version+'.json'), dict(
        production_sha256=sha(public), header=headers[name],
        focused_receipt_sha256=sha(RUN/(label+'.json')), boundary='Focused only; public/review/package gates open.'))
    completed.append(dict(name=name, focused_receipt_sha256=sha(RUN/(label+'.json'))))
    prefix += addition
print('All five unchanged benchmark/source-conjunction BODYs compiled in prerequisite order.', flush=True)
