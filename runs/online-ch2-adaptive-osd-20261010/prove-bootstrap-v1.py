from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

review_path = RUN/'bootstrap-CONTRACT-review-v1.json'
assert sha(review_path) == '86eaa4f2962d88cba3e4b1fbabeeb31e7f57577fd4c554448c66ce7953c2fdb8'
r = load(review_path)
assert not r['required_repairs'] and r['inputs_unchanged']
for row in r['raw_input_checks']:
    assert sha(row['path']) == row['expected_sha256'] == row['before_sha256'] == row['after_sha256']
assert sha(r['report']) == r['report_sha256']
assert sha(r['input_manifest']) == r['input_manifest_sha256']
headers = r['approved_headers']
for row in headers.values():
    assert sha(row['path']) == row['raw_sha256']
w = r['approved_conditional_edit_window']
public = Path(w['path'])
assert sha(public) == w['before_sha256']
end = w['movable_final_marker'].encode('utf8')
assert public.read_bytes().endswith(end)
prefix = public.read_bytes()[:-len(end)]
assert hashlib.sha256(prefix).hexdigest() == w['preserved_prefix_sha256']
write(CONTRACT/'bootstrap-stabilized-v1.json', dict(
    review_sha256=sha(review_path), context_sha256=r['definition_context_sha256'],
    exact_headers=headers, allowed_window=w, parent_regret='required, BODY not authorized'))
write(RUN/'worker-bootstrap-route-v1.md', '''Before tactics, actual project_spec/finite_loss/OracleLaw/canonicalPolicy_legal declarations and prior history_mem implementation were retrieved and read. A takes pair/last-coordinate projections of compiled state_succ. B uses energy induction, finite history induction with zero-skip vs projection feasibility, and inclusive eta rewriting. C projects feasible last entry and nonnegative norm-square sum. D applies shared finite_loss twice and OracleLaw to actual generated finite inputs. E reuses existing canonicalPolicy_legal, never a new chooser. One route, exact all-ten headers/context, no extra helper declarations/imports. Each successful actual focused group build is prerequisite to production append of downstream group. Failed groups keep exact source/log and stop downstream writing.
''')
event('bootstrap-stabilized-event-v1', 'stabilized', dict(
    current_leaf='energy_succ', review_sha256=sha(review_path),
    headers=headers, allowed_groups=w['groups'], parent_regret='open frozen'))
bodies = {
'energy_succ': '''  change (state V α D loss x₁ p (t + 1)).2 = _
  rw [state_succ]
''',
'output_succ': '''  simp only [output, history, state_succ, Fin.snoc_last]
''',
'energy_eq_sum': '''  induction T with
  | zero => simp [energy, state]
  | succ T ih => rw [energy_succ, sum_range_succ, ih]
''',
'history_mem': '''  induction t with
  | zero => simpa only [history, state] using hx₁
  | succ t ih =>
    change (state V α D loss x₁ p (t + 1)).1 i ∈ V.carrier
    rw [state_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      split_ifs with hg
      · exact ih (Fin.last t)
      · exact (BanditRL.OnlineGradientDescent.project_spec V _).1
    · simpa only [Fin.snoc_castSucc] using ih j
''',
'eta_eq_energy': '''  unfold eta
  rw [energy_succ]
''',
'output_mem': '''  exact history_mem V α D loss x₁ p hx₁ t (Fin.last t)
''',
'energy_nonneg': '''  rw [energy_eq_sum]
  exact sum_nonneg (fun _ _ => sq_nonneg _)
''',
'trajectory_finite_loss': '''  exact ⟨BanditRL.OnlineSubgradientDescent.finite_loss V (loss t) hloss _
      (output_mem V α D loss x₁ p hx₁ t),
    BanditRL.OnlineSubgradientDescent.finite_loss V (loss t) hloss u hu⟩
''',
'oracle_feedback': '''  intro t ht
  exact hp t (fun i => loss i.val) (history V α D loss x₁ p t) (loss t)
    (hloss t ht) (output_mem V α D loss x₁ p hx₁ t)
''',
'canonical_feedback': '''  exact oracle_feedback V α D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy
    hx₁ T (BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal V) hloss
'''}
completed = []
for letter, names in zip('ABCDE', w['groups']):
    assert public.read_bytes() == prefix+end
    event('bootstrap-group-'+letter+'-proving-event-v1', 'proving', dict(
        current_leaf=names[0], exact_group=names,
        preceding_group_focused_receipts=completed,
        allowed_file=public.as_posix(), parent_regret='required open'))
    addition = b''
    for name in names:
        addition += b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
    public.write_bytes(prefix+addition+end)
    assert public.read_bytes().startswith(prefix)
    for name in names:
        assert statement_hash(lean_declaration_header(public, name)) == headers[name]['normalized_statement_hash']
    write(RUN/('bootstrap-group-'+letter+'-body-attempt-v1.lean.txt'), public.read_bytes())
    label = 'bootstrap-group-'+letter+'-focused-build-v1'
    code, out = capture(label, 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD', required=False)
    print(out if code else '\n'.join(out.splitlines()[-6:]), flush=True)
    if code:
        capture('bootstrap-group-'+letter+'-failed-trial-v1', sys.executable, '-B', '-X', 'utf8',
            RUN/'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower',
            '--kind', 'attempt', '--status', 'failed', '--attempt-id', 'bootstrap-group-'+letter+'-body-v1',
            '--harness', 'hierarchical', '--obligations-before', '10', '--obligations-after', '10',
            '--verifier-evidence', RUN/(label+'.json'),
            '--notes', 'Actual focused compiler failure; exact group snapshot retained; downstream not written, no header/context weakening.')
        sys.exit(code)
    assert 'Build completed successfully' in out
    write(RUN/('bootstrap-group-'+letter+'-compiled-local-v1.json'), dict(
        production_sha256=sha(public), exact_group=names, header_hashes={n:headers[n] for n in names},
        actual_focused_receipt_sha256=sha(RUN/(label+'.json')),
        preserved_previous_prefix_sha256=hashlib.sha256(prefix).hexdigest(),
        boundary='Focused compiled BODYs only; semantic BODY and combined gates pending.'))
    completed.append(dict(group=letter, focused_receipt_sha256=sha(RUN/(label+'.json'))))
    prefix += addition
print('All five dependency-ordered groups actually built; parent regret remains open.', flush=True)
