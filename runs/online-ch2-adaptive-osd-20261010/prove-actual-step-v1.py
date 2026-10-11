from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
review_path = RUN/'actual-step-CONTRACT-review-v1.json'
assert sha(review_path) == '9d56738b6c6760881ef1b293b048550e2c75e3d94d59a8db236a16fdccb7ffb9'
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
end = (w['movable_final_marker']+'\n').encode('utf8')
assert public.read_bytes().endswith(end)
prefix = public.read_bytes()[:-len(end)]
assert hashlib.sha256(prefix).hexdigest() == w['preserved_prefix_sha256']
write(CONTRACT/'actual-step-stabilized-v1.json', dict(
    review_sha256=sha(review_path), context_sha256=r['context_sha256'], exact_headers=headers,
    allowed_window=w, parent_regret='required, BODY not authorized'))
write(RUN/'worker-actual-step-route-v1.md', '''Before tactics: actual pinned API declaration/memory/source windows and compiled API TYPE probe were read and recorded. A rewrites energy_succ and uses nonnegative/positive norm squares. B obtains positive eta from positive inclusive energy, proves exact zero skip via output_succ and nonpositive gap via lemma_2_31 eta1 support half, and derives zero-diameter equal points from actual output_mem. C adapts both shared lemma_2_31 inequalities to actual nonzero output_succ. D splits current zero vector: explicit skip gives zero distance change/residual; otherwise divide the actual positive-eta chain and rewrite eta_eq_energy, cancelling only verified nonzero alpha,D,sqrt energy. One lower route, no extra helper/import/context, all seven frozen headers unchanged. Retain actual failure source/output and stop downstream group append until repair compiles.
''')
event('actual-step-stabilized-event-v1', 'stabilized', dict(current_leaf='energy_step_mono',
    review_sha256=sha(review_path), exact_headers=headers, parent_regret='frozen open'))
bodies = {
'energy_step_mono': '''  rw [energy_succ]
  linarith [sq_nonneg ‖selected V α D loss x₁ p t‖]
''',
'energy_pos_of_selected_ne_zero': '''  rw [energy_succ]
  exact add_pos_of_nonneg_of_pos (energy_nonneg V α D loss x₁ p t)
    (sq_pos_of_pos (norm_pos_iff.mpr hg))
''',
'eta_pos_of_selected_ne_zero': '''  rw [eta_eq_energy]
  exact div_pos (mul_pos hα hD)
    (Real.sqrt_pos.mpr (energy_pos_of_selected_ne_zero V α D loss x₁ p t hg))
''',
'zero_feedback_step': '''  refine ⟨?_, ?_⟩
  · rw [output_succ, if_pos hz]
  · have hs := (BanditRL.OnlineSubgradientDescent.lemma_2_31 V (loss t) hloss
        1 (by norm_num) (output V α D loss x₁ p t) u hu (selected V α D loss x₁ p t) hg).1
    simpa only [hz, inner_zero_left, one_mul] using hs
''',
'regret_zero_diameter': '''  have heq : ∀ t, output V α 0 loss x₁ p t = u := by
    intro t
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (hdiam _ (output_mem V α 0 loss x₁ p hx₁ t) u hu) (norm_nonneg _)
  constructor
  · simp only [regret, heq, sub_self, sum_const_zero]
  · rw [heq T, sub_self, norm_zero]
''',
'one_step_chain': '''  have hη := eta_pos_of_selected_ne_zero V α D hα hD loss x₁ p t hnz
  simpa only [output_succ, if_neg hnz] using
    BanditRL.OnlineSubgradientDescent.lemma_2_31 V (loss t) hloss
      (eta V α D loss x₁ p t) hη (output V α D loss x₁ p t) u hu
      (selected V α D loss x₁ p t) hg
''',
'one_step': '''  by_cases hz : selected V α D loss x₁ p t = 0
  · obtain ⟨hskip, hgap⟩ := zero_feedback_step V α D loss x₁ p t hloss hg hz u hu
    simpa [hskip, hz] using hgap
  · have hη := eta_pos_of_selected_ne_zero V α D hα hD loss x₁ p t hz
    have hs := one_step_chain V α D hα hD loss x₁ p t hloss hg hz u hu
    have hroot : 0 < Real.sqrt (energy V α D loss x₁ p (t + 1)) :=
      Real.sqrt_pos.mpr (energy_pos_of_selected_ne_zero V α D loss x₁ p t hz)
    apply le_of_mul_le_mul_left (a := eta V α D loss x₁ p t) _ hη
    calc
      eta V α D loss x₁ p t *
          ((loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal) ≤
          ‖output V α D loss x₁ p t - u‖ ^ 2 / 2 -
          ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
          (eta V α D loss x₁ p t) ^ 2 / 2 * ‖selected V α D loss x₁ p t‖ ^ 2 := hs.1.trans hs.2
      _ = _ := by
        simp only [eta_eq_energy]
        field_simp [ne_of_gt hα, ne_of_gt hD, ne_of_gt hroot]
        <;> ring
'''}
completed = []
for letter, names in zip('ABCD', w['groups']):
    assert public.read_bytes() == prefix+end
    event('actual-step-group-'+letter+'-proving-event-v1', 'proving', dict(current_leaf=names[0],
        exact_group=names, preceding_group_focused_receipts=completed, allowed_file=public.as_posix()))
    addition = b''
    for name in names:
        addition += b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
    public.write_bytes(prefix+addition+end)
    assert public.read_bytes().startswith(prefix)
    for name in names:
        assert statement_hash(lean_declaration_header(public, name)) == headers[name]['normalized_statement_hash']
    write(RUN/('actual-step-group-'+letter+'-body-attempt-v1.lean.txt'), public.read_bytes())
    label = 'actual-step-group-'+letter+'-focused-build-v1'
    code, out = capture(label, 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD', required=False)
    print(out if code else '\n'.join(out.splitlines()[-6:]), flush=True)
    if code:
        capture('actual-step-group-'+letter+'-failed-trial-v1', sys.executable, '-B', '-X', 'utf8',
            RUN/'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt',
            '--status', 'failed', '--attempt-id', 'actual-step-group-'+letter+'-body-v1',
            '--harness', 'hierarchical', '--obligations-before', '7', '--obligations-after', '7',
            '--verifier-evidence', RUN/(label+'.json'),
            '--notes', 'Actual compiler failure retained with exact source snapshot; no downstream append/header weakening.')
        sys.exit(code)
    assert 'Build completed successfully' in out
    write(RUN/('actual-step-group-'+letter+'-compiled-local-v1.json'), dict(
        production_sha256=sha(public), exact_group=names, header_hashes={n:headers[n] for n in names},
        actual_focused_receipt_sha256=sha(RUN/(label+'.json')),
        preserved_previous_prefix_sha256=hashlib.sha256(prefix).hexdigest(),
        boundary='Actual focused compilation only; public, BODY-review and combined gates pending.'))
    completed.append(dict(group=letter, focused_receipt_sha256=sha(RUN/(label+'.json'))))
    prefix += addition
print('Seven actual same-run one-step dependencies compiled in four ordered groups; parent open.', flush=True)
