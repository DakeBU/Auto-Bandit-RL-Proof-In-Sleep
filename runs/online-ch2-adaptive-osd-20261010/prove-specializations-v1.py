from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
review_path = RUN/'specialization-CONTRACT-review-v1.json'
assert sha(review_path) == 'afdb90eeaf54e573132bb55571c266d1dbf91e9b871a77730740f600b6891b8d'
r = load(review_path)
assert r['inputs_unchanged'] and not r['required_blocking_repairs']
for x in r['raw_input_checks']:
    assert sha(x['path']) == x['expected_sha256'] == x['before_sha256'] == x['after_sha256']
assert sha(r['report']) == r['report_sha256']
w = r['approved_conditional_edit_window']
public = Path(w['path'])
assert sha(public) == w['before_sha256']
end = (w['movable_final_marker']+'\n').encode('utf8')
assert public.read_bytes().endswith(end)
prefix = public.read_bytes()[:-len(end)]
assert hashlib.sha256(prefix).hexdigest() == w['preserved_prefix_sha256']
headers = r['approved_headers']
for row in headers.values():
    assert sha(row['path']) == row['raw_sha256']
write(CONTRACT/'specialization-stabilized-v1.json', dict(review_sha256=sha(review_path),
    context_sha256=r['context_sha256'], exact_headers=headers, allowed_window=w))
write(RUN/'worker-specializations-route-v1.md', '''Before tactics: actual named declarations/type probe/retrieval and the distinct exact CONTRACT review were read. Source alpha1: instantiate actual parent and drop only its nonnegative residual; normalize coefficient3/2. Source sqrt2/2: prove that fixed alpha positive and coefficient=sqrt2 by sqrt2²=2, drop only nonnegative residual, and use sqrt_mul2 to match printed Dsqrt(2S). D0 and zero energy never require cancellation of D or energy here. Each canonical adapter calls its matching source endpoint and actual canonical_feedback with identical alpha/run. Keep every hconvex binder even if unused by the sufficient-support parent. Append/build one source BODY at a time, then one canonical BODY at a time, stopping at failure. Four exact headers/prefix unchanged, no new top-level helper/import/context. Actual failures retained; only BODY repairs allowed.
''')
event('specialization-stabilized-event-v1', 'stabilized', dict(current_leaf='source_eq4_4',
    review_sha256=sha(review_path), exact_headers=headers, allowed_window=w))
bodies = {
'source_eq4_4': '''  have h := regret_bound V 1 D (by norm_num) hD loss x₁ p hx₁ T hloss hlegal hdiam u hu
  calc
    regret V 1 D loss x₁ p u T ≤
        (1 / (2 * (1 : ℝ)) + 1) * D * Real.sqrt (energy V 1 D loss x₁ p T) :=
      h.trans (sub_le_self _ (by positivity))
    _ = _ := by norm_num
''',
'source_theorem4_14': '''  have hα : 0 < Real.sqrt (2 : ℝ) / 2 := by positivity
  have hc : 1 / (2 * (Real.sqrt (2 : ℝ) / 2)) + Real.sqrt 2 / 2 = Real.sqrt 2 := by
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hn]
    nlinarith [hs]
  have h := regret_bound V (Real.sqrt 2 / 2) D hα hD loss x₁ p hx₁ T hloss hlegal hdiam u hu
  calc
    regret V (Real.sqrt 2 / 2) D loss x₁ p u T ≤
        (1 / (2 * (Real.sqrt 2 / 2)) + Real.sqrt 2 / 2) * D *
          Real.sqrt (energy V (Real.sqrt 2 / 2) D loss x₁ p T) :=
      h.trans (sub_le_self _ (by positivity))
    _ = _ := by
      rw [hc, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
      ring
''',
'canonical_eq4_4': '''  exact source_eq4_4 V D hD loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy hx₁ T
    hconvex hloss (canonical_feedback V 1 D loss x₁ hx₁ T hloss) hdiam u hu
''',
'canonical_theorem4_14': '''  exact source_theorem4_14 V D hD loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy hx₁ T
    hconvex hloss (canonical_feedback V (Real.sqrt 2 / 2) D loss x₁ hx₁ T hloss) hdiam u hu
'''}
completed = []
for group in w['groups']:
    for name in group:
        assert public.read_bytes() == prefix+end
        event('specialization-'+name+'-proving-event-v1', 'proving', dict(current_leaf=name,
            preceding_focused_successes=completed, allowed_file=public.as_posix()))
        addition = b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
        public.write_bytes(prefix+addition+end)
        assert public.read_bytes().startswith(prefix)
        assert statement_hash(lean_declaration_header(public, name)) == headers[name]['normalized_statement_hash']
        write(RUN/('specialization-'+name+'-body-attempt-v1.lean.txt'), public.read_bytes())
        label = 'specialization-'+name+'-focused-build-v1'
        code, out = capture(label, 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD', required=False)
        print(out if code else '\n'.join(out.splitlines()[-7:]), flush=True)
        if code:
            capture('specialization-'+name+'-failed-trial-v1', sys.executable, '-B', '-X', 'utf8',
                RUN/'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt',
                '--status', 'failed', '--attempt-id', 'specialization-'+name+'-body-v1',
                '--harness', 'hierarchical', '--obligations-before', '4', '--obligations-after', '4',
                '--verifier-evidence', RUN/(label+'.json'),
                '--notes', 'Actual compiler failure/full snapshot retained. Stop downstream append; repair only this BODY with exact header and previous prefix unchanged.')
            sys.exit(code)
        assert 'Build completed successfully' in out
        write(RUN/('specialization-'+name+'-compiled-local-v1.json'), dict(
            production_sha256=sha(public), header=headers[name],
            focused_receipt_sha256=sha(RUN/(label+'.json')), boundary='Focused only, not package acceptance.'))
        completed.append(dict(name=name, focused_receipt_sha256=sha(RUN/(label+'.json'))))
        prefix += addition
print('Four exact source/canonical performance BODYs compiled sequentially; benchmark and full package still open.', flush=True)
