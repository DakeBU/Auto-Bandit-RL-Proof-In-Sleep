from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

review_path = RUN/'actual-step-BODY-parent-window-review-v1.json'
assert sha(review_path) == 'd8fef4d6d41cf4243acaec98a8556d2f9d9e445b929da058c4e5167294ab3daf'
r = load(review_path)
assert r['inputs_unchanged'] and not r['required_blocking_repairs']
for row in r['raw_input_checks']:
    assert sha(row['path']) == row['expected_sha256'] == row['before_sha256'] == row['after_sha256']
assert sha(r['report']) == r['report_sha256']
w = r['approved_parent_append_window']
public = Path(w['path'])
assert sha(public) == w['before_sha256']
end = (w['movable_final_marker']+'\n').encode('utf8')
prefix = public.read_bytes()[:-len(end)]
assert public.read_bytes().endswith(end)
assert hashlib.sha256(prefix).hexdigest() == w['preserved_prefix_sha256']
assert sha(w['header_path']) == w['header_raw_sha256']
write(CONTRACT/'parent-stabilized-v1.json', dict(review_sha256=sha(review_path),
    allowed_window=w, boundary='One unchanged parent header/BODY only; source wrappers, benchmark and package gates remain required.'))
write(RUN/'worker-parent-route-v1.md', '''Before tactics: the actual compiled parent dependency TYPE probe and the reviewed director/architect route were read. Split T=0 and D=0 explicitly. For T>0,D>0 instantiate the weighted potential with actual squared distances and inclusive sqrt energy/(2 alpha D); diameter bounds its played distances and actual energy_step_mono supplies nondecreasing weights. Sum actual one_step, rewrite actual energy_eq_sum into the already compiled squared-norm energy sum bound, and multiply by nonnegative alpha D/2. Combine these bounds and only cancel positive alpha and D in the final algebra. Never cancel the total energy square root. The same actual run and negative terminal residual are retained. Local proof terms only; no added helpers/imports/context. Compiler failure snapshots and outputs are retained before BODY-only repair.
''')
event('parent-stabilized-event-v1', 'stabilized', dict(current_leaf='regret_bound',
    review_sha256=sha(review_path), allowed_window=w))
event('parent-proving-event-v1', 'proving', dict(current_leaf='regret_bound',
    route=sha(RUN/'worker-parent-route-v1.md'), allowed_file=public.as_posix()))
body = '''  by_cases hT : T = 0
  · subst T
    simp [regret, energy, state]
  by_cases hDz : D = 0
  · subst D
    obtain ⟨hr, hn⟩ := regret_zero_diameter V α loss x₁ p hx₁ T hdiam u hu
    simp [hr, hn]
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT
  have hp := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    (fun t => ‖output V α D loss x₁ p t - u‖ ^ 2)
    (fun t => Real.sqrt (energy V α D loss x₁ p (t + 1)) / (2 * α * D))
    (D ^ 2) T hTpos
    (by intro t ht; exact div_nonneg (Real.sqrt_nonneg _) (by positivity))
    (by
      intro t ht
      exact div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (energy_step_mono V α D loss x₁ p (t + 1))) (by positivity))
    (by
      intro t ht
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hdiam _ (output_mem V α D loss x₁ p hx₁ t) u hu) 2)
  have hidx : T - 1 + 1 = T := Nat.sub_add_cancel (by omega)
  simp only [hidx] at hp
  have he0 := BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix
    (selected V α D loss x₁ p) T
  have he1 : (∑ t ∈ range T, ‖selected V α D loss x₁ p t‖ ^ 2 /
      Real.sqrt (energy V α D loss x₁ p (t + 1))) ≤
      2 * Real.sqrt (energy V α D loss x₁ p T) := by
    simpa only [← energy_eq_sum V α D loss x₁ p] using he0
  have he := mul_le_mul_of_nonneg_left he1 (by positivity : 0 ≤ α * D / 2)
  have hs : regret V α D loss x₁ p u T ≤
      (∑ t ∈ range T, (‖output V α D loss x₁ p t - u‖ ^ 2 -
        ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2) *
        (Real.sqrt (energy V α D loss x₁ p (t + 1)) / (2 * α * D))) +
      α * D / 2 * (∑ t ∈ range T, ‖selected V α D loss x₁ p t‖ ^ 2 /
        Real.sqrt (energy V α D loss x₁ p (t + 1))) := by
    unfold regret
    calc
      _ ≤ ∑ t ∈ range T, ((‖output V α D loss x₁ p t - u‖ ^ 2 -
          ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2) *
          (Real.sqrt (energy V α D loss x₁ p (t + 1)) / (2 * α * D)) +
          α * D / 2 * (‖selected V α D loss x₁ p t‖ ^ 2 /
            Real.sqrt (energy V α D loss x₁ p (t + 1)))) := by
        apply sum_le_sum
        intro t ht
        simpa only [mul_div_assoc] using
          one_step V α D hα hDpos loss x₁ p t
            (hloss t (mem_range.mp ht)) (hlegal t (mem_range.mp ht)) u hu
      _ = _ := by rw [sum_add_distrib, mul_sum]
  calc
    regret V α D loss x₁ p u T ≤ _ := hs
    _ ≤ (D ^ 2 * (Real.sqrt (energy V α D loss x₁ p T) / (2 * α * D)) -
        ‖output V α D loss x₁ p T - u‖ ^ 2 *
          (Real.sqrt (energy V α D loss x₁ p T) / (2 * α * D))) +
        α * D / 2 * (2 * Real.sqrt (energy V α D loss x₁ p T)) := add_le_add hp he
    _ = _ := by
      field_simp [ne_of_gt hα, ne_of_gt hDpos]
      <;> ring
'''
public.write_bytes(prefix+b'\n'+Path(w['header_path']).read_bytes()+body.encode('utf8')+end)
assert public.read_bytes().startswith(prefix)
assert statement_hash(lean_declaration_header(public, 'regret_bound')) == w['normalized_statement_hash']
write(RUN/'parent-body-attempt-v1.lean.txt', public.read_bytes())
code, out = capture('parent-focused-build-v1', 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD', required=False)
print(out if code else '\n'.join(out.splitlines()[-8:]), flush=True)
if code:
    capture('parent-failed-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'failed',
        '--attempt-id', 'parent-body-v1', '--harness', 'hierarchical',
        '--obligations-before', '1', '--obligations-after', '1',
        '--verifier-evidence', RUN/'parent-focused-build-v1.json',
        '--notes', 'Actual parent compiler failure and complete source retained. Repair only this BODY; header and prefix unchanged.')
    sys.exit(code)
assert 'Build completed successfully' in out
write(RUN/'parent-compiled-local-v1.json', dict(production_sha256=sha(public),
    header=w, actual_focused_receipt_sha256=sha(RUN/'parent-focused-build-v1.json'),
    boundary='Actual focused compilation only. Public/axiom/VALUE/fence/independent BODY review and package gates pending.'))
