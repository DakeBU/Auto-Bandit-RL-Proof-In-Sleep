from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
review_path = RUN/'specialization-BODY-benchmark-CONTRACT-review-v1.json'
assert sha(review_path) == 'be46ad291de3d6ea9fba1b8f19a6a2791757747322d673ee7d6ebe122d3c9fb7'
r = load(review_path)
assert r['inputs_unchanged'] and not r['required_blocking_repairs']
for x in r['raw_input_checks']:
    assert sha(x['path']) == x['expected_sha256'] == x['before_sha256'] == x['after_sha256']
assert sha(r['report']) == r['report_sha256']
w = r['approved_conditional_edit_window']
public = Path(w['path'])
assert not public.exists() and w['create_only']
assert sha(w['context_path']) == w['context_sha256']
headers = load(CONTRACT/'benchmark-fingerprints-draft-v1.json')['headers']
for row in w['headers']:
    assert sha(row['path']) == row['sha256'] == headers[row['target']]['raw_sha256']
write(CONTRACT/'benchmark-stabilized-v1.json', dict(review_sha256=sha(review_path),
    exact_headers=headers, allowed_window=w, source_endpoint_BODY_verdict=r['source_BODY_verdict']))
write(RUN/'worker-benchmark-route-v1.md', '''Before tactics: actual frozen OnlineOptimalStep and Mathlib declarations were retrieved, TYPE-probed and read; exact five headers and distinct source endpoint BODY/benchmark CONTRACT verdicts were read. GLB lower bound uses shared lower_bound/sqrt_sq. Greatestness tests any larger lower bound b: positive coefficients use actual D/sqrtS optimizer; bothzero tests eta1; D0,Spositive tests eta=b/S and Dpositive,S0 tests eta=D²/b, each objective b/2<b. Thus arbitrary closeness, not strict decrease alone, proves GLB. The source scalar factor uses IsGLB.csInf_eq with actual eta1 witness then sqrt_mul. Attainment iff rejects mixed zeros with shared strict-improvement plus shared lower_bound, accepts bothzero via zero_coefficients and positive via distance_energy_argmin. Positive minimum reuses full value/lower/equality-unique APIs. Final source conjunction calls actual source_theorem4_14 and scalar factor at its actual nonnegative energy, retaining both components. Five unchanged headers, exact new context, no helper/definition or old-source edit. Each leaf focus-builds before downstream append; retain real failures and repair only current BODY.
''')
event('benchmark-stabilized-event-v1', 'stabilized', dict(current_leaf='benchmark_isGLB',
    review_sha256=sha(review_path), exact_headers=headers, allowed_window=w))
bodies = {
'benchmark_isGLB': '''  refine ⟨?_, ?_⟩
  · rintro b ⟨η, hη, rfl⟩
    simpa only [Real.sqrt_sq hD] using
      BanditRL.OnlineOptimalStep.lower_bound (D ^ 2) S η (sq_nonneg D) hS hη
  · intro b hb
    by_contra hle
    have hgt : D * Real.sqrt S < b := lt_of_not_ge hle
    by_cases hDz : D = 0
    · subst D
      have hbpos : 0 < b := by simpa using hgt
      by_cases hSz : S = 0
      · subst S
        have hlow := hb (show BanditRL.OnlineOptimalStep.upperBound (0 ^ 2) 0 1 ∈
            {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (0 ^ 2) 0 η} from
          ⟨1, by norm_num, rfl⟩)
        have hzero : b ≤ 0 := by simpa [BanditRL.OnlineOptimalStep.upperBound] using hlow
        exact (not_lt_of_ge hzero) hbpos
      · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
        have hlow := hb (show BanditRL.OnlineOptimalStep.upperBound (0 ^ 2) S (b / S) ∈
            {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (0 ^ 2) S η} from
          ⟨b / S, div_pos hbpos hSpos, rfl⟩)
        have hv : BanditRL.OnlineOptimalStep.upperBound (0 ^ 2) S (b / S) = b / 2 := by
          simp [BanditRL.OnlineOptimalStep.upperBound, div_mul_cancel₀ _ (ne_of_gt hSpos)]
        rw [hv] at hlow
        linarith
    · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
      by_cases hSz : S = 0
      · subst S
        have hbpos : 0 < b := by simpa using hgt
        have hlow := hb (show BanditRL.OnlineOptimalStep.upperBound (D ^ 2) 0 (D ^ 2 / b) ∈
            {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) 0 η} from
          ⟨D ^ 2 / b, div_pos (sq_pos_of_pos hDpos) hbpos, rfl⟩)
        have hv : BanditRL.OnlineOptimalStep.upperBound (D ^ 2) 0 (D ^ 2 / b) = b / 2 := by
          dsimp [BanditRL.OnlineOptimalStep.upperBound]
          field_simp [ne_of_gt hDpos, ne_of_gt hbpos]
        rw [hv] at hlow
        linarith
      · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
        have hlow := hb (show BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S (D / Real.sqrt S) ∈
            {b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η} from
          ⟨D / Real.sqrt S, div_pos hDpos (Real.sqrt_pos.mpr hSpos), rfl⟩)
        rw [(BanditRL.OnlineOptimalStep.distance_energy_argmin D S hDpos hSpos).2.1] at hlow
        exact (not_lt_of_ge hlow) hgt
''',
'source_benchmark_value': '''  have hglb := benchmark_isGLB D S hD hS
  have hne : {b : ℝ | ∃ η : ℝ, 0 < η ∧
      b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η}.Nonempty :=
    ⟨BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S 1, 1, by norm_num, rfl⟩
  rw [hglb.csInf_eq hne, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  ring
''',
'benchmark_attained_iff': '''  constructor
  · rintro ⟨η, hη, hval⟩
    by_cases hDz : D = 0
    · by_cases hSz : S = 0
      · exact Or.inr ⟨hDz, hSz⟩
      · exfalso
        subst D
        have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
        have hv : BanditRL.OnlineOptimalStep.upperBound 0 S η = 0 := by simpa using hval
        have hdec := BanditRL.OnlineOptimalStep.zero_distance_decreases S η hSpos hη
        have hlow := BanditRL.OnlineOptimalStep.lower_bound 0 S (η / 2) (by norm_num) hS hdec.1
        simp only [Real.sqrt_zero, zero_mul] at hlow
        rw [hv] at hdec
        exact (not_lt_of_ge hlow) hdec.2
    · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
      by_cases hSz : S = 0
      · exfalso
        subst S
        simp only [Real.sqrt_zero, mul_zero] at hval
        have hdec := BanditRL.OnlineOptimalStep.zero_energy_decreases (D ^ 2) η (sq_pos_of_pos hDpos) hη
        have hlow := BanditRL.OnlineOptimalStep.lower_bound (D ^ 2) 0 (2 * η) (sq_nonneg D) (by norm_num) hdec.1
        simp only [Real.sqrt_zero, mul_zero] at hlow
        rw [hval] at hdec
        exact (not_lt_of_ge hlow) hdec.2
      · exact Or.inl ⟨hDpos, lt_of_le_of_ne hS (Ne.symm hSz)⟩
  · rintro (⟨hDpos, hSpos⟩ | ⟨rfl, rfl⟩)
    · exact ⟨D / Real.sqrt S, div_pos hDpos (Real.sqrt_pos.mpr hSpos),
        (BanditRL.OnlineOptimalStep.distance_energy_argmin D S hDpos hSpos).2.1⟩
    · exact ⟨1, by norm_num, by norm_num [BanditRL.OnlineOptimalStep.upperBound]⟩
''',
'benchmark_positive_minimum': '''  have hs := BanditRL.OnlineOptimalStep.distance_energy_argmin D S hD hS
  refine ⟨div_pos hD (Real.sqrt_pos.mpr hS), hs.2.1, ?_⟩
  intro η hη
  constructor
  · simpa only [hs.2.1] using hs.2.2 η hη
  · simpa only [hs.1, hs.2.1] using
      BanditRL.OnlineOptimalStep.optimal_unique (D ^ 2) S η (sq_pos_of_pos hD) hS hη
''',
'source_theorem4_14_infimum': '''  exact ⟨BanditRL.OnlineAdaptiveOSD.source_theorem4_14 V D hD loss x₁ p hx₁ T
      hconvex hloss hlegal hdiam u hu,
    source_benchmark_value D (energy V (Real.sqrt 2 / 2) D loss x₁ p T) hD
      (energy_nonneg V (Real.sqrt 2 / 2) D loss x₁ p T)⟩
'''}
prefix = Path(w['context_path']).read_bytes()
end = b'end BanditRL.OnlineAdaptiveBenchmark\n'
completed = []
for group in w['ordered_groups']:
    for name in group:
        if public.exists():
            assert public.read_bytes() == prefix+end
        event('benchmark-'+name+'-proving-event-v1', 'proving', dict(current_leaf=name,
            preceding_focused_successes=completed, allowed_file=public.as_posix()))
        addition = b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
        public.write_bytes(prefix+addition+end)
        assert public.read_bytes().startswith(prefix)
        assert statement_hash(lean_declaration_header(public, name)) == headers[name]['normalized_statement_hash']
        write(RUN/('benchmark-'+name+'-body-attempt-v1.lean.txt'), public.read_bytes())
        label = 'benchmark-'+name+'-focused-build-v1'
        code, out = capture(label, 'lake', 'build', 'BanditRLProof.OnlineAdaptiveBenchmark', required=False)
        print(out if code else '\n'.join(out.splitlines()[-7:]), flush=True)
        if code:
            capture('benchmark-'+name+'-failed-trial-v1', sys.executable, '-B', '-X', 'utf8',
                RUN/'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt',
                '--status', 'failed', '--attempt-id', 'benchmark-'+name+'-body-v1',
                '--harness', 'hierarchical', '--obligations-before', '5', '--obligations-after', '5',
                '--verifier-evidence', RUN/(label+'.json'),
                '--notes', 'Actual benchmark compiler failure/full snapshot retained. Stop downstream append; only current BODY repair allowed, exact header/context unchanged.')
            sys.exit(code)
        assert 'Build completed successfully' in out
        write(RUN/('benchmark-'+name+'-compiled-local-v1.json'), dict(
            production_sha256=sha(public), header=headers[name],
            focused_receipt_sha256=sha(RUN/(label+'.json')), boundary='Focused only, not package/source/chapter acceptance.'))
        completed.append(dict(name=name, focused_receipt_sha256=sha(RUN/(label+'.json'))))
        prefix += addition
print('Five exact benchmark/repaired source-conjunction BODYs compiled sequentially; public/review/full package still open.', flush=True)
