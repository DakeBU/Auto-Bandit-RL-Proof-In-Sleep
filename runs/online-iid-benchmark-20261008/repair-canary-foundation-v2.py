from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'canary-foundation-focused-build-v1-exit.json')['exit_code'] == 1
write(RUN / 'failed-canary-foundation-v1.lean.raw', CANARY.read_bytes())
write(RUN / 'canary-foundation-repair-v2.json', dict(
    actual_failure='Missing ENNReal notation scope; lambda/id rewrite mismatch; explicit measure inference; normalize real numerals and rewrite mean before unfolding observation.',
    repair='Canary proof/context API edits only; all eight public statements/bodies unchanged.',
    corrected_prior_theorem_count=16, prior_count_18_included_two_probability_instances=True,
    public_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
text = CANARY.read_text(encoding='utf8')
text = text.replace('namespace Tests.OnlineGuessingIIDBenchmark', 'open scoped ENNReal\nnamespace Tests.OnlineGuessingIIDBenchmark', 1)
text = text.replace('variance_eq_integral measurable_id.aemeasurable',
    'variance_eq_integral (X := fun x : ℝ => x) (μ := coinLaw) measurable_id.aemeasurable')
text = text.replace('  simpa [observation_variance] using h', '  norm_num [observation_variance] at h\n  exact h')
text = text.replace('have hv := variance_eq_integral (observation_measurable 0).aemeasurable',
    'have hv := variance_eq_integral (μ := iidLaw) (observation_measurable 0).aemeasurable')
text = text.replace('  simpa [Finset.sum_range_succ, meanPredict, empiricalMean, observation, observation_mean,\n    hcenter] using he',
    '  simp_rw [observation_mean] at he\n  simp [Finset.sum_range_succ, meanPredict, empiricalMean, observation] at he\n  exact he.trans hcenter')
CANARY.write_bytes(text.encode('utf8'))
write(RUN / 'canary-foundation-candidate-v2.lean.raw', CANARY.read_bytes())
gate('canary-foundation-focused-build-v2', 'lake', 'build', 'Tests.OnlineGuessingIIDBenchmarkCanary')
headers_fixed(8)
