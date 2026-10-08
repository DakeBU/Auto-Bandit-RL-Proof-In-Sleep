from common_proving_v1 import *

proving_fixed()
assert not load(RUN/'canary-attempt-v2.json')['mathematical_body_compiled']
before = CANARY.read_bytes()
source = before.decode('utf8')
for law,expr in [('lowLaw','(3 / 4 : ℝ≥0∞) + 1 / 4'),('highLaw','(1 / 4 : ℝ≥0∞) + 3 / 4')]:
    old = '  norm_num ['+law+']\n  change '+expr+' = 1\n'
    new = '  simp only ['+law+', Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]\n'
    assert source.count(old) == 1, old
    source = source.replace(old,new)
old = '''    have ht : Measurable (target t) := by
      fun_prop
'''
new = '''    have ht : Measurable (target t) :=
      (measurable_pi_apply t).comp measurable_snd
'''
assert source.count(old) == 1
source = source.replace(old,new)
write(RUN/'canary-repair-v3.json',dict(failed_actual_exit=1,
      failed_source_sha256=sha(RUN/'canary-attempt-v2.lean.raw'),
      failed_log_sha256=sha(RUN/'canary-focused-v2.log'),
      errors=['norm_num changed 1/4 to inverse4 before change; equality not definitional',
        'fun_prop did not unfold local target definition'],
      classification='API normalization, no mathematical counterexample or missing hypothesis',
      repair='Use simp-only to retain common denominators; explicit measurable coordinate composition',
      no_production_change=True,no_canary_header_or_mathematical_definition_change=True,
      all_previous_failures_retained=True))
native('lifecycle-repair-canary-v3','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='public-nondegenerate-canary',attempt=3,
       failure='Preserve ENNReal common denominators and explicit target measurability; exact mathematical quantities unchanged')))
CANARY.write_bytes(source.encode('utf8'))
proving_fixed()
for target in load(RUN/'canary-frozen-targets-v2.json')['targets']:
    assert statement_hash(lean_declaration_header(CANARY,target['name'])) == target['statement_hash']
write(RUN/'canary-attempt-v3.lean.raw',CANARY.read_bytes())
result = gate('canary-focused-v3','lake','build','Tests.OnlineGuessingKernelCausalCanary',required=False)
log = (RUN/'canary-focused-v3.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/Tests/OnlineGuessingKernelCausalCanary.olean'
compiled = result == 0 and 'Built Tests.OnlineGuessingKernelCausalCanary' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0 and \
    'declaration uses `sorry`' not in log
if result == 0:
    assert compiled
write(RUN/'canary-attempt-v3.json',dict(actual_exit=result,source_sha256=sha(CANARY),
      snapshot_sha256=sha(RUN/'canary-attempt-v3.lean.raw'),frozen_targets_sha256=sha(RUN/'canary-frozen-targets-v2.json'),
      public_source_sha256=sha(PUBLIC),mathematical_body_compiled=compiled,
      artifact_sha256=sha(artifact) if compiled else None,body_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('canary-trial-v3','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'Same frozen canary; explicit measure-univ sum retains common denominator and direct coordinate measurability resolves elaboration. Two earlier failures retained; source review and full gates pending.',
       '--lean',CANARY.relative_to(ROOT).as_posix(),'--run-id',RUN.name,
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('Canary repaired focused exit',result,'actual compiled',compiled,flush=True)
