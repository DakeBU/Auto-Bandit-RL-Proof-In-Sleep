from common_proving_v1 import *

proving_fixed()
assert not load(RUN/'canary-attempt-v1.json')['mathematical_body_compiled']
before = CANARY.read_bytes()
source = before.decode('utf8')
changes = [
('''  norm_num [lowLaw]
''','''  norm_num [lowLaw]
  change (3 / 4 : ℝ≥0∞) + 1 / 4 = 1
  rw [← ENNReal.add_div]
  norm_num
'''),
('''  norm_num [highLaw]
''','''  norm_num [highLaw]
  change (1 / 4 : ℝ≥0∞) + 3 / 4 = 1
  rw [← ENNReal.add_div]
  norm_num
'''),
('''def decisionKernel (t : ℕ) : Kernel (KernelDecisionHistory t) I :=
  Kernel.piecewise (switchSet_measurable t)
''','''def decisionKernel (t : ℕ) : Kernel (KernelDecisionHistory t) I := by
  classical
  exact Kernel.piecewise (switchSet_measurable t)
'''),
('''  exact Measure.ae_of_ae_map
''','''  exact ae_of_ae_map
'''),
('''    refine ⟨(by fun_prop).aemeasurable, (observation_measurable t).aemeasurable, ?_⟩
''','''    have ht : Measurable (target t) := by
      fun_prop
    refine ⟨ht.aemeasurable, (observation_measurable t).aemeasurable, ?_⟩
''')]
for old,new in changes:
    assert source.count(old) == 1, old
    source = source.replace(old,new)
write(RUN/'canary-repair-v2.json',dict(failed_actual_exit=1,
      failed_source_sha256=sha(RUN/'canary-attempt-v1.lean.raw'),
      failed_log_sha256=sha(RUN/'canary-focused-v1.log'),
      errors=['ENNReal mass addition not solved by norm_num alone',
        'piecewise predicate lacked local classical decidability',
        'ae_of_ae_map is in MeasureTheory, not Measure',
        'untyped by fun_prop in IdentDistrib constructor'],
      repair='Explicit ENNReal.add_div, classical annotation, correct namespace, typed measurable target',
      no_production_change=True,no_canary_header_or_mathematical_definition_change=True,
      compiler_inserted_sorry_in_failed_output_not_accepted=True,previous_failure_retained=True))
native('lifecycle-repair-canary-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='public-nondegenerate-canary',attempt=2,
       failure='ENNReal mass/decidability/namespace/elaboration repairs, frozen headers and mathematical kernel intact')))
CANARY.write_bytes(source.encode('utf8'))
proving_fixed()
for target in load(RUN/'canary-frozen-targets-v2.json')['targets']:
    assert statement_hash(lean_declaration_header(CANARY,target['name'])) == target['statement_hash']
write(RUN/'canary-attempt-v2.lean.raw',CANARY.read_bytes())
result = gate('canary-focused-v2','lake','build','Tests.OnlineGuessingKernelCausalCanary',required=False)
log = (RUN/'canary-focused-v2.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/Tests/OnlineGuessingKernelCausalCanary.olean'
compiled = result == 0 and 'Built Tests.OnlineGuessingKernelCausalCanary' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0 and \
    'declaration uses `sorry`' not in log
if result == 0:
    assert compiled
write(RUN/'canary-attempt-v2.json',dict(actual_exit=result,source_sha256=sha(CANARY),
      snapshot_sha256=sha(RUN/'canary-attempt-v2.lean.raw'),frozen_targets_sha256=sha(RUN/'canary-frozen-targets-v2.json'),
      public_source_sha256=sha(PUBLIC),mathematical_body_compiled=compiled,
      artifact_sha256=sha(artifact) if compiled else None,body_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('canary-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'Same frozen stochastic canary and exact T/4/variance1/4 terminal; repair ENNReal sum, classical piecewise, namespace and typed measurable target. Failed compiler placeholders retained only as failure evidence; actual successful build required and separate axiom/body/full gates pending.',
       '--lean',CANARY.relative_to(ROOT).as_posix(),'--run-id',RUN.name,
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('Canary repaired focused exit',result,'actual compiled',compiled,flush=True)
