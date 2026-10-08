from common_canary_v1 import *

canary_fixed()
assert not load(RUN/'canary-attempt-v3.json')['mathematical_body_compiled']
assert load(RUN/'canary-mass-api-audit-v1-exit.json')['actual_exit'] == 0
source = CANARY.read_text(encoding='utf8')
old = '  rw [← ENNReal.add_div]\n  norm_num\n'
assert source.count(old) == 2
write(RUN/'canary-contract-failure-audit-v1.json',dict(
      repeated_failed_attempts=[1,2,3],actual_final_errors=['two measure_univ goals 4/4=1'],
      mathematics='Both binary laws total mass (3+1)/4=1. ENNReal division requires denominator positive and finite.',
      actual_pinned_API='ENNReal.div_self (h0 : a != 0) (hI : a != top)',
      compiled_separate_API_probe=sha(RUN/'canary-mass-api-audit-v1.log'),probe_actual_exit=0,
      no_source_target_counterexample_or_weakening=True,
      decidability_and_measurability_repairs_now_elaborate=True,
      stochastic_history_feedback_and_exact_terminal_unchanged=True,
      remaining_repair='Discharge explicit nonzero/finite denominator conditions with pinned div_self',
      all_previous_failures_retained=True,package_accepted=False))
native('lifecycle-repair-canary-v4','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='public-nondegenerate-canary',attempt=4,
       audited_math_and_actual_API=True,failure='Two ENNReal div_self goals, explicit denominator conditions from successful separate probe')))
CANARY.write_bytes(source.replace(old,old+'  exact ENNReal.div_self (by norm_num) (by norm_num)\n').encode('utf8'))
compile_canary_attempt(4,
    'Repeated canary errors audited against frozen math and actual pinned API: only two total-mass 4/4=1 goals remained; separate div_self probe compiled. Explicit nonzero/finite conditions, no target weakening or production change. Prior failures retained; source/body and combined gates pending.')
