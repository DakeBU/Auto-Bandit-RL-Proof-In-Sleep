from common_proving_v1 import *
import re

s = proving_fixed()
assert load(RUN/'leaf-K5-attempt-v2.json')['mathematical_body_compiled']
assert not CANARY.exists()
proposal = RUN/'canary-proposal-v2.lean.txt'
code = proposal.read_text(encoding='utf8')
names = re.findall(r'^theorem (\w+)',code,re.M)
headers = [dict(name='Tests.OnlineGuessingKernelCausal.'+name,
                header=lean_declaration_header(proposal,name),
                statement_hash=statement_hash(lean_declaration_header(proposal,name))) for name in names]
write(RUN/'canary-frozen-targets-v2.json',dict(proposal_sha256=sha(proposal),
      targets=headers,selected_process='selectedSampler chooses K5 once before law/horizon',
      exact_values=dict(low_one='1/4',high_one='3/4',observation_variance='1/4',
        every_horizon_excess='T/4',zero_excess='0',two_round_excess='1/2'),
      switch='1 < last generated action + last observation; empty start uses low law',
      iid_observation_law='existing infinite Bernoulli(1/2) real stream, AE support only',
      canary_headers_frozen_before_first_actual_test_build=True,
      existing_five_production_targets_unchanged=True,
      source_body_and_canary_review_pending=True,package_accepted=False,chapter_complete=False,goal_complete=False))
write(RUN/'canary-plan-v2.md',
      'Frozen exact stochastic canary: low binary unit law has probability1=1/4 and high probability1=3/4; next-round law switches iff last generated action plus last observation exceeds1. Empty start low. Legal histories (action0,observation1), (action1,observation1), (action1,observation0) exhibit both action and observation dependence. Every history gives both atoms positive mass. ONE selected K5 sampler, same infinite process and existing real Bernoulli(1/2) IID observations. Instantiate all five public endpoints, prove binary prediction support from actual joint kernel law, target variance1/4, exact expected-fixed excessT/4 at EVERY naturalT, zero0 and two-roundpositive1/2. No per-horizon selection, current-independence input, pathwise/minE swap or all-protocol claim. Exact headers/raw proposal bound before first Test build; source BODY and canary semantic review still pending.\n')
native('lifecycle-proving-canary-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='public-nondegenerate-canary',attempt=1,
       frozen_targets_sha256=sha(RUN/'canary-frozen-targets-v2.json'),
       dependencies=['K1','K2','K3','K4','K5','existing IID Bernoulli test law'],
       package_accepted=False)))
CANARY.write_bytes(code.encode('utf8'))
proving_fixed()
for target in headers:
    assert statement_hash(lean_declaration_header(CANARY,target['name'])) == target['statement_hash']
write(RUN/'canary-attempt-v1.lean.raw',CANARY.read_bytes())
result = gate('canary-focused-v1','lake','build','Tests.OnlineGuessingKernelCausalCanary',required=False)
log = (RUN/'canary-focused-v1.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/Tests/OnlineGuessingKernelCausalCanary.olean'
compiled = result == 0 and 'Built Tests.OnlineGuessingKernelCausalCanary' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'canary-attempt-v1.json',dict(actual_exit=result,source_sha256=sha(CANARY),
      snapshot_sha256=sha(RUN/'canary-attempt-v1.lean.raw'),frozen_targets_sha256=sha(RUN/'canary-frozen-targets-v2.json'),
      public_source_sha256=sha(PUBLIC),mathematical_body_compiled=compiled,
      artifact_sha256=sha(artifact) if compiled else None,body_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('canary-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'Frozen stochastic binary kernel canary, actual generated action and observation feedback, all five public endpoints with one selected family, same-process all-T T/4 excess and positive target variance. Focused Test build only; source review and combined gates pending.',
       '--lean',CANARY.relative_to(ROOT).as_posix(),'--run-id',RUN.name,
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('Nondegenerate canary focused exit',result,'actual compiled',compiled,flush=True)
