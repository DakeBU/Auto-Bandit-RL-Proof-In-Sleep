from common import *
fixed()
st=load(CONTRACT/'stabilized-v1.json'); t=st['targets'][0]
old=RUN/'first-leaf-public-probe-v1.lean'
assert load(RUN/'first-leaf-public-probe-command-v1.json')['actual_exit']==1
assert sha(PUBLIC)==load(RUN/'first-leaf-focused-inspected-v1.json')['proof_sha256']
probe=old.read_text(encoding='utf8')
bad='("type",toJson (← ppExpr info.type).pretty)'
assert probe.count(bad)==1
probe=probe.replace(bad,'("type_dependencies",toJson (info.type.getUsedConstantsAsSet.toArray.map Name.toString))').replace('first-leaf-value-graph-v1.json','first-leaf-value-graph-v2.json')
write(RUN/'first-leaf-public-probe-v2.lean',probe)
write(RUN/'first-leaf-probe-failure-repair-v2.json',dict(failure='Actual v1 public probe exit1: ppExpr not available in CommandElab context. Full generic example/check/axiom text preceded error but entire probe NOT successful.', prior_receipt_sha256=sha(RUN/'first-leaf-public-probe-command-v1.json'),prior_probe_sha256=sha(old),current_probe_sha256=sha(RUN/'first-leaf-public-probe-v2.lean'),repair='Replace unsupported diagnostic pretty-printer with actual type constant dependency list; use new output filename. Generic statement/application, value and actual-parent checks unchanged.', production_or_statement_changed=False,module_sha256=sha(PUBLIC)))
code,out=capture('first-leaf-public-probe-command-v2','lake','env','lean',RUN/'first-leaf-public-probe-v2.lean',required=False)
assert code==0 and 'ACTUAL-FIRST-LEAF-VALUE-PARENT-CHECKED' in out,(code,out)
assert 'sorryAx' not in out and 'Classical.choice' in out and 'propext' in out and 'Quot.sound' in out
g=load(RUN/'first-leaf-value-graph-v2.json')
assert g['actual_theorem_value'] and 'BanditRL.OnlinePrescientBregman.iterate_one_step' in g['value_dependencies']
write(RUN/'first-leaf-public-inspected-v2.json',dict(actual_exit=code, complete_generic_example=True, actual_value=True,required_parent_value='BanditRL.OnlinePrescientBregman.iterate_one_step',axiom_outputs=1,standard_only_axioms=['propext','Classical.choice','Quot.sound'],generic_context_and_statement_unchanged=True,module_sha256=sha(PUBLIC),concrete_canary='pending',package_acceptance=False))
write(RUN/'pre-first-compiled-native-exact-v2.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']]))
event('native-first-focused-compiled-event-v2','focused-compiled',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],module_sha256=sha(PUBLIC),focused_exit=0,value_parent='actual iterate_one_step',public_value_probe_exit=0,prior_probe_exit=1,canary='pending',package_candidate=False,source_container_closed=False,whole_Goal_status='ACTIVE'))
capture('native-first-focused-trial-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','proof','--status','compiled','--run-id',RUN.name,'--attempt-id','actual-shared-cumulative-sum-v1','--lean',PUBLIC.relative_to(ROOT),'--statement-hash',t['statement_sha256'],'--progress-class','compiled-leaf','--verifier-evidence',RUN/'first-leaf-focused-inspected-v1.json','--verifier-evidence',RUN/'first-leaf-public-inspected-v2.json','--notes','Actual new focused module Built and complete generic public theorem VALUE with actual iterate_one_step parent. Exact frozen header unchanged. Diagnostic probe v1 ppExpr failure retained, v2 repaired without production change. Generic proof compiled only: concrete canary/package BODY/integration/root/fullharness/site/source/chapter acceptance pending. Whole Goal ACTIVE.')
write(RUN/'first-leaf-BODY-review-inputs-v1.json',dict(rows=rows(list(CONTRACT.glob('*'))+[PUBLIC]+[p for p in RUN.glob('*') if p.is_file() and p.suffix!='.png' and not p.name.startswith('CLI-help')]),permitted_prospective_next_leaves=['iterate_fixed_sharp','iterate_variable_sharp'],no_terminal_change=True,concrete_canary_and_package_acceptance_pending=True,whole_Goal_status='ACTIVE'))
fixed()
print('Full first public application/value/standard-axiom probe v2 passed. Package canaries/gates pending.')
print(out[-700:])
