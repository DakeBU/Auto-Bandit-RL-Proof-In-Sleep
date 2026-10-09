from leaf_driver import *
guard()
prior=load(RUN/'seven-leaf-public-axiom-v1.json')
out=base64.b64decode(prior['stdout_base64']).decode('utf8')
assert prior['actual_exit']==0 and 'sorryAx' not in out
lines=[line for line in out.splitlines() if 'depends on axioms:' in line]
assert len(lines)==7 and all(line.endswith('[propext, Classical.choice, Quot.sound]') for line in lines)
write(RUN/'seven-leaf-audit-wrapper-repair-v2.json',dict(actual_Lean_exit=prior['actual_exit'],prior_wrapper_failure='post-success audit expected wrong text axioms[ instead of actual depends on axioms: [',change='Inspect seven exact actual axiom lines from retained successful compiler receipt; no compiler rerun or production mutation',actual_lines=lines))
script=(RUN/'audit-seven-leaves-v1.py').read_text(encoding='utf8')
start=script.index("write(RUN/'seven-leaf-public-inspected-v1.json'")
leaves=[('currentSubgradient_affine','selector',2),('step_affine_fullSpace','step_affine_fullSpace',1),('iterate_affine_prefix','iterate_affine_prefix',1),('powerSteps_pos','powerSteps_pos',1),('phi_limit','phi_limit',2),('switching_loss_regular','switching_loss_regular',2),('phi_range','phi_range',3)]
code=prior['actual_exit']
exec(compile(script[start:],str(RUN/'audit-seven-leaves-v1.py')+':unexecuted-tail','exec'))
