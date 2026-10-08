from commit_owned_v1 import *

fixed_integrated()
assert load(RUN/'contributor-candidate-stacked-v1-exit.json')['actual_exit'] == 0
assert load(RUN/'contributor-candidate-origin-main-v1-exit.json')['actual_exit'] == 0
commit_owned('Record causal kernel candidate contributor evidence')
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
command = [sys.executable,'-B','-X','utf8',str(RUN/'build-clean-site-v1.py')]
child = subprocess.run(command)
write(RUN/'clean-local-site-workflow-v1-exit.json',dict(command=command,actual_exit=child.returncode,
    outer_stdout_inherited=True,inner_build_check_registry_logs_separately_saved=True))
assert child.returncode == 0
