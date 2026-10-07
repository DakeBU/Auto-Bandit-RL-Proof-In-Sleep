from common_integrated_v1 import *
fixed_integrated()
assert load(RUN/'integrated-gates-v1.json')['status'].startswith('Actual root/Tests/fullharness')
gate('scope-before-source-commit-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','before-source-commit-v1')
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Prove causal logarithmic guessing regret lower bound']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(child.stdout.decode('utf8',errors='replace'),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Clean scoped source commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
