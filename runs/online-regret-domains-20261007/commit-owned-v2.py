from common_v1 import *
fixed(integrated=True)
assert load(RUN/'integrated-gates-v3.json')['committed_production_paths']==4
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','--quiet','-m',sys.argv[1]]]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if child.stdout:print(child.stdout.decode('utf-8',errors='replace'),flush=True)
 assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Actual scoped clean commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
