from common_integrated_v2 import *
fixed_integrated();assert load(RUN/'integrated-gates-v3.json')['committed_production_paths']==6
assert load(RUN/'scoped-diff-v4-exit.json')['exit_code']==0
gate('source-scope-before-clean-site-v4',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','before-clean-site-v4')
owned=load(RUN/'owned-commit-paths-v2.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Bind actual no-regret combined gates and preserve raw review evidence']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-9:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Clean source and applicable gate evidence',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
