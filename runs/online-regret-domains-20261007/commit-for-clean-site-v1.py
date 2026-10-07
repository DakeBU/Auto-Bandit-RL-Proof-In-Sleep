from common_v1 import *
fixed(integrated=True)
assert load(RUN/'integrated-gates-v2.json')['status'].startswith('Actual root/Tests/fullharness-v2')
gate('source-scope-before-clean-site-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','before-clean-site-v1')
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Audit typed action and comparator domains for shared regret']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(child.stdout.decode('utf-8',errors='replace'),flush=True)
 assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
print('Clean applicable-site source commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
