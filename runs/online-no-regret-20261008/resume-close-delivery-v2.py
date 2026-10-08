from common_accepted_v1 import *
accepted_fixed()
assert load(RUN/'delivery-obligations-overlay-v1.json')['PR_number']==192
assert load(RUN/'contributor-delivery-v1-exit.json')['exit_code']==0
gate('scoped-diff-delivery-v6',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v6.py','delivery-v6')
gate('source-scope-delivery-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','delivery-v1')
accepted_fixed()
for command in [['git','add','--',*load(RUN/'owned-commit-paths-v2.json')],['git','commit','-m','Record no-regret draft PR delivery and remaining whole-book obligations']]:
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('\n'.join(result.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True)
    assert result.returncode==0,command
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
print('Delivery commit',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),'; next scoped push and direct raw audit.')
