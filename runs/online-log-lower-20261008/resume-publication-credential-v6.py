from common_accepted_v1 import *
accepted_fixed()
assert load(RUN/'branch-push-v1-exit.json')['exit_code']==128
assert 'denied to iclr-artifact2027' in (RUN/'branch-push-v1.log').read_text(encoding='utf8')
account=json.loads(subprocess.check_output(['gh','api','user']))['login']
permissions=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep']))['permissions']
assert account=='jicheng9617' and permissions['push'],(account,permissions)
write(RUN/'credential-repair-v6.json',dict(failed_push='branch-push-v1',cached_Git_manager_account='iclr-artifact2027',actual_GH_account=account,repository_permissions=permissions,repair='Per-command empty credential.helper then gh auth git-credential; no global account or credential change, no credential material logged.',proof_reader_review_unchanged=True,chapter_complete=False,goal_complete=False))
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Preserve denied push and scope publishing credentials to research account']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-4:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
source=(RUN/'publish-reviewed-v4.py').read_text(encoding='utf8')
tail=source[source.index("head=subprocess.check_output"):]
tail=tail.replace("gate('branch-push-v1','git','push'","gate('branch-push-v2','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push'")
exec(compile(tail,'publish-reviewed-v4-tail-with-v6-per-command-GH-credential','exec'))
