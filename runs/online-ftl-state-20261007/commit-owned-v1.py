from common_v1 import *
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()==BRANCH
for cmd in [['git','add','--',*load(RUN/'owned-commit-paths-v1.json')],['git','commit','-m',sys.argv[1]]]:
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)
print(subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
