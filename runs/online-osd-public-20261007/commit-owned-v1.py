import subprocess,sys,json
from pathlib import Path
paths=json.loads((Path(__file__).resolve().parent/'owned-commit-paths-v1.json').read_text(encoding='utf-8'))
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-osd-migration'
for cmd in [['git','add','--',*paths],['git','commit','-m',sys.argv[1]]]:
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)
print(subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
