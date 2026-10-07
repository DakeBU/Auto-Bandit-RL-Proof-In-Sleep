from pathlib import Path
import subprocess
root=Path.cwd();assert root.as_posix()=='E:/ABRL/worktrees/research-online-book'
run=root/'runs/online-unit-scaling-public-20261007'
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()=='f4f48c9c199248530a068677af536d673665c73d'
assert all(s.startswith('?? runs/online-unit-scaling-public-20261007/') for s in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).splitlines())
text=(root/'runs/online-optimal-step-public-20261007/common_v1.py').read_text(encoding='utf-8')
for a,b in [('frozen-coefficient minimization','unit-coordinate scaling'),('5c5fecd69a90c16f29f2d630ab6c167cd9e61e06','f4f48c9c199248530a068677af536d673665c73d'),('ONLINE-OPTIMAL-STEP-PUBLIC','ONLINE-UNIT-SCALING-PUBLIC'),('online-optimal-step','online-unit-scaling'),('OnlineOptimalStep','OnlineUnitScaling'),('OptimalStepProbe','UnitScalingProbe')]:text=text.replace(a,b)
for name,value in [('common_v1.py',text),('.gitattributes','* -text\n')]:
 p=run/name;assert not p.exists();p.write_bytes(value.encode('utf-8'))
print('Bounded unit-scaling helpers initialized; no source/proof edit.')
