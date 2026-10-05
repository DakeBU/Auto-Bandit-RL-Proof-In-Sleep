"""Prepare checks for the same ten retained shared declaration-registry nodes."""
from pathlib import Path
run=Path(__file__).parent
old=Path('runs/online-ogd-migration-20261005')
text=(old/'verify-registry-final02.py').read_text(encoding='utf-8')
for a,b in [('online-ogd-migration-site-final02','online-ftl-migration-site-final01'),
    ('OnlineGradientDescentSource','OnlineFTLFailure'),('BanditRL.OnlineFTLFailure.','BanditRL.OnlineLearning.'),
    ('len(names)==14','len(names)==10'),('teaching:online-ogd','teaching:online-ftl-failure'),
    ('online-unit-scaling-site-final02','online-ogd-migration-site-final02'),
    ('registry-final02.json','registry-final01.json')]:text=text.replace(a,b)
with (run/'verify-registry-final01.py').open('w',encoding='utf-8',newline='\n') as f:f.write(text)
text=(old/'browser-final02.py').read_text(encoding='utf-8')
text=text.replace('online-ogd-migration','online-ftl-migration').replace('final02','final01').replace('/online-ogd/','/online-ftl-failure/')
with (run/'browser-final01.py').open('w',encoding='utf-8',newline='\n') as f:f.write(text)
print('Prepared10 actual native-header/registry checks and actual task-owned reader screenshot tool; no site gate yet.')
