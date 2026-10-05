"""Generate package-specific registry and browser checks from audited shared tools."""
from pathlib import Path
import json
run=Path(__file__).parent
old=Path('runs/online-unit-scaling-20261004')
text=(old/'verify-registry-final02.py').read_text(encoding='utf-8')
for a,b in [('online-unit-scaling-site-final02','online-ogd-migration-site-final01'),
    ('OnlineUnitScaling','OnlineGradientDescentSource'),("len(names)==26","len(names)==14"),
    ('teaching:online-unit-scaling','teaching:online-ogd'),
    ('online-optimal-step-site-final02','online-unit-scaling-site-final02'),
    ('registry-final02.json','registry-final01.json')]:text=text.replace(a,b)
with (run/'verify-registry-final01.py').open('w',encoding='utf-8',newline='\n') as f:f.write(text)
print('Generated actual native14-header registry check; prior10790 IDs/URLs preserved.')
