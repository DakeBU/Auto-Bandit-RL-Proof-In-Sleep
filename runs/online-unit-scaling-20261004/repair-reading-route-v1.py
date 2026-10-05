"""Repair only the bounded teaching navigation; retain all public declarations."""
from pathlib import Path
import json
run=Path(__file__).parent
p=Path('website/content/readings.json')
(run/'leaves/readings-site-v1.json').write_bytes(p.read_bytes())
x=json.loads(p.read_text(encoding='utf-8'))
reading=next(r for r in x['readings'] if r['slug']=='online-unit-scaling')
assert len(reading['teaching_route'])==6
reading['teaching_route']=['BanditRL.OnlineUnitScaling.'+n for n in
    ['unit_exponents','history_scaling','wrong_step_output','regret_fixed_scaled']]
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
print('Four navigation entries; all22 public notes/26 registry nodes/two source cards/Lean targets retained.')
