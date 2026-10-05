from pathlib import Path
import hashlib
files=[
 ('.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean',470,491),
 ('.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean',920,953),
 ('.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean',325,370),
 ('.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean',680,740)
]
for name,start,end in files:
 p=Path(name);print(name,'SHA256',hashlib.sha256(p.read_bytes()).hexdigest())
 for i,line in enumerate(p.read_text(encoding='utf-8').splitlines(),1):
  if start<i<=end:print(str(i)+': '+line)
