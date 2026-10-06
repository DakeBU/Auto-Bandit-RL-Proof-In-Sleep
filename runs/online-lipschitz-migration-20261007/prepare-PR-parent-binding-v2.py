"""Separate bootstrap parent read from a fresh creation-time API record before firstuse."""
from common_v2 import *
assert (RUN/'base-PR175-fresh-v1.json').exists() and not (RUN/'create-pr-v1-01-exit.json').exists()
for old,new in [('create-pr-v1.py','create-pr-v2.py'),('prepare-delivery-v1.py','prepare-delivery-v2.py')]:
 p=RUN/old;t=p.read_text(encoding='utf-8');assert 'base-PR175-fresh-v1' in t
 t=t.replace('base-PR175-fresh-v1','base-PR175-creation-fresh-v1');write(RUN/new,t);compile(t,str(RUN/new),'exec')
generated('PR-parent-adapters-before-use-v2.json',[RUN/'create-pr-v2.py',RUN/'prepare-delivery-v2.py'])
write(RUN/'PR-parent-pre-use-correction-v2.json',dict(original_unused=['create-pr-v1.py','prepare-delivery-v1.py'],bootstrap_parent='base-PR175-fresh-v1.json',creation_parent='base-PR175-creation-fresh-v1.json',reason='Bootstrap already stored exactparent under oldname. API helper creates immutable fresh record; separate creation-time label avoids overwriting/bootstrap name collision. Delivery binds actual freshcreation record.',executed_failure=False,source_or_math_changed=False))
print('Fresh creation-time parent record separated from immutable bootstrapread, before first API use.')
