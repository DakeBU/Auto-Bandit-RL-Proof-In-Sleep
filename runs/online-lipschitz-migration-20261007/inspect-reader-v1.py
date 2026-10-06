"""Read actual selected reader schema before preparing metadata edits."""
from common_v2 import *
out={}
for p,key,field in [('website/content/readings.json','readings','slug'),('website/content/highlights.json','highlights','chapter'),('website/content/chapters.json','chapters','slug')]:
 d=load(p);out[p]=[x for x in d[key] if x.get(field)==ROUTE]
write(RUN/'reader-original-selected-v1.json',out)
for p,rows in out.items():
 print(p,len(rows))
 if p.endswith('readings.json'):
  for x in rows:
   print('keys',list(x));print('teaching_route',x.get('teaching_route'));print('notation',x.get('notation'));print('source_theorems',x.get('source_theorems'));print('proof_bridge',x.get('proof_bridge'));print('worked_example',x.get('worked_example'))
 elif p.endswith('highlights.json'):
  for x in rows:print(x)
