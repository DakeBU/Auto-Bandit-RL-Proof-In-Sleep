from common_v1 import *
def reviewed_fixed():
 fixed()
 f=load(RUN/'stabilized-contract-v1.json')
 assert sha(CONTRACT/'targets-v1.json')==f['targets_sha256'] and sha(CONTRACT/'public-context-v1.lean')==f['context_sha256']
 resolutions={x['original']:x for x in load(RUN/'contract-review-baseline-resolutions-v1.json')}
 for name in ['source-contract-receipt-v1.json','source-repair-receipt-v1.json']:
  r=load(RUN/name);assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
  assert sha(r['report'])==r['report_sha256']
  reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
  for row in load(RUN/'source-contract-inputs-v1.json')['rows']:
   p=row['path'];h=row['sha256'];assert reviewed[p]==h,p
   if sha(p)!=h:
    original=resolutions[p];assert h==original['original_sha256']==original['snapshot_sha256']==sha(original['snapshot']),p
 assert r['required_reader_corrections']==f['original_reader_requirements']
