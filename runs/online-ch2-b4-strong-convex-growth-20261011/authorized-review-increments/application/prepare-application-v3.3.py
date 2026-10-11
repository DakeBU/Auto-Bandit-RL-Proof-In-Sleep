import json,hashlib,ntpath,subprocess
from pathlib import Path
out=Path('tmp/online-ch2-b4-next-strong-convex-freeze-20261011/application')
root=Path.cwd()
def bind(path):
 p=Path(path); b=p.read_bytes();return dict(path=p.as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(name,obj):
 with (out/name).open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
p=json.loads((out/'canonical-freeze-application-proposal-v3.2.json').read_text(encoding='utf-8-sig'))
review=Path('tmp/online-ch2-b4-next-strong-convex-freeze-audit-20261011/freeze-application-review-v3.2.json')
rv=json.loads(review.read_text(encoding='utf-8-sig'))
assert [x['id'] for x in rv['blockers']]==['DUPLICATE_INCREMENT_DESTINATIONS']
seen={}; kept=[]; dropped=[]
for row in p['required_v3_increments']:
 key=ntpath.normcase(ntpath.abspath(row['destination']))
 if key in seen:
  assert row==seen[key], 'Non-identical duplicate must be separately resolved'
  dropped.append(row)
 else:seen[key]=row;kept.append(row)
assert len(dropped)==2
for file in sorted(out.glob('*-v3.2.*')):
 b=bind(file); row={**b,'destination':p['canonical_run']+'/v3-review-increments/'+b['path']};key=ntpath.normcase(ntpath.abspath(row['destination']))
 if key not in seen:kept.append(row);seen[key]=row
for file in [review,review.with_suffix('.md')]:
 b=bind(file);row={**b,'destination':p['canonical_run']+'/v3-review-increments/'+b['path']};key=ntpath.normcase(ntpath.abspath(row['destination']))
 assert key not in seen;kept.append(row);seen[key]=row
p['required_v3_increments']=kept
p['successor_of']=bind(out/'canonical-freeze-application-proposal-v3.2.json')
p['status']='V3_3_EXACT_DUPLICATE_REPAIR_PREPROOF_ONLY_UNEXECUTED'
p['repair_review']=bind(review)
p['duplicate_repair']={'removed_repeated_rows':dropped,'policy':'Retain one identical source/destination/SHA/size binding; no unique historical evidence dropped; runtime duplicate protection unchanged.'}
e=(out/'emit-canonical-freeze-v3.2.ps1').read_text(encoding='utf-8-sig').replace('-v3.2.','-v3.3.')
with (out/'emit-canonical-freeze-v3.3.ps1').open('x',encoding='utf-8',newline='\n') as f:f.write(e)
p['emitter']=bind(out/'emit-canonical-freeze-v3.3.ps1');p['authorization_protocol']['emitter_sha256']=p['emitter']['sha256']
save('canonical-freeze-application-proposal-v3.3.json',p)
# Simulate emitter's complete default destination set, including its receipt reservation.
rows=[dict(category='static',destination=r['destination']) for r in p['archival_rows']]
rows += [dict(category='required_increment',destination=r['destination']) for r in kept]
rows += [dict(category='gate',destination=p['canonical_run']+'/preproof-readiness/gates/'+g['role']+'/receipt.json') for g in p['expected_baseline_gates']]
rows += [dict(category='dynamic_or_reserved',destination=d) for d in [p['canonical_run']+'/preproof-readiness/readiness.json',p['canonical_run']+'/freeze-review/independent-application-review-v3.3.json',p['canonical_doc']+'/canonical-freeze-application-proposal-v3.3.json',p['canonical_run']+'/plans/emit-canonical-freeze-v3.3.ps1',p['canonical_doc']+'/parent-freeze-authorization-v3.3.json',p['canonical_doc']+'/freeze-application-receipt-v3.3.json']]
# Also test optional continuity destination, although same4034 execution needs none.
rows.append(dict(category='optional_continuity_reserved',destination=p['canonical_run']+'/preproof-readiness/source-continuity-review.json'))
seen={}
for r in rows:
 k=ntpath.normcase(ntpath.abspath(r['destination']))
 assert k not in seen,(r,seen.get(k));seen[k]=r
 assert any(k.startswith(ntpath.normcase(ntpath.abspath(base))+'\\') for base in [p['canonical_doc'],p['canonical_run']])
for r in p['archival_rows']:
 b=bind(r['source']);assert b['sha256']==r['sha256'] and b['bytes']==r['bytes']
for r in kept:
 b=bind(r['path']);assert b['sha256']==r['sha256'] and b['bytes']==r['bytes']
prior=json.loads((out/'canonical-freeze-application-proposal-v3.2.json').read_text(encoding='utf-8-sig'));assert p['archival_rows']==prior['archival_rows']
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();status=subprocess.check_output(['git','status','--porcelain=v1'],text=True).strip();assert not status
save('full-destination-simulation-v3.3.json',dict(status='PASS_ALL_DEFINED_DESTINATIONS_UNIQUE',normalization='ntpath.abspath + ntpath.normcase; Windows case insensitive',count=len(rows),rows=rows,static135=True,required_increment_count=len(kept),gate_count=9,includes_readiness_application_review_proposal_emitter_parentauth_receipt=True,includes_optional_continuity=True,optional_additional_archive_bindings='Not supplied; future parent explicit rows still checked against all rows by unchanged emitter HashSet before copy',emitter_executed=False))
save('application-repair-response-v3.3.json',dict(status='REPAIRED_AWAITING_DISTINCT_REVIEW',review=bind(review),proposal=bind(out/'canonical-freeze-application-proposal-v3.3.json'),emitter=p['emitter'],removed_identical_repeat_count=len(dropped),unique_history_preserved=True,static135_unchanged=True,full_destination_simulation=bind(out/'full-destination-simulation-v3.3.json'),head=head,git_status=status,maintenance_accepted=False,reader_pending=True,BODY=False,emitter_executed=False))
print(json.dumps([bind(out/'canonical-freeze-application-proposal-v3.3.json'),p['emitter'],bind(out/'application-repair-response-v3.3.json'),bind(out/'full-destination-simulation-v3.3.json')],indent=2))
