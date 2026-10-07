from common_integrated_v1 import *
fixed_integrated()
resolved=[]
for packet,receipt in [('source-contract-inputs-v2.json','source-contract-receipt-v1.json'),('body-review-inputs-v1.json','public-body-receipt-v1.json')]:
 r=load(RUN/receipt);reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
 assert sha(r['report'])==r['report_sha256']
 for row in load(RUN/packet)['rows']:
  p=Path(row['path']);actual=p
  if sha(p)!=row['sha256']:
   local=p.resolve().relative_to(ROOT).as_posix();assert local in ALLOWED_INTEGRATION,local
   actual=RUN/'snapshots'/(local.replace('/','--')+'.raw')
   resolved.append(dict(packet=packet,reviewed_path=row['path'],snapshot=actual.as_posix(),sha256=row['sha256'],reason='Exact approved integration baseline; live root/reader changes separately scoped by fixed_integrated'))
  assert sha(actual)==row['sha256']==reviewed[row['path']],(packet,row['path'])
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 old=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes();new=Path(p).read_bytes();assert new.startswith(old)
 for line in new[len(old):].decode('utf8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK
old=(RUN/'snapshots/MANIFEST.md.raw').read_bytes();new=Path('MANIFEST.md').read_bytes();assert new.startswith(old)
assert all(TASK in line for line in new[len(old):].decode('utf8').splitlines() if line.strip())
owned=load(RUN/'owned-commit-paths-v1.json')
paths=set(subprocess.check_output(['git','diff','--name-only',BASE],text=True).splitlines())|set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines())
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
write(RUN/('source-scope-'+sys.argv[1]+'.json'),dict(status='passed',owned_paths=sorted(paths),base=BASE,approved_baseline_resolutions=resolved,all_original_contract_and_BODY_inputs_preserved=True,public_canary_BODY_raw_unchanged=True,exact_one_public_and_one_Tests_import=True,eight_old_source_cards_all_old_notes_math_four_curatedIDs_originalglob_preserved=True,old_sources_scanner_pins_inventory_otherBooks_globalSGB_unchanged=True,journals_appendonly_ownTASK=True,chapter_complete=False,goal_complete=False))
print('Scope passed:',len(paths),'owned paths; original inputs resolved exactly:',len(resolved))
