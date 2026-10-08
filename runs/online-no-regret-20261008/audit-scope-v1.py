from common_integrated_v1 import *
fixed_integrated()
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 old=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes();new=Path(p).read_bytes();assert new.startswith(old)
 for line in new[len(old):].decode('utf8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK,(p,line)
old=(RUN/'snapshots/MANIFEST.md.raw').read_bytes();new=Path('MANIFEST.md').read_bytes();assert new.startswith(old)
assert all(TASK in line for line in new[len(old):].decode('utf8').splitlines() if line.strip())
owned=load(RUN/'owned-commit-paths-v1.json')
paths=set(subprocess.check_output(['git','diff','--name-only',BASE],text=True).splitlines())|set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines())
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
write(RUN/('source-scope-'+sys.argv[1]+'.json'),dict(status='passed',owned_paths=sorted(paths),base=BASE,original_contract_BODY_inputs_preserved=True,public_canary_BODY_raw_unchanged=True,exact_one_public_and_one_Tests_import=True,nine_old_source_cards_all_old_notes_math_four_curatedIDs_originalglobs_preserved=True,old_sources_scanner_pins_inventory_otherBooks_globalSGB_unchanged=True,journals_appendonly_ownTASK=True,chapter_complete=False,goal_complete=False))
print('Scope passed:',len(paths),'owned paths; frozen mathematical sources preserved.')
