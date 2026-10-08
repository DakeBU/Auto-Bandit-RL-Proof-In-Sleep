from common_proving_v1 import *
s=proving_fixed()
assert load(RUN/'leaf-L1-attempt-v1.json')['mathematical_body_compiled']
old=PUBLIC.read_bytes();end=b'\nend BanditRL.OnlineLearning\n'
assert old.endswith(end) and sha(PUBLIC)==load(RUN/'leaf-L1-attempt-v1.json')['current_source_sha256']
native('lifecycle-proving-L2-v1','lifecycle-event','--session',TASK,'--event','proving',
    '--payload-json',json.dumps(dict(run_id=RUN.name,selected_leaf='L2',statement_hash=s['targets'][1]['statement_hash'],
        previous_leaf_actual_focused_exit=0,terminal_type_edits=False,accepted_package=False)))
body=''' := by
  have hi := predictable_private_seed_independent μ Y hY hind S hS hseed t F hF
    (hP.mk P) hP.measurable_mk
  exact hi.congr hP.ae_eq_mk.symm (Filter.EventuallyEq.refl _ _)
'''
new=old[:-len(end)]+b'\n'+(s['targets'][1]['header']+body).encode('utf8')+end
PUBLIC.write_bytes(new)
assert new.startswith(old[:-len(end)])
proving_fixed()
write(RUN/'leaf-L2-attempt-v1.lean.raw',new)
result=gate('leaf-L2-focused-v1','lake','build','BanditRLProof.OnlineGuessingAECausal',required=False)
write(RUN/'leaf-L2-attempt-v1.json',dict(id='L2',actual_exit=result,current_source_sha256=sha(PUBLIC),
    snapshot_sha256=sha(RUN/'leaf-L2-attempt-v1.lean.raw'),previous_L1_proof_bytes_preserved=True,
    frozen_statement_hash=s['targets'][1]['statement_hash'],header_unchanged=True,
    mathematical_body_compiled=result==0,semantic_BODY_review_pending=True,package_accepted=False))
native('leaf-L2-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if result==0 else 'failed','--notes','L2 genuine current independence from AE F-measurable version and whole seed/stream independence; exact focused body only.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',s['targets'][1]['statement_hash'],
    '--progress-class','compiled-leaf' if result==0 else 'diagnostic','--obligations-before','3','--obligations-after','3')
proving_fixed()
print('L2 actual focused exit',result,'; acceptance remains pending')
