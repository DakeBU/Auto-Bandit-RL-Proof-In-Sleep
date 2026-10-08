from common_proving_v1 import *
s=proving_fixed()
assert load(RUN/'leaf-L2-attempt-v1.json')['actual_exit']==1
old=PUBLIC.read_bytes()
assert old==(RUN/'leaf-L2-attempt-v1.lean.raw').read_bytes()
needle=(s['targets'][1]['header']+' := by\n  have hi').encode('utf8')
replacement=(s['targets'][1]['header']+' := by\n  rename_i mΩ mSeed hμ\n  letI : MeasurableSpace Ω := mΩ\n  have hi').encode('utf8')
assert old.count(needle)==1
write(RUN/'leaf-L2-repair-v2.json',dict(reason='Local explicit F is of class type; elaboration selected F where ambient measurable instance was required by mu. Fix ambient instance inside proof, same pattern as existing causal independence parent.',
    failed_source_sha256=sha(PUBLIC),actual_failed_log_sha256=sha(RUN/'leaf-L2-focused-v1.log'),
    exact_error='synthesized type class instance is not definitionally equal to expression inferred by typing rules: synthesized F, inferred ambient instance',
    statement_hash=s['targets'][1]['statement_hash'],target_unchanged=True,route_unchanged=True,
    changed_only='Two proof-local rename_i / letI lines; no type, assumptions, parent or source edits'))
native('lifecycle-repair-L2-v2','lifecycle-event','--session',TASK,'--event','repair',
    '--payload-json',json.dumps(dict(run_id=RUN.name,leaf='L2',defect='ambient-instance inference',
        source_contract_version=1,terminal_type_unchanged=True,failed_exit=1)))
PUBLIC.write_bytes(old.replace(needle,replacement))
proving_fixed()
write(RUN/'leaf-L2-attempt-v2.lean.raw',PUBLIC.read_bytes())
result=gate('leaf-L2-focused-v2','lake','build','BanditRLProof.OnlineGuessingAECausal',required=False)
write(RUN/'leaf-L2-attempt-v2.json',dict(id='L2',actual_exit=result,current_source_sha256=sha(PUBLIC),
    snapshot_sha256=sha(RUN/'leaf-L2-attempt-v2.lean.raw'),header_unchanged=True,
    mathematical_body_compiled=result==0,semantic_BODY_review_pending=True,package_accepted=False))
native('leaf-L2-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if result==0 else 'failed','--notes','L2 same exact type; proof-local ambient measurable instance repair; failed v1 retained.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',s['targets'][1]['statement_hash'],
    '--progress-class','compiled-leaf' if result==0 else 'diagnostic','--obligations-before','3','--obligations-after','3')
proving_fixed()
print('Repaired L2 actual focused exit',result)
