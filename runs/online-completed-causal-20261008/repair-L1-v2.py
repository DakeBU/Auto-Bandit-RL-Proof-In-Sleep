from common_proving_v1 import *

s=proving_fixed()
assert load(RUN/'leaf-L1-attempt-v1.json')['actual_exit']==1
assert sha(PUBLIC)==sha(RUN/'leaf-L1-attempt-v1.lean.raw')
text=PUBLIC.read_text(encoding='utf8')
old='''  have hrepresentative : Measurable[F] representative := by
    apply measurable_pi_iff.2
    intro n
    apply measurable_to_bool
    simpa [representative] using hA n
'''
new='''  have hrepresentative : Measurable[F] representative := by
    letI : MeasurableSpace Ω := F
    apply measurable_pi_iff.2
    intro n
    apply measurable_to_bool
    simpa only [representative, Set.preimage, Set.mem_singleton_iff,
      Bool.decide_iff, Set.setOf_mem_eq] using hA n
'''
assert text.count(old)==1
PUBLIC.write_bytes(text.replace(old,new).encode('utf8'))
proving_fixed()
write(RUN/'leaf-L1-repair-v2.json',dict(actual_failure='leaf-L1-focused-v1-exit.json',
    reasons=['Local measurable-pi synthesis selected ambient field instead of required F',
        'Boolean preimage was not normalized by the initial simp call'],
    exact_proof_local_repair='Install F only inside representative measurability proof; explicit Bool/preimage simplification',
    frozen_header_unchanged=True,assumptions_or_conclusion_changed=False,goal_complete=False))
native('lifecycle-repair-L1-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
    json.dumps(dict(run_id=RUN.name,leaf='L1',attempt=2,statement_hash=s['targets'][0]['statement_hash'],
        proof_local_only=True,repair=(RUN/'leaf-L1-repair-v2.json').as_posix(),obligations_pending=4)))
write(RUN/'leaf-L1-attempt-v2.lean.raw',PUBLIC.read_bytes())
result=gate('leaf-L1-focused-v2','lake','build','BanditRLProof.OnlineGuessingCompletedCausal',required=False)
log=(RUN/'leaf-L1-focused-v2.log').read_text(encoding='utf8')
artifact=ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingCompletedCausal.olean'
compiled=(result==0 and 'Built BanditRLProof.OnlineGuessingCompletedCausal' in log and
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size>0)
if result==0:assert compiled
write(RUN/'leaf-L1-attempt-v2.json',dict(id='L1',actual_exit=result,current_source_sha256=sha(PUBLIC),
    snapshot_sha256=sha(RUN/'leaf-L1-attempt-v2.lean.raw'),frozen_statement_hash=s['targets'][0]['statement_hash'],
    header_unchanged=True,mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
    semantic_BODY_review_pending=True,package_accepted=False))
native('leaf-L1-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if compiled else 'failed','--notes','Same exact real-version terminal; proof-local F instance and Bool preimage simplification only. Failed v1 preserved; acceptance/full gates pending.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',s['targets'][0]['statement_hash'],
    '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','4','--obligations-after','4')
proving_fixed()
print('L1 v2 actual focused exit',result,'actual compiled witness',compiled,'four accepted obligations pending.',flush=True)
