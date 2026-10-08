from common_proving_v1 import *

s=proving_fixed()
assert load(RUN/'leaf-L4-attempt-v1.json')['mathematical_body_compiled']
assert sha(PUBLIC)==load(RUN/'leaf-L4-attempt-v1.json')['current_source_sha256']
assert len([x for x in CANARY.read_text(encoding='utf8').splitlines() if x.startswith('theorem ')])==11
write(RUN/'canary-attempt-v1.lean.raw',CANARY.read_bytes())
result=gate('canary-focused-v1','lake','build','Tests.OnlineGuessingCompletedCausalCanary',required=False)
log=(RUN/'canary-focused-v1.log').read_text(encoding='utf8')
artifact=ROOT/'.lake/build/lib/lean/Tests/OnlineGuessingCompletedCausalCanary.olean'
compiled=(result==0 and 'Built Tests.OnlineGuessingCompletedCausalCanary' in log and
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size>0)
if result==0:assert compiled
write(RUN/'canary-attempt-v1.json',dict(actual_exit=result,canary_sha256=sha(CANARY),public_sha256=sha(PUBLIC),
    mathematical_test_bodies_compiled=compiled,actual_named_proofs=11,
    artifact_sha256=sha(artifact) if compiled else None,genuine_augmented_not_ordinary_canary=True,
    semantic_BODY_and_root_Test_full_harness_pending=True,chapter_complete=False,goal_complete=False))
native('canary-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build',
    '--status','compiled' if compiled else 'failed','--run-id',RUN.name,
    '--lean',CANARY.relative_to(ROOT).as_posix(),'--verifier-evidence',RUN/'canary-focused-v1-exit.json',
    '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','4','--obligations-after','4',
    '--notes','Eleven actual named canary proof bodies: augmented-measurable but not ordinary predictable, all four public targets instantiated; positive variance, random seed, nonzero original excess1/2, empty horizon. Package acceptance pending.')
proving_fixed()
print('Actual canary exit',result,'compiled witness',compiled,'four accepted package obligations pending.',flush=True)
