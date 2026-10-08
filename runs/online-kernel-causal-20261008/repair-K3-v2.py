from common_proving_v1 import *

s = proving_fixed()
assert not load(RUN/'leaf-K3-attempt-v1.json')['mathematical_body_compiled']
t = s['targets'][2]
before = PUBLIC.read_bytes()
old = '''      ((measurable_pi_apply t).comp measurable_fst).aemeasurable).2
    rw [kernelGameLaw_map_tape'''
new = '''      ((measurable_pi_apply t).comp measurable_fst).aemeasurable).2
    simp only [Function.comp_def]
    rw [kernelGameLaw_map_tape'''
source = before.decode('utf8')
assert source.count(old) == 1
write(RUN/'leaf-K3-repair-v2.json',dict(failed_actual_exit=1,
      failed_snapshot_sha256=sha(RUN/'leaf-K3-attempt-v1.lean.raw'),
      failed_log_sha256=sha(RUN/'leaf-K3-focused-v1.log'),
      error='Joint map rewriting encountered explicit Function.comp forms introduced by the independence equivalence',
      classification='Lean expression normalization; no missing mathematical hypothesis',
      repair='Normalize Function.comp_def before rewriting the three tape pushforwards',
      statement_hash=t['statement_hash'],no_context_or_terminal_or_K1_K2_change=True,
      same_independence_route=True,previous_failure_retained=True))
native('lifecycle-repair-K3-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='K3',attempt=2,statement_hash=t['statement_hash'],
       failure='Function.comp map expression normalization, frozen statement intact',same_route=True)))
PUBLIC.write_bytes(source.replace(old,new).encode('utf8'))
proving_fixed()
write(RUN/'leaf-K3-attempt-v2.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K3-focused-v2','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K3-focused-v2.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K3-attempt-v2.json',dict(id='K3',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K3-attempt-v2.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      body_source_review_pending=True,package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K3-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'K3 derives fresh-draw independence and actual-history/current-prediction joint kernel law from infinite product law. Normalize composition expressions; v1 failure retained. Conditional law and final performance terminal still pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K3 repaired focused exit',result,'actual compiled',compiled,flush=True)
