from common_proving_v1 import *

s = proving_fixed()
assert not load(RUN/'leaf-K2-attempt-v1.json')['mathematical_body_compiled']
t = s['targets'][1]
before = PUBLIC.read_bytes()
old = '''    have hp : Measurable (fun q : (ℕ → I) × (Fin t → ℝ) =>
        kernelGeneratedActions f t (fun i => q.1 i) q.2) :=
      (kernelGeneratedActions_measurable f hf t).comp (by fun_prop)
'''
new = '''    have hr : Measurable (fun q : (ℕ → I) × (Fin t → ℝ) =>
        ((fun i : Fin t => q.1 i), q.2)) := by
      fun_prop
    have hp : Measurable (fun q : (ℕ → I) × (Fin t → ℝ) =>
        kernelGeneratedActions f t (fun i => q.1 i) q.2) :=
      (kernelGeneratedActions_measurable f hf t).comp hr
'''
text = before.decode('utf8')
assert text.count(old) == 1
write(RUN/'leaf-K2-repair-v2.json',dict(failed_actual_exit=1,
      failed_snapshot_sha256=sha(RUN/'leaf-K2-attempt-v1.lean.raw'),
      failed_log_sha256=sha(RUN/'leaf-K2-focused-v1.log'),
      error='fun_prop could not infer the composition input map at the policy measurability step',
      classification='Lean API elaboration; no mathematical target or missing hypothesis',
      repair='Name and fully type the finite-prefix input restriction map before composition',
      statement_hash=t['statement_hash'],no_context_or_terminal_or_K1_body_change=True,
      same_recursion_route=True,previous_failure_retained=True))
native('lifecycle-repair-K2-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='K2',attempt=2,statement_hash=t['statement_hash'],
       failure='Composition input map metavariable, source statement intact',same_route=True)))
PUBLIC.write_bytes(text.replace(old,new).encode('utf8'))
proving_fixed()
write(RUN/'leaf-K2-attempt-v2.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K2-focused-v2','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K2-focused-v2.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K2-attempt-v2.json',dict(id='K2',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K2-attempt-v2.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      body_source_review_pending=True,package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K2-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'K2 same frozen terminal/algorithm, explicit finite-prefix restriction map fixes composition elaboration. Measurability/prefix coherence/nonanticipation proof; retained v1 failure. Joint-law terminal and package gates pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K2 repaired focused exit',result,'actual compiled',compiled,'K3-K5 pending.',flush=True)
