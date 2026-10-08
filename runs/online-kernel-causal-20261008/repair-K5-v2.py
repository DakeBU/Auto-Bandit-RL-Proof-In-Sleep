from common_proving_v1 import *

s = proving_fixed()
assert not load(RUN/'leaf-K5-attempt-v1.json')['mathematical_body_compiled']
t = s['targets'][4]
before = PUBLIC.read_bytes()
old = '''    simpa only [Measure.map_id] using
      (iIndepFun_iff_map_fun_eq_infinitePi_map (fun n => measurable_pi_apply n)).1 hind
'''
new = '''    have hi :=
      (iIndepFun_iff_map_fun_eq_infinitePi_map (fun n => measurable_pi_apply n)).1 hind
    change (ν : Measure (ℕ → ℝ)).map id = _ at hi
    simpa only [Measure.map_id] using hi
'''
source = before.decode('utf8')
assert source.count(old) == 1
write(RUN/'leaf-K5-repair-v2.json',dict(failed_actual_exit=1,
      failed_snapshot_sha256=sha(RUN/'leaf-K5-attempt-v1.lean.raw'),
      failed_log_sha256=sha(RUN/'leaf-K5-focused-v1.log'),
      error='simp map_id did not match an eta-expanded identity on the infinite observation stream',
      classification='Lean definitional expression normalization; frozen IID assumptions sufficient',
      repair='Explicitly change the joint stream projection to id before map_id simplification',
      statement_hash=t['statement_hash'],no_context_or_terminal_or_K1_K2_K3_K4_change=True,
      same_route=True,previous_failure_retained=True))
native('lifecycle-repair-K5-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='K5',attempt=2,statement_hash=t['statement_hash'],
       failure='Eta-expanded stream identity not matched by map_id; explicit definitional change',same_route=True)))
PUBLIC.write_bytes(source.replace(old,new).encode('utf8'))
proving_fixed()
write(RUN/'leaf-K5-attempt-v2.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K5-focused-v2','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K5-focused-v2.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K5-attempt-v2.json',dict(id='K5',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K5-attempt-v2.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      previous_K1_K2_K3_K4_bytes_preserved=True,body_source_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K5-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'K5 realizes one law/horizon-independent family, actual joint/conditional laws and same-process IID expected-fixed excess at all natural horizons. Eta-expanded stream identity normalized; v1 failure retained. Public nondegenerate canary, body semantics and combined gates pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K5 repaired focused exit',result,'actual compiled',compiled,flush=True)
