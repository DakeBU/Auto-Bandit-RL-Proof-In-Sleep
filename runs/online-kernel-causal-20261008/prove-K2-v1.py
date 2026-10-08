from common_proving_v1 import *

s = proving_fixed()
assert load(RUN/'leaf-K1-attempt-v1.json')['mathematical_body_compiled']
t = s['targets'][1]
before = PUBLIC.read_bytes()
text = before.decode('utf8')
assert 'theorem kernel_sampler_causal_process' not in text
write(RUN/'proving-K2-v1.json',dict(leaf='K2',terminal=t['name'],frozen_statement_hash=t['statement_hash'],
      dependency_ready=True,actual_K1_compiled=True,
      route='Finite-vector measurability by induction/Fin.lastCases; exact prefix coherence by snoc induction; nonanticipation by equality of finite inputs',
      allowed_file=PUBLIC.relative_to(ROOT).as_posix(),frozen_actual_algorithm_unchanged=True,
      unit_outputs_typed=True,no_probability_or_future_observation_assumption_added=True))
native('lifecycle-proving-K2-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
       json.dumps(dict(run_id=RUN.name,selected_leaf='K2',statement_hash=t['statement_hash'],
       actual_dependency_ready=True,single_lower_route=True,no_terminal_type_edits=True)))
helper = '''
private theorem kernelGeneratedActions_measurable
    (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t))) :
    ∀ t, Measurable (fun q : (Fin t → I) × (Fin t → ℝ) =>
      kernelGeneratedActions f t q.1 q.2) := by
  intro t
  induction t with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      have hr : Measurable (fun q : (Fin (t + 1) → I) × (Fin (t + 1) → ℝ) =>
          ((fun i : Fin t => q.1 i.castSucc), fun i : Fin t => q.2 i.castSucc)) := by
        fun_prop
      have hp : Measurable (fun q : (Fin (t + 1) → I) × (Fin (t + 1) → ℝ) =>
          kernelGeneratedActions f t (fun i => q.1 i.castSucc) (fun i => q.2 i.castSucc)) :=
        ih.comp hr
      have hy : Measurable (fun q : (Fin (t + 1) → I) × (Fin (t + 1) → ℝ) =>
          fun i : Fin t => q.2 i.castSucc) := by
        fun_prop
      have hl : Measurable (fun q : (Fin (t + 1) → I) × (Fin (t + 1) → ℝ) =>
          f t (kernelGeneratedActions f t (fun i => q.1 i.castSucc)
            (fun i => q.2 i.castSucc), fun i => q.2 i.castSucc) (q.1 (Fin.last t))) :=
        (hf t).comp ((hp.prodMk hy).prodMk ((measurable_pi_apply (Fin.last t)).comp measurable_fst))
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [kernelGeneratedActions, Fin.snoc_last] using hl
      · simpa only [kernelGeneratedActions, Fin.snoc_castSucc] using
          (measurable_pi_apply j).comp hp
'''
body = ''' := by
  have hm (t : ℕ) : Measurable (kernelCausalPolicy f t) := by
    have hp : Measurable (fun q : (ℕ → I) × (Fin t → ℝ) =>
        kernelGeneratedActions f t (fun i => q.1 i) q.2) :=
      (kernelGeneratedActions_measurable f hf t).comp (by fun_prop)
    exact (hf t).comp ((hp.prodMk measurable_snd).prodMk
      ((measurable_pi_apply t).comp measurable_fst))
  have hc : ∀ t (u : ℕ → I) (y : ℕ → ℝ) (i : Fin t),
      kernelGeneratedActions f t (fun j => u j) (fun j => y j) i =
        kernelGeneratedPrediction f (i : ℕ) (u, y) := by
    intro t
    induction t with
    | zero =>
        intro u y i
        exact Fin.elim0 i
    | succ t ih =>
        intro u y i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [kernelGeneratedActions, Fin.snoc_last]
          rfl
        · simpa only [kernelGeneratedActions, Fin.snoc_castSucc] using ih u y j
  refine ⟨hm, hc, ?_⟩
  intro t ω ω' hu hy
  have hup : (fun i : Fin t => ω.1 i) = (fun i : Fin t => ω'.1 i) :=
    funext fun i => hu i (Nat.le_of_lt i.isLt)
  have hyp : (fun i : Fin t => ω.2 i) = (fun i : Fin t => ω'.2 i) :=
    funext fun i => hy i i.isLt
  simp only [kernelGeneratedPrediction, kernelCausalPolicy]
  rw [hup, hyp, hu t le_rfl]
'''
footer = '\nend BanditRL.OnlineLearning\n'
assert text.endswith(footer)
PUBLIC.write_bytes((text[:-len(footer)] + helper + '\n' + t['header'] + body + footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(before[:-len(footer.encode())])
proving_fixed()
write(RUN/'leaf-K2-attempt-v1.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K2-focused-v1','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K2-focused-v1.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K2-attempt-v1.json',dict(id='K2',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K2-attempt-v1.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      previous_K1_body_bytes_preserved=True,mathematical_body_compiled=compiled,
      artifact_sha256=sha(artifact) if compiled else None,body_source_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K2-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'Actual finite action recursion measurable; earlier generated actions match same infinite process; pointwise tape<=t/observations<t nonanticipation. Frozen definitions and K1 body retained; joint/conditional law/performance and package gates pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K2 focused exit',result,'actual compiled',compiled,'K3-K5 still pending.',flush=True)
