from common_proving_v1 import *

s = proving_fixed()
assert load(RUN/'leaf-K4-attempt-v1.json')['mathematical_body_compiled']
t = s['targets'][4]
before = PUBLIC.read_bytes()
source = before.decode('utf8')
assert '\ntheorem '+t['name'].split('.')[-1] not in source
helper = '''
private theorem kernelGameLaw_map_observation {β : Type*} [MeasurableSpace β]
    (ν : ProbabilityMeasure (ℕ → ℝ)) (g : (ℕ → ℝ) → β) (hg : Measurable g) :
    (kernelGameLaw ν).map (fun ω => g ω.2) = (ν : Measure (ℕ → ℝ)).map g := by
  change (kernelGameLaw ν).map (g ∘ Prod.snd) = _
  rw [← Measure.map_map hg measurable_snd]
  simp
'''
body = ''' := by
  obtain ⟨f, hf, hκ⟩ := kernel_sampler_family_exists κ
  obtain ⟨hpolicy, hprefix, hcausal⟩ := kernel_sampler_causal_process f hf
  refine ⟨f, hf, hκ, hpolicy, hprefix, hcausal, ?_⟩
  intro ν
  refine ⟨kernel_sampler_joint_law κ f hf hκ ν,
    kernel_sampler_conditional_law κ f hf hκ ν, ?_⟩
  intro hind hlaw hb T
  have hY (t : ℕ) : Measurable (fun ω : (ℕ → I) × (ℕ → ℝ) => ω.2 t) :=
    (measurable_pi_apply t).comp measurable_snd
  have hc (n : ℕ) : (kernelGameLaw ν).map (fun ω => ω.2 n) =
      (ν : Measure (ℕ → ℝ)).map (fun y => y n) :=
    kernelGameLaw_map_observation ν (fun y => y n) (measurable_pi_apply n)
  have hInd : iIndepFun (fun t (ω : (ℕ → I) × (ℕ → ℝ)) => ω.2 t)
      (kernelGameLaw ν) := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map hY).2
    change (kernelGameLaw ν).map Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    simp_rw [hc]
    simpa only [Measure.map_id] using
      (iIndepFun_iff_map_fun_eq_infinitePi_map (fun n => measurable_pi_apply n)).1 hind
  have hLaw (t : ℕ) : IdentDistrib (fun ω : (ℕ → I) × (ℕ → ℝ) => ω.2 t)
      (fun ω => ω.2 0) (kernelGameLaw ν) (kernelGameLaw ν) := by
    refine ⟨(hY t).aemeasurable, (hY 0).aemeasurable, ?_⟩
    rw [hc t, hc 0]
    exact (hlaw t).map_eq
  have hBound (t : ℕ) : ∀ᵐ ω ∂(kernelGameLaw ν), ω.2 t ∈ Set.Icc (0 : ℝ) 1 := by
    exact measurePreserving_snd.quasiMeasurePreserving.ae (hb t)
  let policy : (t : ℕ) → ((ℕ → I) × ((↑(Finset.range t) : Type) → ℝ)) → ℝ :=
    fun t q => (kernelCausalPolicy f t
      (q.1, fun i : Fin t => q.2 ⟨i, Finset.mem_range.mpr i.isLt⟩) : ℝ)
  have hp (t : ℕ) : Measurable (policy t) := by
    have hr : Measurable (fun q : (ℕ → I) × ((↑(Finset.range t) : Type) → ℝ) =>
        (q.1, fun i : Fin t => q.2 ⟨i, Finset.mem_range.mpr i.isLt⟩)) := by
      fun_prop
    exact measurable_subtype_coe.comp ((hpolicy t).comp hr)
  have hpb (t : ℕ) (u : ℕ → I) (z : (↑(Finset.range t) : Type) → ℝ)
      (_ : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) : policy t (u, z) ∈ Set.Icc (0 : ℝ) 1 :=
    (kernelCausalPolicy f t
      (u, fun i : Fin t => z ⟨i, Finset.mem_range.mpr i.isLt⟩)).property
  have hseed : IndepFun (Prod.fst : ((ℕ → I) × (ℕ → ℝ)) → (ℕ → I))
      (Prod.snd : ((ℕ → I) × (ℕ → ℝ)) → (ℕ → ℝ)) (kernelGameLaw ν) :=
    indepFun_prod measurable_id measurable_id
  exact randomized_history_policy_expectedFixed_excess (kernelGameLaw ν)
    (fun t ω => ω.2 t) hY hLaw hBound hInd Prod.fst measurable_fst hseed
    policy hp hpb T
'''
native('lifecycle-proving-K5-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='K5',attempt=1,statement_hash=t['statement_hash'],
       dependencies=['K1','K2','K3','K4','randomized_history_policy_expectedFixed_excess'],
       terminal='one sampler family before every law and every natural horizon; actual same-process expected-fixed excess')))
footer = '\nend BanditRL.OnlineLearning\n'
assert source.endswith(footer)
PUBLIC.write_bytes((source[:-len(footer)]+helper+'\n'+t['header']+body+footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(before[:-len(footer.encode())])
proving_fixed()
write(RUN/'leaf-K5-attempt-v1.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K5-focused-v1','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K5-focused-v1.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K5-attempt-v1.json',dict(id='K5',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K5-attempt-v1.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      previous_K1_K2_K3_K4_bytes_preserved=True,body_source_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K5-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'One law/horizon-independent sampler family realizes actual causal joint/conditional laws. IID observation assumptions lifted to same product law; concrete history policy instantiates existing expected-fixed excess producer for all natural horizons including zero. No assumed prediction-current independence or performance bound. Nondegenerate canary/body review/full gates remain.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K5 focused exit',result,'actual compiled',compiled,flush=True)
