from common_proving_v1 import *

s = proving_fixed()
assert load(RUN/'leaf-K2-attempt-v2.json')['mathematical_body_compiled']
t = s['targets'][2]
before = PUBLIC.read_bytes()
text = before.decode('utf8')
assert 'theorem kernel_sampler_joint_law' not in text
write(RUN/'proving-K3-v1.json',dict(leaf='K3',terminal=t['name'],frozen_statement_hash=t['statement_hash'],
      dependency_ready=True,actual_K2_attempt=2,
      route='Disjoint strict-past/current infinite uniform coordinates; lift through fst of product game law; regroup entire environment with past tape; map actual recursively generated history and sampler; product-map equals compProd',
      no_assumed_current_independence_or_desired_kernel_law=True,
      general_product_map_helper='private mathlib-candidate, no new shared node/count claim',
      allowed_file=PUBLIC.relative_to(ROOT).as_posix(),single_lower_route=True))
native('lifecycle-proving-K3-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
       json.dumps(dict(run_id=RUN.name,selected_leaf='K3',statement_hash=t['statement_hash'],
       actual_K2_compiled=True,single_lower_route=True,no_terminal_type_edits=True)))
helpers = '''
private theorem kernelGameLaw_map_tape {β : Type*} [MeasurableSpace β]
    (ν : ProbabilityMeasure (ℕ → ℝ)) (g : (ℕ → I) → β) (hg : Measurable g) :
    (kernelGameLaw ν).map (fun ω => g ω.1) = kernelUniformTapeLaw.map g := by
  change (kernelGameLaw ν).map (g ∘ Prod.fst) = kernelUniformTapeLaw.map g
  rw [← Measure.map_map hg measurable_fst]
  simp

private theorem kernelSampler_product_law {H : Type*} [MeasurableSpace H]
    (m : Measure H) [SFinite m] (κ : Kernel H I) [IsMarkovKernel κ]
    (f : H → I → I) (hf : Measurable (Function.uncurry f))
    (hκ : ∀ h, (volume : Measure I).map (f h) = κ h) :
    (m.prod (volume : Measure I)).map (fun q => (q.1, f q.1 q.2)) = m ⊗ₘ κ := by
  have hm : Measurable (fun q : H × I => (q.1, f q.1 q.2)) :=
    measurable_fst.prodMk hf
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), Measure.compProd_apply hs]
  congr 1
  funext h
  rw [← hκ h, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hs)]
  rfl
'''
body = ''' := by
  let past : (ℕ → I) → (Fin t → I) := fun u i => u i
  have hpast : Measurable past := by
    fun_prop
  have htape : iIndepFun (fun n (u : ℕ → I) => u n) kernelUniformTapeLaw :=
    iIndepFun_infinitePi (P := fun _ : ℕ => (volume : Measure I))
      (X := fun _ => fun z : I => z) (fun _ => measurable_id)
  have hpi : IndepFun past (fun u : ℕ → I => u t) kernelUniformTapeLaw := by
    have hi := iIndepFun.indepFun_finset (Finset.range t) {t} (by simp) htape
      (fun n => measurable_pi_apply n)
    have hr : Measurable (fun z : (↑(Finset.range t) : Type) → I =>
        fun i : Fin t => z ⟨i, Finset.mem_range.mpr i.isLt⟩) := by
      fun_prop
    simpa only [Function.comp_def, past] using hi.comp hr
      (measurable_pi_apply (⟨t, by simp⟩ : (↑({t} : Finset ℕ) : Type)))
  have hpi_game : IndepFun (fun ω : (ℕ → I) × (ℕ → ℝ) => past ω.1)
      (fun ω => ω.1 t) (kernelGameLaw ν) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      (hpast.comp measurable_fst).aemeasurable
      ((measurable_pi_apply t).comp measurable_fst).aemeasurable).2
    rw [kernelGameLaw_map_tape ν (fun u => (past u, u t))
          (hpast.prodMk (measurable_pi_apply t)),
        kernelGameLaw_map_tape ν past hpast,
        kernelGameLaw_map_tape ν (fun u => u t) (measurable_pi_apply t)]
    exact (indepFun_iff_map_prod_eq_prod_map_map hpast.aemeasurable
      (measurable_pi_apply t).aemeasurable).1 hpi
  have hwhole : IndepFun (fun ω : (ℕ → I) × (ℕ → ℝ) => ω.2)
      (fun ω => (past ω.1, ω.1 t)) (kernelGameLaw ν) :=
    (indepFun_prod (μ := kernelUniformTapeLaw) (ν := (ν : Measure (ℕ → ℝ)))
      (hpast.prodMk (measurable_pi_apply t)) measurable_id).symm
  have hblock : IndepFun (fun ω : (ℕ → I) × (ℕ → ℝ) => (ω.2, past ω.1))
      (fun ω => ω.1 t) (kernelGameLaw ν) :=
    independent_private_seed_pair (kernelGameLaw ν) (fun ω => ω.2)
      (fun ω => past ω.1) (fun ω => ω.1 t) measurable_snd
      (hpast.comp measurable_fst) ((measurable_pi_apply t).comp measurable_fst) hwhole hpi_game
  let b : (ℕ → ℝ) × (Fin t → I) → KernelDecisionHistory t := fun q =>
    (kernelGeneratedActions f t q.2 (fun i => q.1 i), fun i => q.1 i)
  have hr : Measurable (fun q : (ℕ → ℝ) × (Fin t → I) =>
      (q.2, fun i : Fin t => q.1 i)) := by
    fun_prop
  have hy : Measurable (fun q : (ℕ → ℝ) × (Fin t → I) =>
      fun i : Fin t => q.1 i) := by
    fun_prop
  have hb : Measurable b := ((kernelGeneratedActions_measurable f hf t).comp hr).prodMk hy
  have hH : Measurable (kernelGeneratedHistory f t) := by
    change Measurable (b ∘ (fun ω : (ℕ → I) × (ℕ → ℝ) => (ω.2, past ω.1)))
    exact hb.comp (measurable_snd.prodMk (hpast.comp measurable_fst))
  have hd : Measurable (fun ω : (ℕ → I) × (ℕ → ℝ) => ω.1 t) :=
    (measurable_pi_apply t).comp measurable_fst
  have hHd : IndepFun (kernelGeneratedHistory f t) (fun ω => ω.1 t) (kernelGameLaw ν) := by
    simpa only [Function.comp_def, b, past, kernelGeneratedHistory] using hblock.comp hb measurable_id
  have hdraw : (kernelGameLaw ν).map (fun ω => ω.1 t) = (volume : Measure I) :=
    (kernelGameLaw_map_tape ν (fun u => u t) (measurable_pi_apply t)).trans
      (Measure.infinitePi_map_eval (fun _ : ℕ => (volume : Measure I)) t)
  have hjoint : (kernelGameLaw ν).map (fun ω => (kernelGeneratedHistory f t ω, ω.1 t)) =
      ((kernelGameLaw ν).map (kernelGeneratedHistory f t)).prod (volume : Measure I) := by
    rw [← hdraw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hH.aemeasurable hd.aemeasurable).1 hHd
  let transform : KernelDecisionHistory t × I → KernelDecisionHistory t × I :=
    fun q => (q.1, f t q.1 q.2)
  have htransform : Measurable transform := measurable_fst.prodMk (hf t)
  calc
    (kernelGameLaw ν).map (fun ω =>
        (kernelGeneratedHistory f t ω, kernelGeneratedPrediction f t ω)) =
        ((kernelGameLaw ν).map (fun ω => (kernelGeneratedHistory f t ω, ω.1 t))).map transform := by
          rw [Measure.map_map htransform (hH.prodMk hd)]
          rfl
    _ = (((kernelGameLaw ν).map (kernelGeneratedHistory f t)).prod (volume : Measure I)).map transform := by
          rw [hjoint]
    _ = (kernelGameLaw ν).map (kernelGeneratedHistory f t) ⊗ₘ κ t :=
          kernelSampler_product_law _ (κ t) (f t) (hf t) (hκ t)
'''
footer = '\nend BanditRL.OnlineLearning\n'
assert text.endswith(footer)
PUBLIC.write_bytes((text[:-len(footer)] + helpers + '\n' + t['header'] + body + footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(before[:-len(footer.encode())])
proving_fixed()
write(RUN/'leaf-K3-attempt-v1.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K3-focused-v1','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K3-focused-v1.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K3-attempt-v1.json',dict(id='K3',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K3-attempt-v1.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      previous_K1_K2_bytes_preserved=True,body_source_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K3-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'Actual fresh draw independence derived from infinitePi and product environment, generated history is strict finite recursion, joint sampler map yields desired compProd law. No desired current-independence/law hypothesis supplied. Frozen terminals and prior bodies retained; package gates pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K3 focused exit',result,'actual compiled',compiled,'K4/K5 and package gates pending.',flush=True)
