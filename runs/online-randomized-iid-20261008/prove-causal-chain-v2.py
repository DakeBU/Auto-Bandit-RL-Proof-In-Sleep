from common_reviewed_v2 import *

headers_fixed(1)
assert load(RUN/'R001-focused-build-v2-exit.json')['exit_code']==0
targets=load(CONTRACT/'targets-v2.json')['rows']
bodies={
'R002':''' := by
  have hpast : Measurable (fun ω (i : (↑(Finset.range t) : Type)) => Y i ω) :=
    measurable_pi_lambda _ (fun i => hY i)
  have hpc : IndepFun (fun ω (i : (↑(Finset.range t) : Type)) => Y i ω) (Y t) μ := by
    have hi := iIndepFun.indepFun_finset (Finset.range t) {t} (by simp) hind hY
    simpa only [Function.comp_def] using hi.comp measurable_id
      (measurable_pi_apply (⟨t, by simp⟩ : (↑({t} : Finset ℕ) : Type)))
  have hblock : IndepFun S
      (fun ω => ((fun i : (↑(Finset.range t) : Type) => Y i ω), Y t ω)) μ := by
    have he : Measurable (fun y : ℕ → ℝ =>
        ((fun i : (↑(Finset.range t) : Type) => y i), y t)) :=
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i)).prodMk (measurable_pi_apply t)
    simpa only [Function.comp_def] using hseed.comp measurable_id he
  exact independent_private_seed_pair μ S _ _ hS hpast (hY t) hblock hpc
''',
'R003':''' := by
  intro s t hst
  let restrict : (Seed × ((↑(Finset.range t) : Type) → ℝ)) →
      (Seed × ((↑(Finset.range s) : Type) → ℝ)) :=
    fun q => (q.1, fun i => q.2 ⟨i, Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp i.property) hst)⟩)
  have hr : Measurable restrict := by
    unfold restrict
    fun_prop
  have hc := MeasurableSpace.comap_mono
    (g := fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) hr.comap_le
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, restrict,
    privateSeedPastInformation] using hc
''',
'R004':''' := by
  have hi : Indep (privateSeedPastInformation S Y t)
      (MeasurableSpace.comap (Y t) inferInstance) μ :=
    (IndepFun_iff_Indep _ _ μ).1 (private_seed_past_independent μ Y hY hind S hS hseed t)
  exact (IndepFun_iff_Indep P (Y t) μ).2
    (indep_of_indep_of_le_left hi (hP.comap_le.trans hF))
''',
'R005':''' := by
  have hi := (private_seed_past_independent μ Y hY hind S hS hseed t).comp
    (hp t) measurable_id
  simpa only [Function.comp_def] using hi
''',
'R006':''' := by
  have hambient (t : ℕ) : Measurable (prediction t) := by
    have hinfo : privateSeedPastInformation S Y t ≤ ‹MeasurableSpace Ω› :=
      (hS.prodMk (measurable_pi_lambda _ (fun i : (↑(Finset.range t) : Type) => hY i))).comap_le
    exact Measurable.of_comap_le ((hP t).comap_le.trans ((hF t).trans hinfo))
  have hL (t : ℕ) : MemLp (prediction t) 2 μ :=
    memLp_of_bounded (hpb t) (hambient t).aestronglyMeasurable 2
  have hInd (t : ℕ) : IndepFun (prediction t) (Y t) μ :=
    predictable_private_seed_independent μ Y hY hind S hS hseed t (F t) (hF t)
      (prediction t) (hP t)
  have he : expectedFixedRegret μ Y prediction T =
      ∑ t ∈ Finset.range T, ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
    unfold expectedFixedRegret
    rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
    exact iid_cumulative_prediction_decomposition μ Y hY hlaw hb prediction hL hInd T
  refine ⟨he, ?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun t _ => integral_nonneg (fun ω => sq_nonneg _))
''',
'R007':''' := by
  have hall : ∀ᵐ ω ∂μ, ∀ t, Y t ω ∈ Set.Icc (0 : ℝ) 1 := ae_all_iff.2 hb
  have hmeas (t : ℕ) : Measurable[privateSeedPastInformation S Y t]
      (fun ω => policy t (S ω, fun i => Y i ω)) := by
    change Measurable[MeasurableSpace.comap
      (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) inferInstance] _
    exact (hp t).comp (comap_measurable _)
  have hbound (t : ℕ) : ∀ᵐ ω ∂μ,
      policy t (S ω, fun i => Y i ω) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hall] with ω hω
    exact hpb t (S ω) _ (fun i => hω i)
  exact predictable_private_seed_expectedFixed_excess μ Y hY hlaw hb hind S hS hseed
    (privateSeedPastInformation S Y) (fun _ => le_rfl)
    (fun t ω => policy t (S ω, fun i => Y i ω)) hmeas hbound T
'''}
write(RUN/'causal-body-candidates-v2.json',dict(contract_version=2,bodies=bodies,
    route='single lower; one ready leaf appended and compiled before next leaf', no_statement_edits=True))
for i,row in enumerate(targets[1:],2):
    headers_fixed(i-1)
    native(row['id']+'-worker-running-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','running',
        '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-'+row['id']+'-V2','--harness','hierarchical',
        '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--notes',
        'Dependency-ready exact v2 leaf '+row['id']+'; actual available parents, explicit reviewed DAG, no target weakening or supplied current-independence/performance certificate.')
    text=PUBLIC.read_text(encoding='utf8')
    assert text.count('end BanditRL.OnlineLearning')==1
    text=text.replace('end BanditRL.OnlineLearning',
        '/-- '+row['source_class']+' -/\n'+row['header']+bodies[row['id']]+'\nend BanditRL.OnlineLearning',1)
    PUBLIC.write_bytes(text.encode('utf8'))
    write(RUN/'leaves'/(row['id']+'-body-v2.lean'),PUBLIC.read_bytes())
    headers_fixed(i)
    gate(row['id']+'-focused-build-v2','lake','build','BanditRLProof.OnlineGuessingRandomizedIID')
    native(row['id']+'-fence-v2','statement-fence','--declaration',row['name'],'--file',PUBLIC,
        '--output',RUN/(row['id']+'-fence-v2.json'))
    native(row['id']+'-safe-verify-v2','safe-verify','--fence',RUN/(row['id']+'-fence-v2.json'),'--lean-file',PUBLIC)
    native(row['id']+'-worker-compiled-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
        '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-'+row['id']+'-V2','--harness','hierarchical',
        '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--new-declaration',row['name'],
        '--verifier-evidence',RUN/(row['id']+'-focused-build-v2-exit.json'),'--progress-class','compiled-leaf',
        '--obligations-before',str(8-i),'--obligations-after',str(7-i),'--notes',
        'Actual frozen '+row['id']+' body focused-builds; header fence scan separate. Body semantic/canary/kernel/root/fullharness/site/FINAL/PR acceptance still pending.')
    write(RUN/(row['id']+'-progress-v2.json'),dict(contract_version=2,closed=[r['name'] for r in targets[:i]],
        remaining=[r['name'] for r in targets[i:]], public_sha256=sha(PUBLIC),
        package_accepted=False,chapter_complete=False,goal_complete=False))
headers_fixed(7)
write(RUN/'30_worker-causal-chain-v2.md','Seven exact frozen v2 bodies focused-build/fence checked sequentially. Joint laws/tuple past independence are actual produced parents; generated information monotonicity and subfield weakening give predictable current independence. Ambient measurability/L2 from a.s.support, genuine PR194 minE and same-prefix decomposition give R006; R007 actually instantiates generated information with policy(seed,finite past), legal cube only. Seven-terminal mathematical frontier7→0, not package acceptance. Public canaries/kernel/actual VALUE calls/BODY/root/Tests/fullharness/site/FINAL/native/PR remain.')
print('All seven frozen public bodies actually build; candidate validation and semantic/body gates pending.')
