from common_proving_v1 import *
s=proving_fixed()
assert not PUBLIC.exists()
text=(CONTRACT/'targets-v1.lean.txt').read_text(encoding='utf8')
prefix=text.split('\ntheorem ')[0]+'\n\n'
body=''' := by
  classical
  have hfactor (t : ℕ) :
      ∃ f : (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
        Measurable f ∧ (hP t).mk (prediction t) =
          fun ω => f (S ω, fun i => Y i ω) := by
    have hm : Measurable[privateSeedPastInformation S Y t] ((hP t).mk (prediction t)) :=
      Measurable.of_comap_le ((hP t).measurable_mk.comap_le.trans (hF t))
    change Measurable[MeasurableSpace.comap
      (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) inferInstance] _ at hm
    obtain ⟨f, hf, he⟩ := hm.exists_eq_measurable_comp
    exact ⟨f, hf, by simpa only [Function.comp_def] using he⟩
  choose f hf he using hfactor
  let policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ :=
    fun t q => (Set.projIcc (0 : ℝ) 1 zero_le_one (f t q) : ℝ)
  refine ⟨policy, ?_, ?_, ?_⟩
  · intro t
    exact ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp
      (hf t)).subtype_coe
  · intro t q
    exact (Set.projIcc (0 : ℝ) 1 zero_le_one (f t q)).property
  · apply ae_all_iff.2
    intro t
    filter_upwards [(hP t).ae_eq_mk, hpb t] with ω hω hbω
    have hq : f t (S ω, fun i => Y i ω) = prediction t ω :=
      (congrFun (he t) ω).symm.trans hω.symm
    change prediction t ω = (Set.projIcc (0 : ℝ) 1 zero_le_one
      (f t (S ω, fun i => Y i ω)) : ℝ)
    rw [hq, Set.projIcc_of_mem zero_le_one hbω]
'''
write(PUBLIC,prefix+'/-! Derived AE strict-past information infrastructure for Orabona v10 printed1/PDF13 and printed3/PDF15. A classical measurable version, not off-null identity or an executable learner constructor. Full completed-information and universal stochastic-kernel coverage remain separate required obligations. -/\n\n'+s['targets'][0]['header']+body+'\nend BanditRL.OnlineLearning\n')
proving_fixed()
write(RUN/'leaf-L1-attempt-v1.lean.raw',PUBLIC.read_bytes())
result=gate('leaf-L1-focused-v1','lake','build','BanditRLProof.OnlineGuessingAECausal',required=False)
write(RUN/'leaf-L1-attempt-v1.json',dict(id='L1',actual_exit=result,
    current_source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-L1-attempt-v1.lean.raw'),
    frozen_statement_hash=s['targets'][0]['statement_hash'],header_unchanged=True,
    mathematical_body_compiled=result==0,semantic_BODY_review_pending=True,package_accepted=False))
native('leaf-L1-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if result==0 else 'failed','--notes','L1 exact stabilized body, focused module compile only; semantic/body/full/reader gates pending.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',s['targets'][0]['statement_hash'],
    '--progress-class','compiled-leaf' if result==0 else 'diagnostic','--obligations-before','3','--obligations-after','3')
proving_fixed()
print('L1 actual focused exit',result,'; accepted source/package obligations remain3')
