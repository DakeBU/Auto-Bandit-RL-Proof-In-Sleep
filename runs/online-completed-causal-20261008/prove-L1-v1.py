from common_proving_v1 import *

s=proving_fixed();assert not PUBLIC.exists()
prefix=(CONTRACT/'targets-v1.lean.txt').read_text(encoding='utf8').split('\ntheorem ')[0]+'\n\n'
body=''' := by
  classical
  rename_i mΩ
  letI : MeasurableSpace Ω := mΩ
  let code : ℝ → ℕ → Bool := MeasurableSpace.mapNatBool ℝ
  have hcode : Measurable code := MeasurableSpace.measurable_mapNatBool ℝ
  have hemb : MeasurableEmbedding code :=
    hcode.measurableEmbedding (MeasurableSpace.injective_mapNatBool ℝ)
  have hcoordinate (n : ℕ) :
      ∃ A : Set Ω, MeasurableSet[F] A ∧
        {ω | code (P ω) n = true} =ᶠ[ae μ] A := by
    have hm : @Measurable Ω Bool (eventuallyMeasurableSpace F (ae μ)) _
        (fun ω => code (P ω) n) :=
      (measurable_pi_apply n).comp (hcode.comp hP)
    exact hm (measurableSet_singleton true)
  choose A hA heq using hcoordinate
  let representative : Ω → ℕ → Bool := fun ω n => decide (ω ∈ A n)
  have hrepresentative : Measurable[F] representative := by
    apply measurable_pi_iff.2
    intro n
    apply measurable_to_bool
    simpa [representative] using hA n
  refine ⟨fun ω => hemb.invFun (representative ω),
    hemb.measurable_invFun.comp hrepresentative, ?_⟩
  filter_upwards [ae_all_iff.2 heq] with ω hω
  have hre : representative ω = code (P ω) := by
    funext n
    have hn := hω n
    change (code (P ω) n = true) = (ω ∈ A n) at hn
    dsimp [representative]
    rw [← hn]
    cases h : code (P ω) n <;> simp [h]
  rw [hre]
  exact (hemb.leftInverse_invFun (P ω)).symm
'''
write(PUBLIC,prefix+'/-! Derived ambient-null-augmentation real versions and causal IID adapters for Orabona v10 printed1/PDF13 and printed3/PDF15. This field is eventuallyMeasurableSpace F (ae ambient_mu), not an asserted completion of mu.trim F. Full causal kernels remain required. -/\n\n'+s['targets'][0]['header']+body+'\nend BanditRL.OnlineLearning\n')
proving_fixed()
write(RUN/'leaf-L1-attempt-v1.lean.raw',PUBLIC.read_bytes())
result=gate('leaf-L1-focused-v1','lake','build','BanditRLProof.OnlineGuessingCompletedCausal',required=False)
log=(RUN/'leaf-L1-focused-v1.log').read_text(encoding='utf8')
artifact=ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingCompletedCausal.olean'
compiled=(result==0 and 'Built BanditRLProof.OnlineGuessingCompletedCausal' in log and
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size>0)
if result==0:assert compiled,'Command0 without actual module compilation witness'
write(RUN/'leaf-L1-attempt-v1.json',dict(id='L1',actual_exit=result,
    current_source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-L1-attempt-v1.lean.raw'),
    frozen_statement_hash=s['targets'][0]['statement_hash'],header_unchanged=True,
    mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
    semantic_BODY_review_pending=True,package_accepted=False))
native('leaf-L1-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if compiled else 'failed','--notes','Actual completed-real-version core focused attempt; immutable target. Command0 alone not compilation. Source/BODY/full/reader/acceptance/delivery gates pending.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',s['targets'][0]['statement_hash'],
    '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','4','--obligations-after','4')
proving_fixed()
print('L1 actual focused exit',result,'actual compiled witness',compiled,'four accepted obligations still pending.',flush=True)
