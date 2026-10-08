from common_proving_v1 import *
s=proving_fixed();assert not PUBLIC.exists()
prefix=(CONTRACT/'context-v1.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
body=''' := by
  constructor
  · intro hL
    rcases hL 0 (by norm_num) with ⟨a0, ha0, h0⟩
    rcases hL 1 (by norm_num) with ⟨a1, ha1, h1⟩
    have hs0 := (meanPredict_fixedRegret_limit_iff y hy 0 a0).mp h0
    have hs1 := (meanPredict_fixedRegret_limit_iff y hy 1 a1).mp h1
    let m : ℝ := (-a0 - (-a1) + 1) / 2
    have hh := ((hs0.sub hs1).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))).div_const (2 : ℝ)
    have hm : Tendsto (empiricalMean y) atTop (nhds m) := by
      convert hh using 1
      funext T
      ring
    have hb : ∀ᶠ T : ℕ in atTop, empiricalMean y T ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
      exact empiricalMean_mem y T hT (fun t _ => hy t)
    have hlo : 0 ≤ m := ge_of_tendsto hm (hb.mono (fun _ h => h.1))
    have hup : m ≤ 1 := le_of_tendsto hm (hb.mono (fun _ h => h.2))
    exact ⟨m, ⟨hlo, hup⟩, hm⟩
  · rintro ⟨m, hmUnit, hm⟩
    exact (meanPredict_limitNoRegret_of_mean_converges y hy m hm).2
'''
write(PUBLIC,prefix+'\n/-- Derived literal-limit criterion for the actual bounded squared-loss FTL. -/\n'+s['targets'][0]['header']+body+'\nend BanditRL.OnlineLearning\n')
proving_fixed();write(RUN/'D1-attempt-v1.lean.raw',PUBLIC.read_bytes())
code=gate('D1-focused-v1','lake','build','BanditRLProof.OnlineFTLOscillation',required=False)
write(RUN/'D1-attempt-v1.json',dict(leaf='D1',statement_hash=s['targets'][0]['statement_hash'],
    source_snapshot_sha256=sha(RUN/'D1-attempt-v1.lean.raw'),actual_build_exit=code,
    status='compiled' if code==0 else 'repair',package_accepted=False,chapter_complete=False,goal_complete=False))
gate('D1-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
    '--task',TASK,'--role','lower','--kind','attempt','--status','compiled' if code==0 else 'failed',
    '--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),
    '--statement-hash',s['targets'][0]['statement_hash'],'--attempt-id','D1-v1',
    '--verifier-evidence',RUN/'D1-focused-v1-exit.json','--progress-class','unreviewed',
    '--obligations-before','4','--obligations-after','4','--notes','Actual frozen D1 body focused build; semantic/body/full gates pending.')
assert code==0,'Retain failed attempt and repair same target.'
native('D1-fence-v1','statement-fence','--declaration',s['targets'][0]['name'],'--file',PUBLIC.relative_to(ROOT),
    '--source-assumption','(hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1)','--output',RUN/'fences/D1-v1.json')
native('D1-safe-v1','safe-verify','--fence',RUN/'fences/D1-v1.json')
print('Actual frozen D1 focused body/fence passed; other three bodies and all package gates required.',flush=True)
