from common_reviewed_v1 import *
reviewed_fixed()
assert load(RUN/'first-leaf-focused-build-v1-exit.json')['exit_code']==0
write(RUN/'leaf-first-public-v1.lean.raw',PUBLIC.read_bytes())
targets=load(CONTRACT/'targets-v1.json')['targets']
bodies=[
'''  by_contra h
  have hpos : 0 < a := lt_of_not_ge h
  have hbound : a ≤ a / 2 :=
    le_of_tendsto hl (hNR u hu (a / 2) (by linarith))
  linarith''',
'''  intro u hu ε hε
  rcases hL u hu with ⟨a, hle, ha⟩
  exact ((tendsto_order.mp ha).2 ε (lt_of_le_of_lt hle hε)).mono
    (fun _ h => h.le)''',
'''  constructor
  · exact limitNoRegret_implies_noRegret V loss prediction
  · intro hNR u hu
    rcases hc u hu with ⟨a, ha⟩
    exact ⟨a, noRegret_limit_nonpos V loss prediction hNR u hu a ha, ha⟩''',
'''  have hs : (∑ t ∈ Finset.range T, loss t u) = potential T * u := by
    induction T with
    | zero => simp [potential]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      change potential n * u + (potential (n + 1) - potential n) * u =
        potential (n + 1) * u
      ring
  unfold comparatorRegret
  have hz : (∑ t ∈ Finset.range T, loss t (0 : ℝ)) = 0 := by
    simp [loss]
  rw [hz, hs]
  ring''',
'''  intro u hu ε hε
  apply Filter.Eventually.of_forall
  intro T
  rw [regret_eq]
  have hp : 0 ≤ potential T := by
    unfold potential
    split_ifs
    · exact Nat.cast_nonneg T
    · norm_num
  have hn : -potential T * u ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) hu.1
  exact (div_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg T)).trans hε.le''',
'''  rw [regret_eq]
  have he : 2 * (n + 1) % 2 = 0 := by omega
  simp only [potential, if_pos he, mul_one]
  have hn : ((2 * (n + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [neg_div, div_self hn]''',
'''  rw [regret_eq]
  have ho : (2 * n + 1) % 2 ≠ 0 := by omega
  simp [potential, ho]''',
'''  rintro ⟨a, ha⟩
  have he : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega) tendsto_id
  have ho : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega) tendsto_id
  have hE : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds a) := by
    simpa only [Function.comp_def, normalized_even] using ha.comp he
  have hO : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds a) := by
    simpa only [Function.comp_def, normalized_odd] using ha.comp ho
  have hEa : a = (-1 : ℝ) := tendsto_nhds_unique hE tendsto_const_nhds
  have hOa : a = (0 : ℝ) := tendsto_nhds_unique hO tendsto_const_nhds
  linarith''',
'''  refine ⟨noRegret, ?_⟩
  intro hL
  rcases hL 1 (by norm_num) with ⟨a, _, ha⟩
  exact no_limit ⟨a, ha⟩''']
context=(CONTRACT/'public-context-v1.lean').read_text(encoding='utf8');prefix,rest=context.split('namespace NoRegretCounterexample',1)
defs=rest[:rest.index('end NoRegretCounterexample')]
core='\n\n'.join(x['header']+' := by\n'+b for x,b in zip(targets[:3],bodies[:3]))
counter='\n\n'.join(x['header']+' := by\n'+b for x,b in zip(targets[3:],bodies[3:]))
s=prefix+core+'\n\nnamespace NoRegretCounterexample'+defs+counter+'\n\nend NoRegretCounterexample\nend BanditRL.OnlineLearning\n'
for x in targets:assert x['header']+' := by' in s
PUBLIC.write_bytes(s.encode('utf8'))
write(RUN/'30_worker-route-v1.md','Preserve frozen targets/models and first compiled body. Lower follows the reviewed route: two actual epsilon-limit bridges; inductive finite loss telescoping; nonnegative potential/sign upper bound; actual positive even/odd subsequence normalized identities; cofinal maps and real limit uniqueness; same-process strict separation. No supplied desired regret/moment/stability assumption, no source or carrier restriction. All nine frozen statements present with actual bodies; focused build still determines compiled status.\n')
gate('all-nine-focused-build-v1','lake','build','BanditRLProof.OnlineNoRegretSemantics')
write(RUN/'leaf-progress-v2.json',dict(contract_target_count=9,closed_public_targets=[x['name'] for x in targets],remaining_contract_targets=[],public_sha256=sha(PUBLIC),new_public_proofs=9,new_public_definitions=3,source_body_review_pending=True,public_canary_and_combined_full_gates_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
reviewed_fixed();print('All nine exact public theorem bodies compiled; candidate validation/review remains')
