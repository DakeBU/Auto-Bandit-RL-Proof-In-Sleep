from proof_driver import *
fixed()
assert load(RUN/'fixed-canary-focused-inspected-v2.json')['compiled_module_markers']
TEST=ROOT/'Tests/OnlinePrescientBregmanSourceCanary.lean'
row=load(CONTRACT/'canary-headers-draft-v2.json')['targets'][1]
lets='\n'.join(line for line in row['header'].splitlines() if line.startswith('    let '))
body='  dsimp only\n'+lets.replace('    let ','  let ')+'\n'
parent='BanditRL.OnlinePrescientBregmanRegretCanary.decreasing_signed_run'
for alias,index in [('hs0',3),('hs1',4),('hclosed',5),('hstrict',6),('hdiff',7),('hη',10),('hmono',11),('hold',12),('hmovement',15),('hmaxneg',16),('hmaxpos',17)]:
    body+='  have '+alias+' := '+parent+'.2'*(index-1)+'.1\n'
body+='''  have hVn : V.Nonempty := ⟨0, by norm_num [V]⟩
  have hbot (t : ℕ) (_ht : t < 2) (z : ℝ) : loss t z ≠ ⊥ := by
    by_cases ht0 : t = 0 <;> by_cases hz : z ∈ V <;> simp [loss, ht0, f0, f1, hz]
  have hdom (t : ℕ) (_ht : t < 2) : V ⊆ effectiveDomain (loss t) := by
    intro z hz
    change loss t z < ⊤
    by_cases ht0 : t = 0 <;> simp [loss, ht0, f0, f1, hz]
  have hs (t : ℕ) (_ht : t < 2) : ∀ z ∈ V, (SourceSubdifferential (loss t) z).Nonempty := by
    intro z hz
    by_cases ht0 : t = 0
    · simpa only [loss, if_pos ht0] using hs0 z hz
    · simpa only [loss, if_neg ht0] using hs1 z hz
  have hproper (t : ℕ) (ht : t < 2) : SourceProper (loss t) :=
    sourceProper_of_domain (loss t) V hVn (hbot t ht) (hdom t ht)
  have hmin (t : ℕ) (ht : t < 2) : x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal)) V
        (x (t + 1)) := by
    obtain ⟨p, hprev, hp, hm⟩ := iterate_succ_some_spec V ψ η loss (1 / 2)
      (x (t + 1)) t (hold (t + 1) (Nat.succ_le_of_lt ht))
    have heq : p = x t := Option.some.inj (hprev.symm.trans (hold t (Nat.le_of_lt ht)))
    subst p
    exact ⟨hp, hm⟩
  have hinit : x 0 = (1 / 2 : ℝ) := by norm_num [x]
  have hseq := iterate_eq_of_source_updates V univ (convex_Icc (-1 : ℝ) 1)
    (fun _ _ => mem_univ _) ψ hstrict η loss (1 / 2) x 2 hinit hη hproper hs hmin
  have hclosedX : SourceClosed (fun z => (ψ z : EReal) + extendedIndicator univ z) := by
    simpa [extendedIndicator] using hclosed
  have hd : DifferentiableOn ℝ ψ (interior (univ : Set ℝ)) := by
    simpa only [interior_univ] using hdiff
  have hi : ∀ t ≤ 2, x t ∈ interior (univ : Set ℝ) := by simp
  have hprinted : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        ((range 2).sup' (by decide) (fun t => divergence ψ u (x t))) / η 1 -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / η t := by
    intro u hu
    exact source_variable_regret V univ (convex_Icc (-1 : ℝ) 1) hVn isClosed_Icc
      (fun _ _ => mem_univ _) ψ hstrict hclosedX hd η loss (1 / 2) x 2 (by decide)
      hη hinit hi hmono hbot hdom hs hmin u hu
  have hnum : (-1 / 2 : ℝ) ≤ -11 / 64 := by
    have hb := hprinted (1 / 2) (by norm_num [V])
    rw [hmaxpos, hmovement] at hb
    convert hb using 1 <;> norm_num [sum_range_succ, loss, f0, f1, V, x, η]
  exact ⟨hseq, hmovement, hmaxneg, hmaxpos, hprinted, hnum⟩
'''
old=TEST.read_bytes()
write(RUN/'decreasing-canary-exact-before-v1.json',dict(path=TEST.relative_to(ROOT).as_posix(),sha256=sha(TEST),before_raw_base64=base64.b64encode(old).decode('ascii')))
native_snapshot('decreasing-canary-proving-before-v1')
event('decreasing-canary-proving-event-v1','proving',dict(task=TASK,leaf=row['name'],canary=True,production_terminals_closed=6,accepted=False))
addition='\nnamespace BanditRL.OnlinePrescientBregmanSourceCanary\n\n'+row['header'].rstrip()+' := by\n'+body+'\nend BanditRL.OnlinePrescientBregmanSourceCanary\n'
TEST.write_bytes(old+addition.encode('utf8'))
write(RUN/'decreasing-canary-attempt-source-v1.lean',TEST.read_bytes())
code,out=capture('decreasing-canary-focused-build-v1','lake','build','Tests.OnlinePrescientBregmanSourceCanary',required=False)
compiled=code==0 and 'Built Tests.OnlinePrescientBregmanSourceCanary' in out and 'Build completed successfully' in out
actual=lifecycle.lean_declaration_header(TEST,row['name'])
assert lifecycle.statement_hash(actual)==load(CONTRACT/'frozen-decreasing_source_run-v1.json')['statement_hash']
write(RUN/'decreasing-canary-focused-inspected-v1.json',dict(actual_exit=code,actual_stdout=out,compiled_module_markers=compiled,source=rows([TEST]),header_frozen=True,package_accepted=False))
assert compiled
