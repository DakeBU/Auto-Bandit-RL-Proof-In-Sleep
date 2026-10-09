from proof_driver import *
fixed()
assert load(RUN/'six-production-focused-summary-v1.json')['proof_terminal_remaining']==0
canaries=load(CONTRACT/'canary-headers-draft-v2.json')
TEST=ROOT/'Tests/OnlinePrescientBregmanSourceCanary.lean'
assert not TEST.exists()
for row in canaries['targets']:
    write(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'),lifecycle.make_statement_fence(declaration=row['name'],file=TEST.relative_to(ROOT).as_posix(),statement=row['header']))
row=canaries['targets'][0]
lets='\n'.join(line for line in row['header'].splitlines() if line.startswith('    let '))
body='''  dsimp only
'''+lets.replace('    let ','  let ')+'''
  have hs0 := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.1
  have hs1 := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.1
  have hclosed := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.1
  have hstrict := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.2.1
  have hdiff := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.2.2.1
  have hold := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.2.2.2.1
  have hterminal := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.2.2.2.2.1
  have hD10 := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.2.2.2.2.2.1
  have hD21 := BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run.2.2.2.2.2.2.2.2.2.2.1
  have hVn : V.Nonempty := ⟨0, by norm_num [V]⟩
  have hbot (t : ℕ) (_ht : t < 2) (z : ℝ) : loss t z ≠ ⊥ := by
    by_cases ht0 : t = 0 <;> by_cases hz : z ∈ V <;> simp [loss, ht0, f0, f1, hz]
  have hdom (t : ℕ) (_ht : t < 2) : V ⊆ effectiveDomain (loss t) := by
    intro z hz
    change loss t z < ⊤
    by_cases ht0 : t = 0 <;> simp [loss, ht0, f0, f1, hz]
  have hs (t : ℕ) (_ht : t < 2) : ∀ z ∈ V, (SourceSubdifferential (loss t) z).Nonempty := by
    by_cases ht0 : t = 0
    · simpa [loss, ht0] using hs0
    · simpa [loss, ht0] using hs1
  have hproper (t : ℕ) (ht : t < 2) : SourceProper (loss t) :=
    sourceProper_of_domain (loss t) V hVn (hbot t ht) (hdom t ht)
  have hf0 : SourceProper f0 := by simpa [loss] using hproper 0 (by decide)
  have hmin (t : ℕ) (ht : t < 2) : x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((1⁻¹ * divergence ψ z (x t) : ℝ) : EReal)) V
        (x (t + 1)) := by
    obtain ⟨p, hprev, hp, hm⟩ := iterate_succ_some_spec V ψ (fun _ => 1) loss (1 / 2)
      (x (t + 1)) t (hold (t + 1) (Nat.succ_le_of_lt ht))
    have heq : p = x t := Option.some.inj (hprev.symm.trans (hold t (Nat.le_of_lt ht)))
    subst p
    exact ⟨hp, hm⟩
  have hinit : x 0 = (1 / 2 : ℝ) := by norm_num [x]
  have hseq := iterate_eq_of_source_updates V univ (convex_Icc (-1 : ℝ) 1)
    (fun _ _ => mem_univ _) ψ hstrict (fun _ => 1) loss (1 / 2) x 2 hinit
    (by intros; norm_num) hproper hs hmin
  have hc : StrictConvexOn ℝ V (fun z => (f0 z).toReal + divergence ψ z (1 / 2)) := by
    simpa using penalized_strictConvex V univ (convex_Icc (-1 : ℝ) 1)
      (fun _ _ => mem_univ _) ψ hstrict f0 hf0 hs0 1 (by norm_num) (1 / 2)
  have ha : advance V ψ 1 f0 (1 / 2) = some 0 :=
    advance_eq_some_of_minimizer V univ (convex_Icc (-1 : ℝ) 1)
      (fun _ _ => mem_univ _) ψ hstrict f0 hf0 hs0 1 (by norm_num) (1 / 2) 0
      (by norm_num [V]) (by simpa [loss, x] using (hmin 0 (by decide)).2)
  have hclosedX : SourceClosed (fun z => (ψ z : EReal) + extendedIndicator univ z) := by
    simpa [extendedIndicator] using hclosed
  have hd : DifferentiableOn ℝ ψ (interior (univ : Set ℝ)) := by
    simpa only [interior_univ] using hdiff
  have hi : ∀ t ≤ 2, x t ∈ interior (univ : Set ℝ) := by simp
  have hprinted : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1 := by
    intro u hu
    exact source_fixed_regret V univ (convex_Icc (-1 : ℝ) 1) hVn isClosed_Icc
      (fun _ _ => mem_univ _) ψ hstrict hclosedX hd 1 (by norm_num) loss (1 / 2) x 2
      hinit hi hbot hdom hs hmin u hu
  have hA : divergence ψ (-1 / 2) (1 / 2) = 5 / 8 := by simpa [x] using hterminal
  have hB : divergence ψ 0 (1 / 2) = 11 / 64 := by simpa [x] using hD10
  have hC : divergence ψ (1 / 2) 0 = 9 / 64 := by simpa [x] using hD21
  have hnum : (-9 / 8 : ℝ) ≤ 5 / 16 := by
    convert hprinted (-1 / 2) (by norm_num [V]) using 1 <;>
      norm_num [sum_range_succ, loss, f0, f1, V, x, hA, hB, hC]
  exact ⟨hf0, hc, ha, hseq, hD10, hD21, hprinted, hnum⟩
'''
native_snapshot('fixed-canary-proving-before-v1')
event('fixed-canary-proving-event-v1','proving',dict(task=TASK,leaf=row['name'],canary=True,production_terminals_closed=6,accepted=False))
text=canaries['imports']+'set_option autoImplicit false\n\n'+row['header'].rstrip()+' := by\n'+body+'\nend BanditRL.OnlinePrescientBregmanSourceCanary\n'
write(TEST,text)
write(RUN/'fixed-canary-attempt-source-v1.lean',TEST.read_bytes())
code,out=capture('fixed-canary-focused-build-v1','lake','build','Tests.OnlinePrescientBregmanSourceCanary',required=False)
compiled=code==0 and 'Built Tests.OnlinePrescientBregmanSourceCanary' in out and 'Build completed successfully' in out
write(RUN/'fixed-canary-focused-inspected-v1.json',dict(actual_exit=code,actual_stdout=out,compiled_module_markers=compiled,source=rows([TEST]),header_frozen=True,package_accepted=False))
assert compiled
