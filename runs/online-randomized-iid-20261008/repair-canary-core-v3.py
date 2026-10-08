from common_reviewed_v2 import *

headers_fixed(7)
assert load(RUN/'canary-core-focused-build-v2-exit.json')['exit_code']==1
write(RUN/'canary-core-failure-repair-v3.json',dict(failed_build='canary-core-focused-build-v2-exit.json',
    failed_source='leaves/canary-core-v2.lean',contract_version=2,public_terminal_changed=False,
    canary_statement_changed=False,issues=['explicit map-fst shape for seed law',
        'piecewise measurable proof requires measurable Iic',
        'IdentDistrib integral composition beta normalization', 'two-round sum must normalize right side separately'],
    repair='Only proof bodies, actual original counterexample/deviation statements preserved.'))
text=CANARY.read_text(encoding='utf8')
changes=[
('  simp [seededLaw, seed]\n','  change (coinLaw.prod iidLaw).map Prod.fst = coinLaw.map (fun x : ℝ => x)\n  simp\n'),
('  unfold seedBit\n  fun_prop\n','  unfold seedBit\n  exact measurable_const.ite measurableSet_Iic measurable_const\n'),
('''    rw [(seed_has_coinLaw.comp (by fun_prop : Measurable (fun x => (seedBit x - 1 / 2)^2))).integral_eq,
      coinLaw_integral]
    norm_num [seedBit]''','''    have hm : Measurable (fun x : ℝ => (seedBit x - 1 / 2)^2) :=
      (seedBit_measurable.sub measurable_const).pow_const 2
    have he : (∫ ω, (seedBit (seed ω) - 1 / 2)^2 ∂seededLaw) =
        ∫ x, (seedBit x - 1 / 2)^2 ∂coinLaw := by
      simpa only [Function.comp_def] using (seed_has_coinLaw.comp hm).integral_eq
    rw [he, coinLaw_integral]
    norm_num [seedBit]'''),
('''  simp [Finset.sum_range_succ, seededPolicy, lastPolicy, target_mean, hfirst, hsecond] at he
  exact he''','''  apply he.trans
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change (∫ ω, (seedBit (seed ω) - ∫ ω, target 0 ω ∂seededLaw)^2 ∂seededLaw) +
    (∫ ω, (target 0 ω - ∫ ω, target 0 ω ∂seededLaw)^2 ∂seededLaw) = 1 / 2
  rw [target_mean, hfirst, hsecond]
  norm_num''')]
for old,new in changes:
    assert text.count(old)==1,old
    text=text.replace(old,new,1)
CANARY.write_bytes(text.encode('utf8'))
write(RUN/'leaves'/'canary-core-v3.lean',CANARY.read_bytes())
gate('canary-core-focused-build-v3','lake','build','Tests.OnlineGuessingRandomizedIIDCanary')
headers_fixed(7)
print('Actual nondegenerate independent-tape/infinite-IID core canary compiles; XOR boundary still required.')
