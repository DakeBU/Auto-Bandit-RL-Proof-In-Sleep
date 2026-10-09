from canary_driver import *
assert not TEST.exists()
review=load(RUN/'full-body-canary-review-v1.json')
assert sha(RUN/'full-body-canary-review-v1.json')=='b23b98482347317ad1e93cde37956b88f0c9e3c1eaf537db82e8028d057ba9ef'
assert review['BODY_verdict']=='accepted-with-explicit-delta' and review['canary_CONTRACT_verdict']=='accepted-with-explicit-delta' and not review['required_blocking_repairs']
for manifest,key in [('full-body-canary-review-inputs-v1.json','immutable_rows'),('full-body-canary-review-supplement-v1.json','rows')]:
    for row in load(RUN/manifest)[key]:assert sha(row['path'])==row['sha256']
assert load(RUN/'canary-type-probe-v2.json')['actual_exit']==0
for row in canaries['targets']:
    frozen=lifecycle.make_statement_fence(declaration=row['name'],file=TEST.relative_to(ROOT).as_posix(),statement=row['header'])
    frozen['scoped_context_and_definitions']=canaries['prefix']
    frozen['raw_header_sha256']=row['raw_header_sha256']
    write(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'),frozen)
write(CONTRACT/'canaries-stabilized-v1.json',dict(targets=canaries['targets'],complete_prefix=canaries['prefix'],prefix_sha256=hashlib.sha256(canaries['prefix'].encode('utf8')).hexdigest(),BODY_and_CONTRACT_review=rows([RUN/'full-body-canary-review-v1.md',RUN/'full-body-canary-review-v1.json']),neutral_reconstruction=rows([RUN/'canary-blind-reconstruction-v1.md',RUN/'canary-blind-reconstruction-v1.json']),Test=TEST.relative_to(ROOT).as_posix(),only_test_lowering_allowed=True,canary_BODY='required/open',full_gates='required/open'))
native_snapshot('canaries-stabilized-native-before-v1')
event('canaries-stabilized-v1','stabilized',dict(task=TASK,source_terminals_focused_compiled=11,source_BODY_accepted=True,canary_CONTRACT_accepted=True,Test_only=TEST.relative_to(ROOT).as_posix(),canary_conjunction_sizes=[7,9],different_horizon_loss_streams=True,package_accepted=False))
write(TEST,canaries['prefix'])
lower_canary(0,'''  classical
  have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
  have hstate (t : ℕ) : scalarRun 2 t =
      -(∑ i ∈ range t, powerSteps (1/2) i * switchSlope 2 i) := by
    have hloss : (fun (s : ℕ) (z : ℝ) => (switchLoss 2 (1 : ℝ) s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope 2 s : ℝ) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, hin, mul_comm]
    unfold scalarRun
    rw [hloss, iterate_affine_prefix]
    simp
  have h0 : powerSteps (1/2) 0 = 1 := by norm_num [powerSteps]
  have hpos : 0 < powerSteps (1/2) 1 := powerSteps_pos (1/2) 1
  have hdec : powerSteps (1/2) 1 < powerSteps (1/2) 0 := by
    norm_num [powerSteps]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hx0 : scalarRun 2 0 = 0 := by simpa using hstate 0
  have hx1 : scalarRun 2 1 = 1 := by
    simpa [sum_range_succ, switchSlope, powerSteps] using hstate 1
  have hx2 : scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) := by
    have h := hstate 2
    norm_num [sum_range_succ, switchSlope, powerSteps] at h
    linarith only [h]
  have hp : (2 : ℝ) ^ (1/2 : ℝ) = 2 * (2 : ℝ) ^ (-(1/2 : ℝ)) := by
    conv_lhs => rw [show (1/2 : ℝ) = 1 + (-(1/2 : ℝ)) by norm_num]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hr : scalarRegret 2 = 1 := by
    have h := switching_scalar_regret_identity (1/2) 2
    change scalarRegret 2 = _ at h
    norm_num [sum_range_succ, powerSteps] at h
    rw [hp] at h
    linarith only [h]
  exact ⟨h0, hpos, hdec, hx0, hx1, hx2, hr⟩
''')
