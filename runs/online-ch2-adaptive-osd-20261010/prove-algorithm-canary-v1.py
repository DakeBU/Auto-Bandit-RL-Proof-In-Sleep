from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
review_path=RUN/'benchmark-BODY-canary-CONTRACT-review-v1.json'
assert sha(review_path)=='83baacd93020fd632de97db27f404644dd8c2402084a62b3e7bf18f67e551943'
review=load(review_path)
assert review['inputs_unchanged'] and not review['required_blocking_repairs']
for row in review['raw_input_checks']:
    assert sha(row['path'])==row['expected_sha256']==row['before_sha256']==row['after_sha256']
window=review['approved_conditional_edit_window']
public=Path(window['path'])
assert not public.exists() and sha(window['context_path'])==window['context_sha256']
headers=load(CONTRACT/'algorithm-canary-fingerprints-draft-v1.json')['headers']
for row in window['headers']:
    assert sha(row['path'])==row['sha256']==headers[row['target']]['raw_sha256']
write(CONTRACT/'algorithm-canary-stabilized-v1.json',dict(review_sha256=sha(review_path),
    exact_headers=headers,allowed_window=window,context_sha256=window['context_sha256']))
write(RUN/'worker-algorithm-canary-route-v1.md','Before tactics: read full distinct favorable benchmark BODY/canary CONTRACT decisions and independently rehash112RAW. Seven complete frozen leaves, one lower route. Shared affine_convex/proper/full affine_subdifferential produce regularity/support; actual energy_eq_sum/output_succ/eta_eq_energy produce trace; actual parent and source endpoints produce all4 performance branches; actual state_prefix produces full state equality. Zero cases instantiate actual parent, without canceling sqrt-energy or assuming zero supports at D0. Exact new Test context/header/BODY only; one focused success before downstream append, retain failures and BODY-only repairs. No full package acceptance.')
event('algorithm-canary-stabilized-event-v1','stabilized',dict(current_leaf='loss_regular',
    review_sha256=sha(review_path),allowed_window=window))
bodies={
'loss_regular': '''  have hf : loss t = fun y : ℝ => ((inner ℝ (feedback t) y + 0 : ℝ) : EReal) := by
    funext y
    change ((feedback t * y : ℝ) : EReal) = ((y * feedback t + 0 : ℝ) : EReal)
    congr 1
    ring
  rw [hf]
  refine ⟨affine_convex (feedback t) 0, ⟨affine_proper (feedback t) 0, ?_⟩, ?_⟩
  · intro z hz
    rw [affine_subdifferential]
    exact ⟨feedback t, rfl⟩
  · intro z
    rw [affine_subdifferential]
    rfl
''',
'feedback_energy': '''  have hg : ∀ α : ℝ, ∀ t : ℕ,
      selected V α 1 loss (1 / 2) policy t = feedback t := by
    intro α t
    rfl
  refine ⟨hg, ?_⟩
  intro α T hT
  unfold q
  rw [energy_eq_sum]
  simp_rw [hg]
  interval_cases T <;> norm_num [feedback, sum_range_succ, Real.norm_eq_abs]
''',
'trace_canary': '''  have hg := feedback_energy.1 1
  have he := feedback_energy.2 1
  have hr0 : r 1 0 = 0 := by
    rw [r, eta_eq_energy]
    change 1 * 1 / Real.sqrt (q 1 1) = 0
    rw [he 1 (by norm_num)]
    norm_num
  have hr1 : r 1 1 = 1 / 3 := by
    rw [r, eta_eq_energy]
    change 1 * 1 / Real.sqrt (q 1 2) = 1 / 3
    rw [he 2 (by norm_num)]
    norm_num
  have hr2 : r 1 2 = 1 / 3 := by
    rw [r, eta_eq_energy]
    change 1 * 1 / Real.sqrt (q 1 3) = 1 / 3
    rw [he 3 (by norm_num)]
    norm_num
  have hr3 : r 1 3 = 1 / 5 := by
    rw [r, eta_eq_energy]
    change 1 * 1 / Real.sqrt (q 1 4) = 1 / 5
    rw [he 4 (by norm_num)]
    norm_num
  have hx0 : x 1 0 = 1 / 2 := rfl
  have hx1 : x 1 1 = 1 / 2 := by
    change output V 1 1 loss (1 / 2) policy (0 + 1) = _
    rw [output_succ, hg]
    norm_num [feedback]
    exact hx0
  have hx2 : x 1 2 = 0 := by
    change output V 1 1 loss (1 / 2) policy (1 + 1) = _
    rw [output_succ, hg]
    norm_num only [feedback]
    change BanditRL.OnlineGradientDescent.project V (x 1 1 - r 1 1 * 3) = 0
    rw [hx1, hr1, V, BanditRL.OnlineGradientDescent.project_unitInterval]
    norm_num
  have hx3 : x 1 3 = 0 := by
    change output V 1 1 loss (1 / 2) policy (2 + 1) = _
    rw [output_succ, hg]
    norm_num [feedback]
    exact hx2
  have hx4 : x 1 4 = 4 / 5 := by
    change output V 1 1 loss (1 / 2) policy (3 + 1) = _
    rw [output_succ, hg]
    norm_num only [feedback]
    change BanditRL.OnlineGradientDescent.project V (x 1 3 - r 1 3 * (-4)) = 4 / 5
    rw [hx3, hr3, V, BanditRL.OnlineGradientDescent.project_unitInterval]
    norm_num
  refine ⟨hx0, hx1, hx2, hx3, hx4, hr0, hr1, hr2, hr3, ?_, ?_, ?_, ?_⟩
  · change ∑ t ∈ range 4, ((loss t (x 1 t)).toReal - (loss t 0).toReal) = 3 / 2
    norm_num [sum_range_succ, loss, feedback, hx0, hx1, hx2, hx3]
  · rw [hx4]
    norm_num [Real.norm_eq_abs]
  · rw [V, BanditRL.OnlineGradientDescent.project_unitInterval]
    norm_num
  · norm_num
''',
'performance_canary': '''  have hx₁ : (1 / 2 : ℝ) ∈ V.carrier := by
    norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]
  have hu : (0 : ℝ) ∈ V.carrier := by
    norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]
  have hdiam : ∀ a ∈ V.carrier, ∀ b ∈ V.carrier, ‖a - b‖ ≤ (1 : ℝ) := by
    intro a ha b hb
    change a ∈ Icc (0 : ℝ) 1 at ha
    change b ∈ Icc (0 : ℝ) 1 at hb
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hlegal (α : ℝ) : LegalFeedback V α 1 loss (1 / 2) policy 4 := by
    intro t ht
    change feedback t ∈ SourceSubdifferential (loss t) _
    exact (loss_regular V t).2.2 _
  have he (α : ℝ) : energy V α 1 loss (1 / 2) policy 4 = 25 := by
    simpa using feedback_energy.2 α 4 (by norm_num)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hn, _, _⟩ := trace_canary
  change ‖output V 1 1 loss (1 / 2) policy 4 - 0‖ ^ 2 = 16 / 25 at hn
  have hp := regret_bound V 1 1 (by norm_num) (by norm_num) loss (1 / 2) policy hx₁ 4
    (fun t ht => (loss_regular V t).2.1) (hlegal 1) hdiam 0 hu
  have hs := source_eq4_4 V 1 (by norm_num) loss (1 / 2) policy hx₁ 4
    (fun t ht => (loss_regular V t).1) (fun t ht => (loss_regular V t).2.1)
    (hlegal 1) hdiam 0 hu
  have hb := BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum V 1 (by norm_num)
    loss (1 / 2) policy hx₁ 4 (fun t ht => (loss_regular V t).1)
    (fun t ht => (loss_regular V t).2.1) (hlegal (Real.sqrt 2 / 2)) hdiam 0 hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [he, hn] using hp
  · simpa [he] using hs
  · simpa [he] using hb.1
  · simpa [he] using hb.2
''',
'prefix_canary': '''  refine ⟨state_prefix V 1 1 loss futureLoss (1 / 2) policy 2 ?_, ?_, ?_⟩
  · intro s hs
    funext z
    simp [futureLoss, hs]
  · intro h
    have hz := congrFun h 0
    norm_num [loss, feedback, futureLoss] at hz
  · funext z
    norm_num [futureLoss]
''',
'zero_energy_canary': '''  have ho : ∀ t : ℕ, output V 1 1 zeroLoss (1 / 2) zeroPolicy t = 1 / 2 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [output_succ]
      simpa [selected, zeroPolicy] using ih
  have he : ∀ T : ℕ, energy V 1 1 zeroLoss (1 / 2) zeroPolicy T = 0 := by
    intro T
    rw [energy_eq_sum]
    simp [selected, zeroPolicy]
  have hf : ∀ t : ℕ, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (zeroLoss t) := by
    intro t
    simpa [loss, feedback, zeroLoss] using (loss_regular V 0).2.1
  have hl : LegalFeedback V 1 1 zeroLoss (1 / 2) zeroPolicy 4 := by
    intro t ht
    change (0 : ℝ) ∈ SourceSubdifferential (zeroLoss t) _
    simpa [feedback, loss, zeroLoss] using (loss_regular V 0).2.2
      (output V 1 1 zeroLoss (1 / 2) zeroPolicy t)
  have hd : ∀ a ∈ V.carrier, ∀ b ∈ V.carrier, ‖a - b‖ ≤ (1 : ℝ) := by
    intro a ha b hb
    change a ∈ Icc (0 : ℝ) 1 at ha
    change b ∈ Icc (0 : ℝ) 1 at hb
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hp := regret_bound V 1 1 (by norm_num) (by norm_num) zeroLoss (1 / 2) zeroPolicy
    (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval]) 4 (fun t ht => hf t)
    hl hd 0 (by norm_num [V, BanditRL.OnlineGradientDescent.unitInterval])
  refine ⟨ho, he, ?_, ?_, ?_⟩
  · simp [regret, zeroLoss]
  · rw [ho]
    norm_num [Real.norm_eq_abs]
  · simpa [he] using hp
''',
'zero_diameter_canary': '''  have ho (t : ℕ) : output W 1 0 loss 0 policy t = 0 := by
    have hm := output_mem W 1 0 loss 0 policy (by simp [W]) t
    simpa [W] using hm
  have he : energy W 1 0 loss 0 policy 2 = 9 := by
    rw [energy_eq_sum]
    norm_num [selected, policy, feedback, sum_range_succ, Real.norm_eq_abs]
  have hl : LegalFeedback W 1 0 loss 0 policy 2 := by
    intro t ht
    change feedback t ∈ SourceSubdifferential (loss t) _
    exact (loss_regular W t).2.2 _
  have hd : ∀ a ∈ W.carrier, ∀ b ∈ W.carrier, ‖a - b‖ ≤ (0 : ℝ) := by
    intro a ha b hb
    have ha0 : a = 0 := by simpa [W] using ha
    have hb0 : b = 0 := by simpa [W] using hb
    simp [ha0, hb0]
  have hp := regret_bound W 1 0 (by norm_num) (by norm_num) loss 0 policy (by simp [W]) 2
    (fun t ht => (loss_regular W t).2.1) hl hd 0 (by simp [W])
  refine ⟨ho 2, he, ?_, ?_, ?_⟩
  · norm_num [selected, policy, feedback]
  · unfold regret
    simp_rw [ho]
    simp
  · simpa using hp
'''}
prefix=Path(window['context_path']).read_bytes()
end=b'end AdaptiveProbe\n'
completed=[]
for index,name in enumerate(n for group in window['ordered_groups'] for n in group):
    if public.exists():
        assert public.read_bytes()==prefix+end
    event('algorithm-canary-'+name+'-proving-event-v1','proving',dict(current_leaf=name,
        allowed_file=public.as_posix(),preceding_focused_successes=completed))
    addition=b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
    public.write_bytes(prefix+addition+end)
    assert statement_hash(lean_declaration_header(public,name))==headers[name]['normalized_statement_hash']
    write(RUN/('algorithm-canary-'+name+'-body-attempt-v1.lean.txt'),public.read_bytes())
    label='algorithm-canary-'+name+'-focused-build-v1'
    code,out=capture(label,'lake','build','Tests.OnlineAdaptiveOSDCanary',required=False)
    print(out if code else '\n'.join(out.splitlines()[-6:]),flush=True)
    if code:
        capture('algorithm-canary-'+name+'-failed-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
            'trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed',
            '--attempt-id','algorithm-canary-'+name+'-body-v1','--harness','hierarchical',
            '--obligations-before','7','--obligations-after',str(7-index),'--verifier-evidence',RUN/(label+'.json'),
            '--notes','Actual focused compiler failure and full snapshot retained; stop downstream append; exact frozen header/context unchanged; BODY-only repair.')
        sys.exit(code)
    assert 'Build completed successfully' in out
    write(RUN/('algorithm-canary-'+name+'-compiled-local-v1.json'),dict(
        production_sha256=sha(public),header=headers[name],focused_receipt_sha256=sha(RUN/(label+'.json')),
        boundary='Focused only; full public/axiom/VALUE/BODY review and combined package gates open.'))
    completed.append(dict(name=name,focused_receipt_sha256=sha(RUN/(label+'.json'))))
    prefix+=addition
print('All seven exact complete canary BODYs focused-compiled sequentially.',flush=True)
