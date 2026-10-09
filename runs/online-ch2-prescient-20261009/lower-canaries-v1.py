from common import *
fixed()
review=RUN/'canary-CONTRACT-review-v1.json'
assert sha(review)=='e355d1444e1cba3b5c90f8688625a083adffbac4ff78f8574542dc34ea03e519'
r=load(review);assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
for row in load(RUN/'canary-CONTRACT-review-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
c=load(CONTRACT/'canary-targets-draft-v1.json');targets=c['targets']
write(CONTRACT/'canary-stabilized-v1.json',dict(stage='stabilized exact5headers and3concrete definitions',review_sha256=sha(review),draft_sha256=sha(CONTRACT/'canary-targets-draft-v1.json'),context_sha256=sha(RUN/'neutral-canary-types-v1.txt'),targets=targets,allowed_file=(ROOT/'Tests/OnlinePrescientLinearCanary.lean').as_posix(),allowed_helpers='Only explicit necessary local scalar projection/arithmetic helpers, no root/readers/other Tests changes',compiled=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
context=(RUN/'neutral-canary-types-v1.txt').read_text(encoding='utf8').split('Proposed type-only canaries')[0]
helpers='''-- Explicit scalar instances of the existing selected-projection characterization.
private theorem interval_project_neg_two :
    BanditRL.OnlineGradientDescent.project interval (-2) = -1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval (-2) (-1)
    (by norm_num [interval])
  intro w hw
  change -1 ≤ w ∧ w ≤ 1 at hw
  simp only [real_inner_eq_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith only [hw.1])

private theorem interval_project_mem (z : ℝ) (hz : z ∈ interval.carrier) :
    BanditRL.OnlineGradientDescent.project interval z = z := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval z z hz
  intro w hw
  simp

private theorem interval_project_three :
    BanditRL.OnlineGradientDescent.project interval 3 = 1 := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational interval 3 1
    (by norm_num [interval])
  intro w hw
  change -1 ≤ w ∧ w ≤ 1 at hw
  simp only [real_inner_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith only [hw.2])

private theorem whole_project (z : ℝ) :
    BanditRL.OnlineGradientDescent.project whole z = z := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational whole z z (by trivial)
  intro w hw
  simp

private theorem interval_states :
    iterate interval (1 / 2) signals 1 1 = -1 ∧
    iterate interval (1 / 2) signals 1 2 = -(1 / 2) := by
  have h1 : iterate interval (1 / 2) signals 1 1 = -1 := by
    change BanditRL.OnlineGradientDescent.project interval
      ((1 : ℝ) - (1 / 2) * signals 0) = -1
    norm_num [signals]
    exact interval_project_neg_two
  refine ⟨h1, ?_⟩
  rw [iterate, h1]
  change BanditRL.OnlineGradientDescent.project interval
    ((-1 : ℝ) - (1 / 2) * signals 1) = -(1 / 2)
  norm_num [signals]
  exact interval_project_mem _ (by norm_num [interval])

private theorem whole_states :
    iterate whole (1 / 2) signals 1 1 = -2 ∧
    iterate whole (1 / 2) signals 1 2 = -(3 / 2) := by
  have h1 : iterate whole (1 / 2) signals 1 1 = -2 := by
    change BanditRL.OnlineGradientDescent.project whole
      ((1 : ℝ) - (1 / 2) * signals 0) = -2
    rw [whole_project]
    norm_num [signals]
  refine ⟨h1, ?_⟩
  rw [iterate, h1]
  change BanditRL.OnlineGradientDescent.project whole
    ((-2 : ℝ) - (1 / 2) * signals 1) = -(3 / 2)
  rw [whole_project]
  norm_num [signals]

'''
bodies=[
'''  rcases interval_states with ⟨h1, h2⟩
  norm_num [prediction, regret, sum_range_succ, h1, h2, iterate,
    signals, real_inner_eq_mul, Real.norm_eq_abs]
''',
'''  refine ⟨fun t x => BanditRL.OnlineGradientDescent.Source.gradient_linear (signals t) x, ?_⟩
  rcases interval_states with ⟨h1, h2⟩
  norm_num [regret, prediction, sum_range_succ, h1, h2, iterate,
    signals, real_inner_eq_mul, Real.norm_eq_abs]
''',
'''  rcases whole_states with ⟨h1, h2⟩
  norm_num [prediction, regret, sum_range_succ, h1, h2, iterate,
    signals, real_inner_eq_mul, Real.norm_eq_abs]
''',
'''  have hp : prediction interval (1 / 2) signals 1 0 = -1 := interval_states.1
  have hz : prediction interval (1 / 2) (fun _ => 0) 1 0 = 1 := by
    change BanditRL.OnlineGradientDescent.project interval ((1 : ℝ) - (1 / 2) * 0) = 1
    norm_num
    exact interval_project_mem _ (by norm_num [interval])
  refine ⟨by rw [hp, hz]; norm_num, ?_⟩
  intro h hh
  rw [prediction_prefix interval (1 / 2) h signals 1 0 (by
    intro s hs
    have : s = 0 := by omega
    subst s
    simpa only [signals, if_pos rfl] using hh)]
  exact hp
''',
'''  have hp : prediction interval 1 (fun _ => 0) 3 0 = 1 := by
    change BanditRL.OnlineGradientDescent.project interval ((3 : ℝ) - 1 * 0) = 1
    norm_num
    exact interval_project_three
  refine ⟨by norm_num [interval], hp, ?_, ?_, ?_⟩
  · norm_num [hp, iterate]
  · simp [regret]
  · intro u hu
    exact regret_sharp_bound interval 1 (by norm_num) (fun _ => 0) 3 u 0 hu
''']
text=context+helpers
for t,b in zip(targets,bodies):text+=t['exact_proposed_header']+' := by\n'+b+'\n'
text+='end Tests.OnlinePrescientLinear\n'
test=ROOT/'Tests/OnlinePrescientLinearCanary.lean';write(test,text)
write(RUN/'canary-lower-plan-v1.json',dict(stage='proving exact5headers',file=test.as_posix(),frozen_contract_sha256=sha(CONTRACT/'canary-stabilized-v1.json'),production_sha256=sha(PUBLIC),helpers=['interval_project_neg_two','interval_project_mem','interval_project_three','whole_project','interval_states','whole_states'],retrieval='Existing OnlineGradientDescent.project_eq_of_variational reused; OnlineGuessingOGD scalar-clipping route and OnlineHuber full-space identity inspected. Helpers are concrete private Test arithmetic, not new generic/source terminals.',required_producer_calls=['actual project definition through advance/iterate','prediction_prefix in current_and_future_information','regret_sharp_bound at outside_initial_center_and_empty_horizon','Source.gradient_linear in constrained_gradient_sign_counterexample'],roots_readers_edited=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
code,out=capture('canaries-focused-build-v1','lake','build','Tests.OnlinePrescientLinearCanary',required=False)
print(out[-12000:]);print('Actual canary compiler',code)
