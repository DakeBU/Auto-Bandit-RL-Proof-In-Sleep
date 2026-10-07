from common_v1 import *
write(RUN/'exact-bindings-repair-v3.json',dict(
    prior_exit=load(RUN/'all-exact-types-v2-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'all-exact-types-v2.log'),
    cause='simp-only reports no progress for already definitionally equal cases and unapplied higher-order expectation/measure functions.',
    correction='Apply function extensionality before the recursive equality rewrite; use rfl first for unchanged nominal-free propositions and equality transport where needed.',
    source_or_frozen_target_or_neutral_input_changed=False))
text=(RUN/'leaves/all-exact-types-v2.lean').read_text(encoding='utf-8')
old='''  simp only [f7, BanditRL.OnlineLearning.GuessingLower.pathExpectation, f2_eq]'''
new='''  funext T f
  unfold f7 BanditRL.OnlineLearning.GuessingLower.pathExpectation
  rw [f2_eq]'''
assert text.count(old)==1;text=text.replace(old,new)
old='''  simp only [f8, BanditRL.OnlineLearning.GuessingLower.prefixMeasure, f2_eq]
  rfl'''
new='''  funext T inst
  unfold f8 BanditRL.OnlineLearning.GuessingLower.prefixMeasure
  rw [f2_eq]
  rfl'''
assert text.count(old)==1;text=text.replace(old,new)
old='  simp only [NeutralContext.f2_eq, NeutralContext.f7_eq, NeutralContext.f8_eq, NeutralContext.P_eq] <;> rfl'
new='''  first
  | rfl
  | simp only [NeutralContext.f2_eq, NeutralContext.f7_eq, NeutralContext.f8_eq, NeutralContext.P_eq] <;> rfl'''
assert text.count(old)==64;text=text.replace(old,new)
write(RUN/'leaves/all-exact-types-v3.lean',text)
gate('all-exact-types-v3','lake','env','lean',RUN/'leaves/all-exact-types-v3.lean')
