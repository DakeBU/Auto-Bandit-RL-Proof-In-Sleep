from common_v1 import *
write(RUN/'exact-bindings-repair-v2.json',dict(
    prior_exit=load(RUN/'all-exact-types-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'all-exact-types-v1.log'),
    cause='Separately defined recursive path functions are extensionally equal but not definitionally identical; nominally distinct distribution structures require fieldwise propositional equivalence.',
    correction='Prove recursive function equality by actual list induction, lift to finite expectation/measure functions, and prove the distribution predicates equal with propext and both actual record fields. Check all64 closed propositions under those proved equality transports.',
    source_or_frozen_target_or_neutral_input_changed=False,
    old_failed_rfl_check_preserved=True))
index=load(RUN/'full-neutral-map-v2.json')
identity='import Tests.OnlineGuessingLogLowerCanary\n'+(RUN/'full-neutral-packet-v2.lean').read_text(encoding='utf-8')
identity+='''
namespace NeutralContext
theorem f2_eq_point (h : List Bool) : f2 h = BanditRL.OnlineLearning.GuessingLower.pathWeight h := by
  induction h with
  | nil => rfl
  | cons b h ih =>
    change f2 h * (if b then f1 h else 1-f1 h) =
      BanditRL.OnlineLearning.GuessingLower.pathWeight h *
        (if b then BanditRL.OnlineLearning.GuessingLower.polyaNext h
          else 1-BanditRL.OnlineLearning.GuessingLower.polyaNext h)
    rw [ih]
    rfl
theorem f2_eq : f2 = BanditRL.OnlineLearning.GuessingLower.pathWeight := funext f2_eq_point
theorem f7_eq : f7 = BanditRL.OnlineLearning.GuessingLower.pathExpectation := by
  simp only [f7, BanditRL.OnlineLearning.GuessingLower.pathExpectation, f2_eq]
theorem f8_eq : @f8 = @BanditRL.OnlineLearning.GuessingLower.prefixMeasure := by
  simp only [f8, BanditRL.OnlineLearning.GuessingLower.prefixMeasure, f2_eq]
  rfl
theorem P_eq {X : Type*} (arms : Finset X) (p : X → ℝ) :
    P arms p = BanditRLProof.Exp3.FiniteActionDistribution arms p := by
  apply propext
  constructor
  · intro h
    exact ⟨h.nonneg,h.sum_eq_one⟩
  · intro h
    exact ⟨h.nonneg,h.sum_eq_one⟩
end NeutralContext
universe u
def propositionOf {P : Prop} (_ : P) : Prop := P
'''
for row in index:
    suffix='.{u}' if row['polymorphic'] else ''
    identity+='example : NeutralContext.'+row['id']+suffix+' = propositionOf (@'+row['name']+suffix+') := by\n'
    identity+='  unfold NeutralContext.'+row['id']+' propositionOf\n'
    identity+='  simp only [NeutralContext.f2_eq, NeutralContext.f7_eq, NeutralContext.f8_eq, NeutralContext.P_eq] <;> rfl\n'
pubdefs=['polyaNext','pathWeight','binaryStream','binaryValues','causalPredict','pathRegret','pathExpectation','prefixMeasure','pathLearnerLoss','pathBestLoss']
for i,n in enumerate(pubdefs+['coinMeasure','seededPolicy'],1):
    identity+='example : @NeutralContext.f'+str(i)+' = @'+(PRE if i<=10 else 'GuessingLogLowerProbe.')+n+' := by '
    identity+=('exact NeutralContext.f'+str(i)+'_eq\n') if i in [2,7,8] else 'rfl\n'
write(RUN/'leaves/all-exact-types-v2.lean',identity)
gate('all-exact-types-v2','lake','env','lean',RUN/'leaves/all-exact-types-v2.lean')
print('Actual64 closed proposition equalities and12 definition equalities verified with explicit nominal/recursive bridges.')
