from common_v1 import *
fixed()
pub = (CONTRACT/'public-context-v1.lean').read_text(encoding='utf8')
neutral = (CONTRACT/'neutral-context-v1.lean').read_text(encoding='utf8')
text = pub+'\n'+neutral.replace('import Mathlib\n','')+'\n'
text += '''open BanditRL.OnlineLearning NeutralLimit
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) :
    C0 μ Y T = expectedFixedMinimum μ Y T := rfl
example {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y P : ℕ → Ω → ℝ) (T : ℕ) : C1 μ Y P T = expectedFixedRegret μ Y P T := rfl
example (y : ℕ → ℝ) (t : ℕ) : C2 y t = meanPredict y t := rfl
'''
text += '\n'.join('example : S00'+str(i)+' = Q00'+str(i)+' := rfl' for i in range(1,5))+'\n'
write(RUN/'neutral-identities-v1.lean',text)
gate('neutral-identities-v1','lake','env','lean',RUN/'neutral-identities-v1.lean')
write(RUN/'neutral-identity-receipt-v1.json',dict(
    neutral_whole_prop_identities=4,definition_identities=3,actual_exit=0,
    semantic_target_proofs=0,interpretation='definitional identity only; not theorem proofs',
    public_context_sha256=sha(CONTRACT/'public-context-v1.lean'),
    neutral_context_sha256=sha(CONTRACT/'neutral-context-v1.lean')))
fixed()
