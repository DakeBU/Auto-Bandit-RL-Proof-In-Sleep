from append_leaf_v1 import *
assert load(RUN/'D1-attempt-v1.json')['actual_build_exit']==0
helpers='''private theorem dyadicObservation_binary (t : ℕ) :
    dyadicObservation t = 0 ∨ dyadicObservation t = 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simp [dyadicObservation]
    | succ n =>
      have hparent : n / 2 < n + 1 := by omega
      rcases ih (n / 2) hparent with hzero | hone
      · rw [dyadicObservation, hzero]
        norm_num
      · rw [dyadicObservation, hone]
        norm_num
'''
body=''' := by
  intro t
  rcases dyadicObservation_binary t with hzero | hone
  · simp [hzero]
  · simp [hone]
'''
append_leaf(1,body,helpers)
