import BanditRLProof

namespace Tests.OnlineGuessingLower
open BanditRL.OnlineGradientDescent
lemma first_state : iterate unitInterval (1/16) (fun _ x => (x-0)^2) 1 1 = 7/8 := by
  have h := guessing_zero_trajectory 4 (by omega) 1
  norm_num at h ⊢
  exact h
lemma source_lower : 1 ≤ regret unitInterval (1/16) (fun _ x => (x-0)^2) 1 0 64 := by
  have h := guessing_squared_horizon_lower 4 (by omega)
  norm_num at h
  simpa only [sub_zero] using h
#print axioms first_state
#print axioms source_lower
end Tests.OnlineGuessingLower

#print axioms BanditRL.OnlineGradientDescent.guessing_zero_trajectory
#print axioms BanditRL.OnlineGradientDescent.guessing_tuned_eta_square
#print axioms BanditRL.OnlineGradientDescent.guessing_squared_horizon_lower
