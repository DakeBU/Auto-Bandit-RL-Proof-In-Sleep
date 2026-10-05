import BanditRLProof
import Tests.OnlineGuessingOGDCanary
import Tests.OnlineGuessingLowerCanary
import Tests.OnlineGuessingComparisonCanary

#check @BanditRL.OnlineGradientDescent.project_unitInterval
#print axioms BanditRL.OnlineGradientDescent.project_unitInterval
#check @BanditRL.OnlineGradientDescent.square_regular
#print axioms BanditRL.OnlineGradientDescent.square_regular
#check @BanditRL.OnlineGradientDescent.gradient_square
#print axioms BanditRL.OnlineGradientDescent.gradient_square
#check @BanditRL.OnlineGradientDescent.gradient_square_bound
#print axioms BanditRL.OnlineGradientDescent.gradient_square_bound
#check @BanditRL.OnlineGradientDescent.square_step_clamp
#print axioms BanditRL.OnlineGradientDescent.square_step_clamp
#check @BanditRL.OnlineGradientDescent.example_2_14
#print axioms BanditRL.OnlineGradientDescent.example_2_14
#check @BanditRL.OnlineGradientDescent.guessing_zero_trajectory
#print axioms BanditRL.OnlineGradientDescent.guessing_zero_trajectory
#check @BanditRL.OnlineGradientDescent.guessing_tuned_eta_square
#print axioms BanditRL.OnlineGradientDescent.guessing_tuned_eta_square
#check @BanditRL.OnlineGradientDescent.guessing_squared_horizon_lower
#print axioms BanditRL.OnlineGradientDescent.guessing_squared_horizon_lower
#check @BanditRL.OnlineGradientDescent.meanPredict_zero_cumulativeLoss
#print axioms BanditRL.OnlineGradientDescent.meanPredict_zero_cumulativeLoss
#check @BanditRL.OnlineGradientDescent.guessing_vs_mean_lower
#print axioms BanditRL.OnlineGradientDescent.guessing_vs_mean_lower
#check @BanditRL.OnlineGradientDescent.guessing_vs_mean_unbounded
#print axioms BanditRL.OnlineGradientDescent.guessing_vs_mean_unbounded
#check @BanditRL.OnlineGradientDescent.unitInterval
#print axioms BanditRL.OnlineGradientDescent.unitInterval
#check @Tests.OnlineGuessingOGD.labels
#print axioms Tests.OnlineGuessingOGD.labels
#check @Tests.OnlineGuessingOGD.losses
#print axioms Tests.OnlineGuessingOGD.losses
#check @Tests.OnlineGuessingOGD.first_projected
#print axioms Tests.OnlineGuessingOGD.first_projected
#check @Tests.OnlineGuessingOGD.second_projected
#print axioms Tests.OnlineGuessingOGD.second_projected
#check @Tests.OnlineGuessingOGD.source_four_rounds
#print axioms Tests.OnlineGuessingOGD.source_four_rounds
#check @Tests.OnlineGuessingLower.first_state
#print axioms Tests.OnlineGuessingLower.first_state
#check @Tests.OnlineGuessingLower.source_lower
#print axioms Tests.OnlineGuessingLower.source_lower
#check @Tests.OnlineGuessingComparison.actual_zero_stream_gap
#print axioms Tests.OnlineGuessingComparison.actual_zero_stream_gap
