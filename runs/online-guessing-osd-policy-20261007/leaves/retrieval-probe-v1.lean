import BanditRLProof.OnlineGuessingSubgradient
import BanditRLProof.OnlineSubgradientPolicy
set_option pp.universes true
#check @BanditRL.OnlineGuessingSubgradient.loss
#check @BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound
#check @BanditRL.OnlineGuessingSubgradient.loss_on_unitInterval
#check @BanditRL.OnlineSubgradientPolicy.output_succ
#check @BanditRL.OnlineSubgradientPolicy.regret_tuned
#check @BanditRL.OnlineSubgradientPolicy.regret_fixed
#check @BanditRL.OnlineSubgradientPolicy.canonical_output
#check @BanditRL.OnlineGradientDescent.project_unitInterval
#check @Real.tendsto_sqrt_atTop
#check @tendsto_inv_atTop_zero
