import BanditRLProof.OnlineUnboundedOSD
#check BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
#print axioms BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
#check BanditRL.OnlineUnboundedOSD.step_affine_fullSpace
#print axioms BanditRL.OnlineUnboundedOSD.step_affine_fullSpace
#check BanditRL.OnlineUnboundedOSD.iterate_affine_prefix
#print axioms BanditRL.OnlineUnboundedOSD.iterate_affine_prefix
#check BanditRL.OnlineUnboundedOSD.powerSteps_pos
#print axioms BanditRL.OnlineUnboundedOSD.powerSteps_pos
#check BanditRL.OnlineUnboundedOSD.phi_limit
#print axioms BanditRL.OnlineUnboundedOSD.phi_limit
#check BanditRL.OnlineUnboundedOSD.switching_loss_regular
#print axioms BanditRL.OnlineUnboundedOSD.switching_loss_regular
#check BanditRL.OnlineUnboundedOSD.phi_range
#print axioms BanditRL.OnlineUnboundedOSD.phi_range
#check (BanditRL.OnlineUnboundedOSD.step_affine_fullSpace (2 : ℝ) (3 : ℝ) 5 7)
#check (BanditRL.OnlineUnboundedOSD.iterate_affine_prefix (fun t => ((t+1 : ℕ) : ℝ)) (fun t => ((t+2 : ℕ) : ℝ)) (fun _ => (7 : ℝ)) (3 : ℝ) 4)
#check (BanditRL.OnlineUnboundedOSD.powerSteps_pos (1/2 : ℝ) 3)
#check (BanditRL.OnlineUnboundedOSD.switching_loss_regular 4 (1 : ℝ) (by norm_num) 3)
#check (BanditRL.OnlineUnboundedOSD.phi_range (1/2 : ℝ) (by norm_num) (by norm_num))
