import BanditRLProof.OnlineGuessingKernelCausal
open scoped ENNReal
#check ENNReal.add_div
#check ENNReal.div_self
example : (4 / 4 : ℝ≥0∞) = 1 := ENNReal.div_self (by norm_num) (by norm_num)
