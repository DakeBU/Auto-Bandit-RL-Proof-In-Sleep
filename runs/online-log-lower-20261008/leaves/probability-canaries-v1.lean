import BanditRLProof.OnlineGuessingLogLower
open BanditRL.OnlineLearning.GuessingLower Set
example : polyaNext [] = (1 : ℝ) / 2 := by norm_num [polyaNext]
example : polyaNext [true] = (2 : ℝ) / 3 := by norm_num [polyaNext]
example : polyaNext [false] = (1 : ℝ) / 3 := by norm_num [polyaNext]
example (h : List Bool) : 0 < polyaNext h ∧ polyaNext h < 1 := probability_mem h
#check BanditRL.OnlineLearning.GuessingLower.probability_mem
#print axioms BanditRL.OnlineLearning.GuessingLower.probability_mem
