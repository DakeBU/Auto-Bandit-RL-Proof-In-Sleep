import BanditRLProof.Algorithms.CUCBFiniteDeterministicExample

/-! Full finite source-model witnesses: noise, multiple nonsingleton actions,
actual approximation oracle and all frozen performance/boundary cases. -/
namespace Tests.CUCBFiniteModelCanary
open BanditRLProof.CUCB.FiniteExample

example (i : Fin 3) : 0<(law i {bit true}).toReal ∧ (law i {bit true}).toReal<1 := noisy_each_arm i
example (a : Bool) : (selected a).card=2 := selected_size a
example : source.approximationRegret 1=1/4 := regret_one_positive
example (H : ℕ) : noBadSource.approximationRegret H≤0 := no_bad_regret H

#print axioms model
#print axioms source
#print axioms randomizedSource
#print axioms fullSource
#print axioms noisy_each_arm
#print axioms observation_compatible
#print axioms regret_one_positive
#print axioms refined_regret
#print axioms probabilistic_regret
#print axioms randomized_probabilistic_regret
#print axioms randomized_action_mass
#print axioms deterministic_regret
#print axioms no_bad_regret
end Tests.CUCBFiniteModelCanary
