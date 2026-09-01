import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoNthPull

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory

#check twoArmPrefixGeneratedAction
#check twoArmPrefixOptimalPullCount
#check twoArmInclusiveOptimalPullCountProcess
#check twoArmNthOptimalPullTime
#check isStoppingTime_twoArmNthOptimalPullTime
#check measurable_twoArmNthOptimalPullTime
#check twoArmNthOptimalPullTime_eq_top_iff
#check twoArmOptimalPullCount_lt_succ_of_nthOptimalPullTime_eq_top
#check twoArmOptimalPullCount_lt_of_fin_nthOptimalPullTime_eq_top
#check twoArmNthOptimalPullTime_spec
#check twoArmNthOptimalPullReward
#check measurable_twoArmNthOptimalPullReward
#check twoArmNthOptimalPullSuccessProbability
#check measurable_twoArmNthOptimalPullSuccessProbability

/-- A finite first-pull time is a genuine chronological arm-`0` selection and
the inclusive count advances from zero to one. -/
example
    (t : Nat)
    (sample : Unit × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime 0 sample = (t : WithTop Nat)) :
    twoArmOptimalPullCount t sample = 0 /\
      twoArmGeneratedAction sample t = 0 /\
      twoArmOptimalPullCount (t + 1) sample = 1 := by
  simpa using twoArmNthOptimalPullTime_spec 0 t sample htime

/-- The zero-based index is not shifted: index one is the second arm-`0`
selection, with one earlier optimal pull and two inclusive pulls. -/
example
    (t : Nat)
    (sample : Unit × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime 1 sample = (t : WithTop Nat)) :
    twoArmOptimalPullCount t sample = 1 /\
      twoArmGeneratedAction sample t = 0 /\
      twoArmOptimalPullCount (t + 1) sample = 2 := by
  simpa using twoArmNthOptimalPullTime_spec 1 t sample htime

/-- A trace that always selects arm `1` exposes the explicit missing first
optimal pull as `top`; no arbitrary finite default is substituted. -/
example :
    twoArmNthOptimalPullTime 0
        ((), fun _ : Nat => ((1 : Fin 2), (0 : Real))) =
      (⊤ : WithTop Nat) := by
  rw [twoArmNthOptimalPullTime_eq_top_iff]
  intro chron
  have hzero :
      twoArmOptimalPullCount (chron + 1)
          ((), fun _ : Nat => ((1 : Fin 2), (0 : Real))) = 0 := by
    apply pullCount_eq_zero_of_forall_ne
    intro s hs
    simp [twoArmGeneratedAction]
  omega

/-- The extracted reward and post-pull probability use the same finite
chronological coordinate; no selected-IID premise is introduced. -/
example
    (eta : Real) (pullIndex t : Nat)
    (sample : Unit × ((k : Nat) -> Fin 2 × Real))
    (htime :
      twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmNthOptimalPullReward pullIndex sample = (sample.2 t).2 /\
      twoArmNthOptimalPullSuccessProbability eta pullIndex sample =
        twoArmSuccessProbability eta t sample := by
  exact
    ⟨twoArmNthOptimalPullReward_eq_of_time_eq
        pullIndex t sample htime,
      twoArmNthOptimalPullSuccessProbability_eq_of_time_eq
        eta pullIndex t sample htime⟩

#print axioms twoArmNthOptimalPullTime_spec
#print axioms twoArmOptimalPullCount_lt_of_fin_nthOptimalPullTime_eq_top
#print axioms measurable_twoArmNthOptimalPullReward
#print axioms measurable_twoArmNthOptimalPullSuccessProbability

end StochasticGradientBandit
end BanditRLProof
