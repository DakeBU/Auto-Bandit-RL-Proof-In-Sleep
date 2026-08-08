import BanditRLProof.TsallisFiniteArmIIDHistoryAdaptiveRefinedCorruptedRewardLaw

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A concrete corruption process that leaves the best arm unchanged and adds
the same nonnegative reward boost to every other arm at every round. -/
noncomputable def uniformSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (epsilon : Real)
    (hepsilon : 0 <= epsilon) :
    FiniteArmIIDHistoryAdaptiveRewardShiftSource K where
  initial arm := if arm = model.bestArm then 0 else epsilon
  successor _ _ arm := if arm = model.bestArm then 0 else epsilon
  measurable_successor _ :=
    (measurable_of_countable
      (fun arm : Fin K => if arm = model.bestArm then 0 else epsilon)).comp
        measurable_snd
  envelope _ arm := if arm = model.bestArm then 0 else epsilon
  envelope_nonneg _ arm := by
    split_ifs <;> positivity
  initial_abs_le arm := by
    split_ifs <;> simp [abs_of_nonneg hepsilon]
  successor_abs_le _ _ arm := by
    split_ifs <;> simp [abs_of_nonneg hepsilon]

/-- The uniform suboptimal-arm boost has the exact deterministic envelope
budget `(T+1) * (# suboptimal arms) * epsilon`. -/
theorem finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_uniformSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (epsilon : Real) (hepsilon : 0 <= epsilon) :
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget model horizon
        (uniformSuboptimalRewardBoostSource model epsilon hepsilon) =
      (((horizon + 1 : Nat) : Real)) *
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          epsilon := by
  rw [finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_eq]
  simp only [uniformSuboptimalRewardBoostSource]
  simp only [if_true, add_zero]
  have hinner :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => if arm = model.bestArm then 0 else epsilon) =
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          epsilon := by
    calc
      _ = ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun _ => epsilon) := by
            apply Finset.sum_congr rfl
            intro arm harm
            rw [if_neg (Finset.ne_of_mem_erase harm)]
      _ = _ := by simp
  calc
    (Finset.range (horizon + 1)).sum (fun _ =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => if arm = model.bestArm then 0 else epsilon)) =
      (Finset.range (horizon + 1)).sum (fun _ =>
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          epsilon) := by
        apply Finset.sum_congr rfl
        intro _ _
        exact hinner
    _ = (((horizon + 1 : Nat) : Real)) *
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          epsilon := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

/-- The explicit scalar regime in which the coefficient-aware refined theorem
is used for the uniform suboptimal-arm boost. -/
noncomputable def finiteArmIIDUniformSuboptimalBoostRefinedRegime
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (epsilon : Real) : Prop :=
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  25 * reciprocalGap ^ 2 <= armCount * horizonMass ∧
    epsilon * reciprocalGap <= 1 ∧
      25 * reciprocalGap *
          (Real.log
            ((2 * armCount * horizonMass) /
              (25 * reciprocalGap ^ 2)) + 2) <=
        horizonMass * armCount * epsilon

/-- Natural scalar conditions for the uniform suboptimal-arm boost imply the
coefficient-aware refined corruption window. -/
theorem finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_uniformSuboptimalRewardBoostSource
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (hhorizon :
      25 *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real))) ^ 2 <=
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          (((horizon + 1 : Nat) : Real)))
    (hepsilonGap :
      epsilon *
          ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real)) <= 1)
    (hcorruptionLower :
      25 *
          ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real)) *
          (Real.log
            ((2 *
                (((Finset.univ : Finset (Fin K)).erase
                  model.bestArm).card : Real) *
                (((horizon + 1 : Nat) : Real))) /
              (25 *
                (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
                  (fun arm =>
                    1 / ((model.gap arm : Rat) : Real))) ^ 2)) + 2) <=
        (((horizon + 1 : Nat) : Real)) *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
            epsilon) :
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow model horizon
      (uniformSuboptimalRewardBoostSource model epsilon hepsilon) := by
  rw [finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_uniformSuboptimalRewardBoostSource]
  refine ⟨hhorizon, ?_, hcorruptionLower⟩
  have hhorizonMass : 0 <= (((horizon + 1 : Nat) : Real)) := by positivity
  have harmCount :
      0 <= (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) := by
    positivity
  calc
    ((((horizon + 1 : Nat) : Real)) *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          epsilon) *
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real)) =
      ((((horizon + 1 : Nat) : Real)) *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real)) *
        (epsilon *
          ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real))) := by ring
    _ <= ((((horizon + 1 : Nat) : Real)) *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real)) *
        1 := mul_le_mul_of_nonneg_left hepsilonGap
          (mul_nonneg hhorizonMass harmCount)
    _ = (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
        (((horizon + 1 : Nat) : Real)) := by ring

/-- The named uniform-boost refined regime supplies the model-facing compact
corruption window without exposing its three clauses separately. -/
theorem finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_uniformSuboptimalRewardBoostSource_of_refinedRegime
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (hregime : finiteArmIIDUniformSuboptimalBoostRefinedRegime
      model horizon epsilon) :
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow model horizon
      (uniformSuboptimalRewardBoostSource model epsilon hepsilon) := by
  rcases hregime with ⟨hhorizon, hepsilonGap, hcorruptionLower⟩
  exact
    finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_uniformSuboptimalRewardBoostSource
      model horizon epsilon hepsilon hhorizon hepsilonGap hcorruptionLower

/-- A total explicit bound: use the refined square-root branch inside its
coefficient-aware window and the logarithmic additive-budget branch everywhere
else. In particular, the fallback covers zero and small corruption. -/
noncomputable def finiteArmIIDUniformSuboptimalBoostAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (epsilon : Real) : Real := by
  classical
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let armCount : Real := (actions.card : Real)
  let horizonMass : Real := ((horizon + 1 : Nat) : Real)
  let reciprocalGap := actions.sum
    (fun arm => 1 / ((model.gap arm : Rat) : Real))
  let scale := 2 * armCount * horizonMass
  let corruption := horizonMass * armCount * epsilon
  exact if finiteArmIIDUniformSuboptimalBoostRefinedRegime model horizon epsilon then
    1 + Real.log horizonMass +
      10 * Real.sqrt (corruption * reciprocalGap) *
        (2 + Real.sqrt
          (Real.log (scale / (corruption * reciprocalGap)) + 1))
  else
    (1 + Real.log horizonMass) * (1 + 25 * reciprocalGap) + corruption

/-- Refined local regret for the concrete corruption process that uniformly
boosts every suboptimal arm by `epsilon` at every round. The corruption budget
is exposed explicitly rather than through the abstract source envelope. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDUniformSuboptimalBoostRewardLawRegret_le_refinedLocalExplicit
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat)
    (hhorizon :
      25 *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real))) ^ 2 <=
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
          (((horizon + 1 : Nat) : Real)))
    (hepsilonGap :
      epsilon *
          ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real)) <= 1)
    (hcorruptionLower :
      25 *
          ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
            (fun arm => 1 / ((model.gap arm : Rat) : Real)) *
          (Real.log
            ((2 *
                (((Finset.univ : Finset (Fin K)).erase
                  model.bestArm).card : Real) *
                (((horizon + 1 : Nat) : Real))) /
              (25 *
                (((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
                  (fun arm =>
                    1 / ((model.gap arm : Rat) : Real))) ^ 2)) + 2) <=
        (((horizon + 1 : Nat) : Real)) *
          (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
            epsilon) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let source := uniformSuboptimalRewardBoostSource model epsilon hepsilon
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    let reciprocalGap :=
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
        (fun arm => 1 / ((model.gap arm : Rat) : Real))
    let horizonMass : Real := ((horizon + 1 : Nat) : Real)
    let armCount : Real :=
      (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real)
    let scale := 2 * armCount * horizonMass
    let corruption := horizonMass * armCount * epsilon
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      1 + Real.log horizonMass +
        10 * Real.sqrt (corruption * reciprocalGap) *
          (2 + Real.sqrt
            (Real.log (scale / (corruption * reciprocalGap)) + 1)) := by
  let source := uniformSuboptimalRewardBoostSource model epsilon hepsilon
  have hwindow : finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow
      model horizon source := by
    simpa only [source] using
      finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow_uniformSuboptimalRewardBoostSource
        model horizon epsilon hepsilon hhorizon hepsilonGap hcorruptionLower
  have hroute :=
    integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_refinedLocalExplicit_of_window
      model armLaw hprob hbound hmean source hsuboptimal hgapPos hgapLeOne
        horizon hwindow
  simpa only [source,
    finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_uniformSuboptimalRewardBoostSource]
    using hroute

/-- Uniform suboptimal-arm boost regret for every nonnegative `epsilon` and
finite horizon. The theorem selects the refined local branch when its named
regime holds and otherwise falls back to the compiled logarithmic theorem. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDUniformSuboptimalBoostRewardLawRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (hsuboptimal :
      ((Finset.univ : Finset (Fin K)).erase model.bestArm).Nonempty)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let source := uniformSuboptimalRewardBoostSource model epsilon hepsilon
    let law := finiteArmIIDRewardVectorLaw armLaw
    let loss := finiteArmIIDHistoryAdaptiveCorruptedRewardLoss source
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      finiteArmIIDUniformSuboptimalBoostAllRegimeBound
        model horizon epsilon := by
  classical
  let source := uniformSuboptimalRewardBoostSource model epsilon hepsilon
  by_cases hregime : finiteArmIIDUniformSuboptimalBoostRefinedRegime
      model horizon epsilon
  · have hclauses :
        let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
        let armCount : Real := (actions.card : Real)
        let horizonMass : Real := ((horizon + 1 : Nat) : Real)
        let reciprocalGap := actions.sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))
        25 * reciprocalGap ^ 2 <= armCount * horizonMass ∧
          epsilon * reciprocalGap <= 1 ∧
            25 * reciprocalGap *
                (Real.log
                  ((2 * armCount * horizonMass) /
                    (25 * reciprocalGap ^ 2)) + 2) <=
              horizonMass * armCount * epsilon := by
        simpa only [finiteArmIIDUniformSuboptimalBoostRefinedRegime] using hregime
    rcases hclauses with ⟨hhorizon, hepsilonGap, hcorruptionLower⟩
    have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDUniformSuboptimalBoostRewardLawRegret_le_refinedLocalExplicit
        model armLaw hprob hbound hmean epsilon hepsilon hsuboptimal hgapPos
          hgapLeOne horizon hhorizon hepsilonGap hcorruptionLower
    simpa only [source, finiteArmIIDUniformSuboptimalBoostAllRegimeBound,
      hregime, if_pos] using hroute
  · have hroute :=
      integral_sampledScheduledHalfTsallisFiniteArmIIDHistoryAdaptiveCorruptedRewardLawRegret_le_log
        model armLaw hprob hbound hmean source hgapPos horizon
    simpa only [source, finiteArmIIDUniformSuboptimalBoostAllRegimeBound,
      hregime, if_neg,
      finiteArmIIDHistoryAdaptiveRewardCorruptionBudget_uniformSuboptimalRewardBoostSource]
      using hroute

end Tsallis
end BanditRLProof
