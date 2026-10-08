import BanditRLProof.OnlineGuessingAECausal
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option pp.explicit true
set_option pp.notation false

open MeasureTheory ProbabilityTheory Filter

universe u v
namespace BanditRL.OnlineLearning

#check (∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : MeasurableSpace Ω) (P : Ω → ℝ)
    (hP : @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P),
    ∃ version : Ω → ℝ, Measurable[F] version ∧ P =ᶠ[ae μ] version)

#check (∀ {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (S : Ω → Seed)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, @Measurable _ _ (eventuallyMeasurableSpace (F t) (ae μ)) _ (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1),
    ∃ policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
      (∀ t, Measurable (policy t)) ∧
      (∀ t q, policy t q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ ω ∂μ, ∀ t, prediction t ω = policy t (S ω, fun i => Y i ω))

#check (∀ {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ)
    (hP : @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P),
    IndepFun P (Y t) μ)

#check (∀ {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, @Measurable _ _ (eventuallyMeasurableSpace (F t) (ae μ)) _ (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T)

end BanditRL.OnlineLearning
