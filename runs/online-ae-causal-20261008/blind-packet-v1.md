Scoped context only. Finset.range t is{0,...,t-1}; its subtype is the finite-history coordinate type. Measure mu is on the ambient measurable space. AEStronglyMeasurable[F] P mu means existence of an F-strongly-measurable real function equal to P mu-almost everywhere, using ambient mu (not an asserted completion identity). iIndepFun is joint independence of the infinite family; IndepFun S(fun omega t=>Y t omega) is seed independence from the entire infinite stream. IdentDistrib is identical distribution under the two displayed measures. These terms are used exactly as the pinned Lean APIs define them.

def privateSeedPastInformation(S:Omega->Seed)(Y:Nat->Omega->Real)(t:Nat) := comap (fun omega => (S omega, fun i:range(t) => Y i omega)) productMeasurableSpace
expectedFixedMinimum(mu,Y,T) := sInf ((fun u:Real => integral mu (fun omega => sum(t<T) (u-Y_t omega)^2)) '' Icc(0,1))
expectedFixedRegret(mu,Y,P,T) := integral mu (fun omega => sum(t<T) (P_t omega-Y_t omega)^2) - expectedFixedMinimum(mu,Y,T)

Reconstruct only the following exact Lean headers in natural language and LaTeX, seven semantic slots each. No source identity, proof body, prior reviewer verdict or production acceptance is supplied. Requested Astra/medium is unverified runtime configuration. This actor has prior staged history; disclose it and do not claim absolute blindness.

```lean
import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Topology.UnitInterval

open MeasureTheory ProbabilityTheory

universe u v
namespace BanditRL.OnlineLearning

theorem ae_predictable_exists_bounded_history_policy {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (S : Ω → Seed)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, AEStronglyMeasurable[F t] (prediction t) μ)
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) :
    ∃ policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
      (∀ t, Measurable (policy t)) ∧
      (∀ t q, policy t q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ ω ∂μ, ∀ t, prediction t ω = policy t (S ω, fun i => Y i ω)

theorem ae_predictable_private_seed_independent {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ) (hP : AEStronglyMeasurable[F] P μ) :
    IndepFun P (Y t) μ

theorem ae_predictable_private_seed_expectedFixed_excess {Ω : Type u} {Seed : Type v}
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
    (hP : ∀ t, AEStronglyMeasurable[F t] (prediction t) μ)
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T

end BanditRL.OnlineLearning
```
