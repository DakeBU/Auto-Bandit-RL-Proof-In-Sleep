import BanditRLProof.OnlineGuessingIIDBenchmark

open MeasureTheory ProbabilityTheory
universe u v w z

namespace BanditRL.OnlineLearning

/-- Information available before round t: one private tape and strict-past targets. -/
def privateSeedPastInformation {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance

end BanditRL.OnlineLearning

open BanditRL.OnlineLearning
namespace DraftSeed
def Q001 : Prop := ∀
    {Ω : Type u} {Seed : Type v} {Χ : Type w} {Ζ : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Seed] [MeasurableSpace Χ] [MeasurableSpace Ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Seed) (X : Ω → Χ) (Y : Ω → Ζ)
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hseed : IndepFun S (fun ω => (X ω, Y ω)) μ) (hXY : IndepFun X Y μ),
    IndepFun (fun ω => (S ω, X ω)) Y μ

def Q002 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ) (t : ℕ),
    IndepFun (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) (Y t) μ

def Q003 : Prop := ∀
    {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ),
    Monotone (privateSeedPastInformation S Y)

def Q004 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ) (hP : Measurable[F] P),
    IndepFun P (Y t) μ

def Q005 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t)) (t : ℕ),
    IndepFun (fun ω => policy t (S ω, fun i => Y i ω)) (Y t) μ

def Q006 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ) (hP : ∀ t, Measurable[F t] (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T

def Q007 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t s z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t (s, z) ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    expectedFixedRegret μ Y (fun t ω => policy t (S ω, fun i => Y i ω)) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (S ω, fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y (fun t ω => policy t (S ω, fun i => Y i ω)) T

end DraftSeed
#check ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
#check MeasureTheory.Measure.prodAssoc_prod
#check MeasureTheory.Measure.map_map
#check MeasurableEquiv.map_measurableEquiv_injective
#check Measurable.comap_le
#check Measurable.of_comap_le
#check MeasurableSpace.comap_mono
#check MeasurableSpace.comap_comp
#check ProbabilityTheory.indep_of_indep_of_le_left
#check ProbabilityTheory.IndepFun_iff_Indep
#check ProbabilityTheory.iIndepFun.indepFun_finset
#check BanditRL.OnlineLearning.history_policy_independent
#check BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
#check BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
