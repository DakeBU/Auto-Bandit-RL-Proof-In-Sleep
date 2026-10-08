Reconstruct only C0–C2 complete definitions and seven closed propositions Q001–Q007, including all quantifiers and seven semantic slots. Read only this packet and neutral-context-v2.lean. No source identity, theorem name, body or prior verdict. Distinguish whole-vector joint independence from pairwise independence, comap information versus ambient measurability, strict past and empty history, all-seed/legal-history bounds versus almost-sure bounds, probability and integrations, fixed-comparator order, consumer versus produced causality. State exactly which side information classes and limits are covered; no kernel representation or independence assumption strengthening. Prior staged actor history disclosed; no absolute-blind/human/external/runtime attestation. Reconstruct, do not prove or accept.

```lean
import Mathlib
open MeasureTheory ProbabilityTheory
universe u v w z
namespace NeutralSeed

noncomputable def C0 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def C1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    C0 μ Y T

/-- Information available before round t: one private tape and strict-past targets. -/
def C2 {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance

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
    Monotone (C2 S Y)

def Q004 : Prop := ∀ {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ C2 S Y t)
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
    (hF : ∀ t, F t ≤ C2 S Y t)
    (prediction : ℕ → Ω → ℝ) (hP : ∀ t, Measurable[F t] (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    C1 μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ C1 μ Y prediction T

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
    C1 μ Y (fun t ω => policy t (S ω, fun i => Y i ω)) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (S ω, fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ C1 μ Y (fun t ω => policy t (S ω, fun i => Y i ω)) T

end NeutralSeed
```
