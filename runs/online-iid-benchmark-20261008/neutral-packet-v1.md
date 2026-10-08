Reconstruct only four complete definitions C0–C3 and eight closed propositions Q001–Q008 in natural language, LaTeX and seven semantic slots. No source identity, proof bodies, desired verdict or prior acceptance. Distinguish the order of infimum and integration, actual image/IsLeast membership, a.s. versus pointwise bounds, probability normalization/same-law versus independence, supplied independent-prediction consumer versus explicit finite strict-history and fixed first-output predictor, oracle distribution mean versus unknown-distribution learner, zero/positive horizons and normalization. Prior staged actor history disclosed, no absolute-blind/human/external/runtime attestation. Do not read any other files/source identities. Reconstruct rather than prove or accept.

```lean
import Mathlib
open MeasureTheory ProbabilityTheory
namespace NeutralExpected
noncomputable def C2 (y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, y t) / T
noncomputable def C3 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 / 2 else C2 y t
noncomputable def C0 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def C1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    C0 μ Y T

def Q001 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (u : ℝ),
    (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ +
        (T : ℝ) * (u - ∫ ω, Y 0 ω ∂μ)^2

def Q002 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
        Set.Icc (0 : ℝ) 1) ((T : ℝ) * variance (Y 0) μ)

def Q003 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    C0 μ Y T = (T : ℝ) * variance (Y 0) μ

def Q004 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, MemLp (prediction t) 2 μ)
    (hInd : ∀ t, IndepFun (prediction t) (Y t) μ) (T : ℕ),
    (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
      (T : ℝ) * variance (Y 0) μ =
        ∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ

def Q005 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, policy t z ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    C1 μ Y (fun t ω => policy t (fun i => Y i ω)) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ C1 μ Y (fun t ω => policy t (fun i => Y i ω)) T

def Q006 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ) (T : ℕ),
    C1 μ Y (fun t ω => C3 (fun i => Y i ω) t) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (C3 (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ C1 μ Y (fun t ω => C3 (fun i => Y i ω) t) T

def Q007 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ),
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      C1 μ Y (fun _ _ => ∫ ω, Y 0 ω ∂μ) T = 0

def Q008 : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, policy t z ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T),
    (∫ ω, ∑ t ∈ Finset.range T, (policy t (fun i => Y i ω) - Y t ω)^2 ∂μ) /
        (T : ℝ) - variance (Y 0) μ =
      C1 μ Y (fun t ω => policy t (fun i => Y i ω)) T / (T : ℝ)

end NeutralExpected
```
