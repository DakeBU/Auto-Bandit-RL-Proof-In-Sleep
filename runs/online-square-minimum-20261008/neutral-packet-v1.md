Reconstruct only the four definitions C0-C3 and six closed propositions Q001-Q006 below, in natural language, LaTeX and seven semantic slots. No source identity, theorem proofs, desired verdict or prior acceptance is supplied. Explicitly distinguish finite-horizon minimum/infimum, feasibility, arbitrary supplied prediction versus the explicitly defined strict-prefix predictor, positive-horizon restrictions, signed comparisons, empty-prefix conventions and coefficient/indexing. Do not read other files or source identities. No proof/acceptance judgment; staged actor history is disclosed, no absolute-blind/runtime/human/external attestation.

```lean
import Mathlib
namespace NeutralMinimum
noncomputable def C0 (y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, y t) / T
noncomputable def C1 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 / 2 else C0 y t
noncomputable def C2 (loss : ℕ → ℝ → ℝ) (prediction : ℕ → ℝ)
    (u : ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, loss t (prediction t)) -
    ∑ t ∈ Finset.range T, loss t u
noncomputable def C3 (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)
def Q001 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C0 y T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∑ t ∈ Finset.range T, (C0 y T - y t)^2) ≤
          ∑ t ∈ Finset.range T, (u - y t)^2

def Q002 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1) =
        ∑ t ∈ Finset.range T, (C0 y T - y t)^2

def Q003 : Prop := ∀ (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C3 y prediction T =
      C2 (fun t x => (x - y t)^2) prediction (C0 y T) T

def Q004 : Prop := ∀ (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1),
    C2 (fun t x => (x - y t)^2) prediction u T ≤
      C3 y prediction T

def Q005 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C3 y (C1 y) T ≤ 4 + 4 * Real.log T

def Q006 : Prop := ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    C3 y (C1 y) T ≤
      (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)

end NeutralMinimum
```
