import BanditRLProof.Algorithms.CUCBConcentration
import BanditRLProof.ProbabilityUnionBound

/-! Peeling over the actual random number of observed outcomes. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem observationCount_le {m : ℕ} (Y : ℕ → Feedback m) (n : ℕ) (i : Fin m) :
    observationCount Y n i≤n := by
  induction n with
  | zero => simp [observationCount]
  | succ n ih =>
    rw [observationCount_succ]
    split_ifs <;> omega

variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] {m : ℕ}

noncomputable def pathDeviation (D : Measure UnitOutcome) (i : Fin m) (n : ℕ)
    (lower : Bool) (Y : ℕ → Round A m) : ℝ :=
  if lower then -(∑t∈Finset.range n, pathNoise D i t Y)
  else ∑t∈Finset.range n, pathNoise D i t Y

variable (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
variable [IsMarkovKernel oracle] [IsMarkovKernel environment]
variable (D : Measure UnitOutcome) [IsProbabilityMeasure D] (i : Fin m)
variable (hcompat : ∀a, ObservationCompatible (environment a) D i)
include hcompat

theorem path_deviation_slice (n k : ℕ) (lower : Bool) (L : ℝ) (hL : 0≤L) (hk : 0<k) :
    (cucbTrajectory oracle environment) {Y |
      Real.sqrt ((k:ℝ)*L/2)≤pathDeviation D i n lower Y ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k} ≤ ENNReal.ofReal (Real.exp (-L)) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have he : -2*(Real.sqrt ((k:ℝ)*L/2))^2/k = -L := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  cases lower
  · simpa only [pathDeviation, Bool.false_eq_true, if_false, sum_pathCount, he] using
      path_noise_count_tail_optimized oracle environment D i hcompat n
        (Real.sqrt ((k:ℝ)*L/2)) k (Real.sqrt_nonneg _) hkR
  · simpa only [pathDeviation, if_true, sum_pathCount, he] using
      path_negative_noise_count_tail_optimized oracle environment D i hcompat n
        (Real.sqrt ((k:ℝ)*L/2)) k (Real.sqrt_nonneg _) hkR

theorem path_deviation_confidence (n : ℕ) (lower : Bool) (L : ℝ) (hL : 0≤L) :
    (cucbTrajectory oracle environment) {Y |
      0<observationCount (fun t => (Y t).2) n i ∧
      Real.sqrt ((observationCount (fun t => (Y t).2) n i : ℝ)*L/2)≤
        pathDeviation D i n lower Y} ≤ (n:ENNReal)*ENNReal.ofReal (Real.exp (-L)) := by
  let E : ℕ → Set (ℕ → Round A m) := fun k => {Y |
    Real.sqrt ((k:ℝ)*L/2)≤pathDeviation D i n lower Y ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k}
  have hs : {Y : ℕ → Round A m |
      0<observationCount (fun t => (Y t).2) n i ∧
      Real.sqrt ((observationCount (fun t => (Y t).2) n i : ℝ)*L/2)≤pathDeviation D i n lower Y}
      ⊆ ⋃ k∈Finset.Icc 1 n, E k := by
    intro Y hY
    apply Set.mem_iUnion.mpr ⟨observationCount (fun t => (Y t).2) n i, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hY.1, observationCount_le _ n i⟩, ?_⟩
    exact ⟨hY.2, le_rfl⟩
  calc
    _ ≤ (cucbTrajectory oracle environment) (⋃k∈Finset.Icc 1 n, E k) := measure_mono hs
    _ ≤ ∑k∈Finset.Icc 1 n, (cucbTrajectory oracle environment) (E k) :=
      ProbabilityUnionBound.measure_biUnion_finset_le _ _ E
    _ ≤ ∑_k∈Finset.Icc 1 n, ENNReal.ofReal (Real.exp (-L)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact path_deviation_slice oracle environment D i hcompat n k lower L hL
        (Finset.mem_Icc.mp hk).1
    _ = _ := by simp [nsmul_eq_mul]

end BanditRLProof.CUCB
