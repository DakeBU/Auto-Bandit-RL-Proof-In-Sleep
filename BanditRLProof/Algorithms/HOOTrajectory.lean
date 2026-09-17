import BanditRLProof.Algorithms.HOOMeasurable
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! The actual HOO reward law on one infinite chronological trajectory.
Every successor kernel selects its region using only the observed prefix. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory

def prefixExtension (n : ℕ) (h : (i : Finset.Iic n) → ℝ) : ℕ → ℝ :=
  fun i => if hi : i ≤ n then h ⟨i, Finset.mem_Iic.mpr hi⟩ else 0

theorem measurable_prefixExtension (n : ℕ) : Measurable (prefixExtension n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ≤ n
  · simpa only [prefixExtension, dif_pos hi] using
      (measurable_pi_apply (⟨i, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n))
  · simpa only [prefixExtension, dif_neg hi] using
      (measurable_const : Measurable (fun _ : (i : Finset.Iic n) → ℝ => (0 : ℝ)))

theorem action_prefixExtension (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    action ν ρ (prefixExtension n (Preorder.frestrictLe n Y)) (n+1) = action ν ρ Y (n+1) := by
  apply action_causal
  intro i hi
  simp only [prefixExtension, dif_pos (show i ≤ n by omega), Preorder.frestrictLe_apply]

noncomputable def stepKernel (ν ρ : ℝ) (law : Kernel Node ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℝ) ℝ :=
  law.comap (fun h => action ν ρ (prefixExtension n h) (n+1))
    ((measurable_action ν ρ (n+1)).comp (measurable_prefixExtension n))

instance stepKernel_markov (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law] (n : ℕ) :
    IsMarkovKernel (stepKernel ν ρ law n) := by unfold stepKernel; infer_instance

noncomputable def trajectory (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law] :
    Measure (ℕ → ℝ) :=
  Kernel.trajMeasure (law (action ν ρ (fun _ => 0) 0)) (stepKernel ν ρ law)

instance trajectory_probability (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law] :
    IsProbabilityMeasure (trajectory ν ρ law) := by unfold trajectory; infer_instance

theorem stepKernel_apply_prefix (ν ρ : ℝ) (law : Kernel Node ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    stepKernel ν ρ law n (Preorder.frestrictLe n Y) = law (action ν ρ Y (n+1)) := by
  simp only [stepKernel, Kernel.comap_apply, action_prefixExtension]

/-- Conditional reward distribution is produced by the constructed trajectory,
not supplied as a confidence or stochastic-process oracle. -/
theorem trajectory_condDistrib (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law] (n : ℕ) :
    condDistrib (fun Y : ℕ → ℝ => Y (n+1)) (Preorder.frestrictLe n) (trajectory ν ρ law)
      =ᵐ[(trajectory ν ρ law).map (Preorder.frestrictLe n)] stepKernel ν ρ law n :=
  Kernel.condDistrib_trajMeasure

/-- The joint prefix/next-reward law, useful without choosing a conditional
expectation version. It keeps the actual history-dependent kernel. -/
theorem trajectory_prefix_compProd (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law] (n : ℕ) :
    (trajectory ν ρ law).map (Preorder.frestrictLe n) ⊗ₘ stepKernel ν ρ law n =
      (trajectory ν ρ law).map (fun Y => (Preorder.frestrictLe n Y, Y (n+1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end BanditRLProof.HOO
