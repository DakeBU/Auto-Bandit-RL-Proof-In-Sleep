import BanditRLProof.Algorithms.UCB

/-!
# Source MOSS index and deterministic selection step

Algorithm 7 in Lattimore--Szepesvari, *Bandit Algorithms*, uses a horizon
dependent, realized-pull-count index. These definitions keep its factor four
and log-plus truncation. They do not yet construct a stochastic history law
or prove Theorem 9.1's regret bound.
-/

namespace BanditRLProof.MOSS

/-- Source convention `log max {1,x}`. -/
noncomputable def logPlus (x : ℝ) : ℝ := Real.log (max 1 x)

/-- Source confidence radius at sample count `s`. Real division totalizes
`s=0`; the post-initialization algorithm must be used on positive counts. -/
noncomputable def radius (n k s : ℕ) : ℝ :=
  Real.sqrt (4 / (s : ℝ) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ))))

/-- Source index for arbitrary current empirical means and pull counts. -/
noncomputable def index {k : ℕ} (n : ℕ) (empiricalMean : Fin k → ℝ)
    (pulls : Fin k → ℕ) (a : Fin k) : ℝ :=
  empiricalMean a + radius n k (pulls a)

/-- Zero-based Algorithm 7 action: first each arm once, then a real argmax.
This accepts a state; consistency of that state with past feedback is a
separate history-level obligation. -/
noncomputable def action {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (empiricalMean : Fin k → ℝ) (pulls : Fin k → ℕ) : Fin k :=
  if ht : t < k then ⟨t, ht⟩ else UCB.scoreArgmax hk (index n empiricalMean pulls)

theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x :=
  Real.log_nonneg (le_max_left 1 x)

theorem radius_nonneg (n k s : ℕ) : 0 ≤ radius n k s :=
  Real.sqrt_nonneg _

@[simp] theorem radius_zero (n k : ℕ) : radius n k 0 = 0 := by
  simp [radius]

/-- Exact squared source radius, including the totalized zero-count branch. -/
theorem radius_sq (n k s : ℕ) :
    radius n k s ^ 2 =
      4 / (s : ℝ) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ))) := by
  apply Real.sq_sqrt
  exact mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg s))
    (logPlus_nonneg _)

@[simp] theorem action_of_lt {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (empiricalMean : Fin k → ℝ) (pulls : Fin k → ℕ) (ht : t < k) :
    action hk n t empiricalMean pulls = ⟨t, ht⟩ := by
  simp [action, ht]

/-- Initialization selects each source arm at its own zero-based time. -/
theorem action_initial_arm {k : ℕ} (hk : 0 < k) (n : ℕ)
    (empiricalMean : Fin k → ℝ) (pulls : Fin k → ℕ) (a : Fin k) :
    action hk n a.val empiricalMean pulls = a := by
  simp [action, a.isLt]

theorem action_index_max {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (empiricalMean : Fin k → ℝ) (pulls : Fin k → ℕ)
    (ht : k ≤ t) (a : Fin k) :
    index n empiricalMean pulls a ≤
      index n empiricalMean pulls (action hk n t empiricalMean pulls) := by
  simpa [action, not_lt.mpr ht] using
    UCB.scoreArgmax_spec hk (index n empiricalMean pulls) a

/-- The large-gap selection implication in the proof of Theorem 9.1.
The optimism-deficit bound is explicit and is not a concentration theorem. -/
theorem selected_index_gt_mean_add_half_gap {k : ℕ} (hk : 0 < k)
    (n t : ℕ) (mean empiricalMean : Fin k → ℝ) (pulls : Fin k → ℕ)
    (best chosen : Fin k) (deficit : ℝ) (ht : k ≤ t)
    (hselected : action hk n t empiricalMean pulls = chosen)
    (hoptimism : mean best - deficit ≤ index n empiricalMean pulls best)
    (hgap : 2 * deficit < mean best - mean chosen) :
    mean chosen + (mean best - mean chosen) / 2 <
      index n empiricalMean pulls chosen := by
  have hmax := action_index_max hk n t empiricalMean pulls ht best
  rw [hselected] at hmax
  linarith

end BanditRLProof.MOSS
