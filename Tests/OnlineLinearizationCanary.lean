import BanditRLProof.OnlineLinearization

/-! Real causal OCO-to-OLO reduction with strict slack, nonzero supports,
positive endpoint distance, universal two-round OLO producer and public adapters. -/
noncomputable section
namespace LinearizationProbe
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineLinearization

def V : Domain (E := ℝ) := ⟨univ, ⟨0, mem_univ 0⟩, isClosed_univ, convex_univ⟩
def learner : LinearPolicy (E := ℝ) := fun t h => -(∑ i : Fin t, h i)
def quadratic (x : ℝ) : EReal := (((x - 1) ^ 2 / 2 : ℝ) : EReal)
def affine (x : ℝ) : EReal := (x : EReal)
def losses (t : ℕ) : ℝ → EReal := if t = 0 then quadratic else affine
def policy : SupportPolicy (E := ℝ) := fun t _ h _ => if t = 0 then h (Fin.last t) - 1 else 1
abbrev x (t : ℕ) := output learner losses policy t
abbrev g (t : ℕ) := selected learner losses policy t

theorem learner_feasible : Feasible V learner := by
  intro t h
  exact mem_univ _

theorem quadratic_support (z : ℝ) : z - 1 ∈ SourceSubdifferential quadratic z := by
  intro y
  change (((z - 1) ^ 2 / 2 : ℝ) : EReal) +
    ((inner ℝ (z - 1) (y - z) : ℝ) : EReal) ≤ (((y - 1) ^ 2 / 2 : ℝ) : EReal)
  norm_cast
  change (z - 1) ^ 2 / 2 + (y - z) * (z - 1) ≤ (y - 1) ^ 2 / 2
  nlinarith [sq_nonneg (y - z)]

theorem affine_support (z : ℝ) : (1 : ℝ) ∈ SourceSubdifferential affine z := by
  intro y
  change (z : EReal) + ((inner ℝ (1 : ℝ) (y - z) : ℝ) : EReal) ≤ (y : EReal)
  norm_cast
  change z + (y - z) * 1 ≤ y
  linarith

theorem quadratic_on : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V quadratic := by
  constructor
  · refine ⟨?_, 0, 1 / 2, ?_⟩
    · intro z; simp [quadratic]
    · norm_num [quadratic]
  · intro z hz
    exact ⟨z - 1, quadratic_support z⟩

theorem affine_on : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V affine := by
  constructor
  · refine ⟨?_, 0, 0, rfl⟩
    intro z; simp [affine]
  · intro z hz
    exact ⟨1, affine_support z⟩

theorem losses_on (t : ℕ) : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (losses t) := by
  unfold losses
  split_ifs
  · exact quadratic_on
  · exact affine_on

theorem x_zero : x 0 = 0 := by
  simp [x, output, learner]

theorem g_zero : g 0 = -1 := by
  change outputHistory learner (history learner losses policy 0) (Fin.last 0) - 1 = -1
  rw [outputHistory_last]
  simp [learner]

theorem g_one : g 1 = 1 := by
  simp [g, selected, policy]

theorem x_one : x 1 = 1 := by
  change output learner losses policy 1 = 1
  rw [output_linear_run]
  norm_num [linearRun, learner, Fin.sum_univ_succ, g_zero]

theorem x_two : x 2 = 0 := by
  change output learner losses policy 2 = 0
  rw [output_linear_run]
  norm_num [linearRun, learner, Fin.sum_univ_succ, g_zero, g_one]

theorem feedback_two : LegalFeedback learner losses policy 2 := by
  intro t ht
  have hi : t = 0 ∨ t = 1 := by omega
  rcases hi with rfl | rfl
  · change g 0 ∈ SourceSubdifferential (losses 0) (x 0)
    rw [g_zero, x_zero]
    simpa [losses] using quadratic_support 0
  · change g 1 ∈ SourceSubdifferential (losses 1) (x 1)
    rw [g_one, x_one]
    simpa [losses] using affine_support 1

theorem actual_same_linear_run : x 1 = linearRun learner g 1 :=
  output_linear_run learner losses policy 1

theorem actual_convex_regret : regret learner losses policy 1 2 = 1 / 2 := by
  norm_num [regret, Finset.sum_range_succ, x_zero, x_one, losses, quadratic, affine]

theorem actual_linear_regret : BanditRL.OnlineLearning.comparatorRegret
    (fun t => linearLoss (g t)) (linearRun learner g) 1 2 = 1 := by
  rw [BanditRL.OnlineLearning.comparatorRegret_eq_sum]
  simp only [← output_linear_run]
  norm_num [Finset.sum_range_succ, g_zero, g_one, x_zero, x_one, linearLoss, RCLike.inner_apply]

theorem actual_public_comparison : regret learner losses policy 1 2 ≤
    BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (g t))
      (linearRun learner g) 1 2 :=
  regret_comparison V learner losses policy 2 (fun t _ => losses_on t) feedback_two 1 (mem_univ _)

theorem actual_strict_slack : regret learner losses policy 1 2 <
    BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (g t))
      (linearRun learner g) 1 2 := by
  rw [actual_convex_regret, actual_linear_regret]
  norm_num

def bound (v : ℕ → ℝ) (u : ℝ) (T : ℕ) : ℝ :=
  u ^ 2 / 2 + (∑ t ∈ range T, (v t) ^ 2) / 2 - (linearRun learner v T - u) ^ 2 / 2

theorem universal_two (v : ℕ → ℝ) (u : ℝ) :
    BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (v t))
      (linearRun learner v) u 2 = bound v u 2 := by
  have hinner (a b : ℝ) : inner ℝ a b = b * a := by rfl
  simp [BanditRL.OnlineLearning.comparatorRegret, Finset.sum_range_succ, linearRun,
    learner, Fin.sum_univ_succ, linearLoss, hinner, bound]
  ring

theorem actual_public_transfer : regret learner losses policy 1 2 ≤ bound g 1 2 :=
  regret_transfer V learner losses policy 2 (fun t _ => losses_on t) feedback_two bound
    (fun v u _ => (universal_two v u).le) 1 (mem_univ _)

theorem actual_bound_value : bound g 1 2 = 1 := by
  have hx : linearRun learner g 2 = 0 := by
    rw [← output_linear_run]
    exact x_two
  norm_num [bound, Finset.sum_range_succ, g_zero, g_one, hx]

theorem nonzero_energy : (∑ t ∈ range 2, (g t) ^ 2) = 2 := by
  norm_num [Finset.sum_range_succ, g_zero, g_one]

theorem positive_terminal : ‖x 2 - 1‖ ^ 2 = 1 := by
  rw [x_two]
  norm_num

theorem canonical_producer_instance :
    regret learner losses BanditRL.OnlineSubgradientPolicy.canonicalPolicy 1 2 ≤
      BanditRL.OnlineLearning.comparatorRegret
        (fun t => linearLoss (selected learner losses BanditRL.OnlineSubgradientPolicy.canonicalPolicy t))
        (linearRun learner (selected learner losses BanditRL.OnlineSubgradientPolicy.canonicalPolicy)) 1 2 :=
  canonical_regret_comparison V learner learner_feasible losses 2 (fun t _ => losses_on t) 1 (mem_univ _)

def invalid_future (t : ℕ) : ℝ → EReal := if t = 0 then losses 0 else fun _ => ⊤

theorem current_and_future_do_not_change_output : output learner invalid_future policy 1 = 1 := by
  have h := output_prefix learner losses invalid_future policy 1 (by
    intro s hs
    have he : s = 0 := by omega
    subst s
    simp [invalid_future])
  exact h.symm.trans x_one

theorem zero_horizon_actual_comparison : regret learner losses policy 1 0 ≤
    BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (g t))
      (linearRun learner g) 1 0 :=
  regret_comparison V learner losses policy 0 (fun t ht => False.elim (by omega))
    (fun t ht => False.elim (by omega)) 1 (mem_univ _)
end LinearizationProbe
