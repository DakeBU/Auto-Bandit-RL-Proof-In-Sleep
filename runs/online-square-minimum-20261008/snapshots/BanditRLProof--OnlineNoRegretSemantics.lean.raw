import BanditRLProof.OnlineLearningAsymptotic
import Mathlib.Tactic

open Filter
namespace BanditRL.OnlineLearning

/-- Literal ordinary-real-limit reading, kept separate from the shared upper condition. -/
def LimitNoRegret {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∃ a : ℝ, a ≤ 0 ∧
    Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)

theorem noRegret_limit_nonpos {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hNR : NoRegret V loss prediction) (u : X) (hu : u ∈ V) (a : ℝ)
    (hl : Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)) :
    a ≤ 0 := by
  by_contra h
  have hpos : 0 < a := lt_of_not_ge h
  have hbound : a ≤ a / 2 :=
    le_of_tendsto hl (hNR u hu (a / 2) (by linarith))
  linarith

theorem limitNoRegret_implies_noRegret {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hL : LimitNoRegret V loss prediction) :
    NoRegret V loss prediction := by
  intro u hu ε hε
  rcases hL u hu with ⟨a, hle, ha⟩
  exact ((tendsto_order.mp ha).2 ε (lt_of_le_of_lt hle hε)).mono
    (fun _ h => h.le)

theorem limitNoRegret_iff_noRegret_of_converges {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hc : ∀ u ∈ V, ∃ a : ℝ,
      Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)) :
    LimitNoRegret V loss prediction ↔ NoRegret V loss prediction := by
  constructor
  · exact limitNoRegret_implies_noRegret V loss prediction
  · intro hNR u hu
    rcases hc u hu with ⟨a, ha⟩
    exact ⟨a, noRegret_limit_nonpos V loss prediction hNR u hu a ha, ha⟩

namespace NoRegretCounterexample

/-- A nonnegative horizon potential with alternating normalized values. -/
noncomputable def potential (T : ℕ) : ℝ :=
  if T % 2 = 0 then (T : ℝ) else 0

/-- Actual exogenous real affine losses; no horizon-dependent learner. -/
noncomputable def loss (t : ℕ) (x : ℝ) : ℝ :=
  (potential (t + 1) - potential t) * x

theorem regret_eq (T : ℕ) (u : ℝ) :
    comparatorRegret loss (fun _ => 0) u T = -potential T * u := by
  have hs : (∑ t ∈ Finset.range T, loss t u) = potential T * u := by
    induction T with
    | zero => simp [potential]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      change potential n * u + (potential (n + 1) - potential n) * u =
        potential (n + 1) * u
      ring
  unfold comparatorRegret
  have hz : (∑ t ∈ Finset.range T, loss t (0 : ℝ)) = 0 := by
    simp [loss]
  rw [hz, hs]
  ring

theorem noRegret :
    NoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0) := by
  intro u hu ε hε
  apply Filter.Eventually.of_forall
  intro T
  rw [regret_eq]
  have hp : 0 ≤ potential T := by
    unfold potential
    split_ifs
    · exact Nat.cast_nonneg T
    · norm_num
  have hn : -potential T * u ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) hu.1
  exact (div_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg T)).trans hε.le

theorem normalized_even (n : ℕ) :
    comparatorRegret loss (fun _ => 0) 1 (2 * (n + 1)) /
      ((2 * (n + 1) : ℕ) : ℝ) = -1 := by
  rw [regret_eq]
  have he : 2 * (n + 1) % 2 = 0 := by omega
  simp only [potential, if_pos he, mul_one]
  have hn : ((2 * (n + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [neg_div, div_self hn]

theorem normalized_odd (n : ℕ) :
    comparatorRegret loss (fun _ => 0) 1 (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) = 0 := by
  rw [regret_eq]
  have ho : (2 * n + 1) % 2 ≠ 0 := by omega
  simp only [potential, if_neg ho, neg_zero, zero_mul, zero_div]

theorem no_limit :
    ¬ ∃ a : ℝ, Tendsto
      (fun T : ℕ => comparatorRegret loss (fun _ => 0) 1 T / T) atTop (nhds a) := by
  rintro ⟨a, ha⟩
  have he : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * (n + 1); omega) tendsto_id
  have ho : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * n + 1; omega) tendsto_id
  have hE : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds a) := by
    simpa only [Function.comp_def, normalized_even] using ha.comp he
  have hO : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds a) := by
    simpa only [Function.comp_def, normalized_odd] using ha.comp ho
  have hEa : a = (-1 : ℝ) := tendsto_nhds_unique hE tendsto_const_nhds
  have hOa : a = (0 : ℝ) := tendsto_nhds_unique hO tendsto_const_nhds
  linarith

theorem strict_separation :
    NoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0) := by
  refine ⟨noRegret, ?_⟩
  intro hL
  rcases hL 1 (by norm_num) with ⟨a, _, ha⟩
  exact no_limit ⟨a, ha⟩

end NoRegretCounterexample
end BanditRL.OnlineLearning
