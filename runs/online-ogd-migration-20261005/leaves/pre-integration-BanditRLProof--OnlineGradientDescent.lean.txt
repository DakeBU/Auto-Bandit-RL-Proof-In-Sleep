import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Projected online gradient descent

Orabona, arXiv:1912.13213v10, Algorithm 2.1, Proposition 2.11,
Lemma 2.12, Theorem 2.13 (constant step only), and Eq. (2.1).
Time `t = 0` denotes source round 1; `iterate ... T` is source `x_(T+1)`.
The Hilbert-space interfaces specialize to finite-dimensional real Euclidean spaces.
-/

noncomputable section
open Set Finset
open scoped InnerProductSpace

namespace BanditRL.OnlineGradientDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A nonempty closed convex feasible set, independent of losses and comparators. -/
structure Domain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier

/-- The unique nearest point, constructed from the Hilbert projection theorem. -/
def project (V : Domain E) (z : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex V.nonempty
    V.closed.isComplete V.convex z)

/-- Source regularity: convex and differentiable on an open neighborhood of the domain. -/
def RegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V.carrier ⊆ U ∧ ConvexOn ℝ U f ∧ DifferentiableOn ℝ f U

/-- One update uses only the current point, current loss, and fixed step size. -/
def step (V : Domain E) (η : ℝ) (f : E → ℝ) (x : E) : E :=
  project V (x - η • gradient f x)

/-- Algorithm 2.1, constant step branch. The current loss is read after outputting the point. -/
def iterate (V : Domain E) (η : ℝ) (loss : ℕ → E → ℝ) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V η (loss t) (iterate V η loss x₁ t)

/-- Comparator regret of this exact generated trajectory over `T` rounds. -/
def regret (V : Domain E) (η : ℝ) (loss : ℕ → E → ℝ) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, (loss t (iterate V η loss x₁ t) - loss t u)

/-- The projection exists in the feasible set and minimizes Euclidean distance. -/
theorem project_spec (V : Domain E) (z : E) :
    project V z ∈ V.carrier ∧ ‖z - project V z‖ = ⨅ w : V.carrier, ‖z - w‖ := by
  exact Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex V.nonempty
    V.closed.isComplete V.convex z)

/-- Characterization that makes the chosen projection publicly instantiable. -/
theorem project_eq_of_variational (V : Domain E) (z p : E) (hp : p ∈ V.carrier)
    (h : ∀ w ∈ V.carrier, inner ℝ (z - p) (w - p) ≤ 0) : project V z = p := by
  have hq := (norm_eq_iInf_iff_real_inner_le_zero V.convex (project_spec V z).1).mp
    (project_spec V z).2 p hp
  have hpq := h (project V z) (project_spec V z).1
  rw [show project V z - p = -(p - project V z) by abel, inner_neg_right] at hpq
  have he : inner ℝ (z - project V z) (p - project V z) -
      inner ℝ (z - p) (p - project V z) = ‖p - project V z‖ ^ 2 := by
    rw [← inner_sub_left, show (z - project V z) - (z - p) = p - project V z by abel,
      real_inner_self_eq_norm_sq]
  have hn : ‖p - project V z‖ = 0 := by nlinarith [norm_nonneg (p - project V z)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- Proposition 2.11: distance to every feasible comparator decreases. -/
theorem proposition_2_11 (V : Domain E) (z u : E) (hu : u ∈ V.carrier) :
    ‖project V z - u‖ ≤ ‖z - u‖ := by
  have hv := (norm_eq_iInf_iff_real_inner_le_zero V.convex (project_spec V z).1).mp
    (project_spec V z).2 u hu
  have he : ‖z - u‖ ^ 2 = ‖z - project V z‖ ^ 2 -
      2 * inner ℝ (z - project V z) (u - project V z) + ‖project V z - u‖ ^ 2 := by
    conv_lhs => rw [show z - u = (z - project V z) - (u - project V z) by abel]
    rw [norm_sub_sq_real, norm_sub_rev u (project V z)]
  nlinarith [sq_nonneg ‖z - project V z‖, norm_nonneg (project V z - u), norm_nonneg (z - u)]

/-- Theorem 2.7 interface derived from convex differentiable losses, not a premise. -/
theorem first_order (V : Domain E) (f : E → ℝ) (hf : RegularLoss V f)
    (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier) :
    f x - f u ≤ inner ℝ (gradient f x) (x - u) := by
  rcases hf with ⟨U, hU, hVU, hconv, hdiff⟩
  have hg := hdiff.hasGradientAt (hU.mem_nhds (hVU hx))
  have hd : HasDerivAt (AffineMap.lineMap x u : ℝ → E) (u - x) 0 := by
    simpa only [AffineMap.lineMap_apply_module', one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (u - x)).add_const x
  have hfd := hg.hasFDerivAt
  have hfd' : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f x))
      (AffineMap.lineMap x u (0 : ℝ)) := by simpa using hfd
  have hline := hconv.comp_affineMap (AffineMap.lineMap x u : ℝ →ᵃ[ℝ] E)
  have hb := hline.le_slope_of_hasDerivAt
    (by simpa using hVU hx) (by simpa using hVU hu) (by norm_num : (0 : ℝ) < 1)
    (hfd'.comp_hasDerivAt 0 hd)
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one, InnerProductSpace.toDual_apply_apply] at hb
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hb
  linarith

/-- Lemma 2.12 preserves both inequalities of the source's one-step chain. -/
theorem lemma_2_12 (V : Domain E) (f : E → ℝ) (hf : RegularLoss V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier) :
    η * (f x - f u) ≤ η * inner ℝ (gradient f x) (x - u) ∧
    η * inner ℝ (gradient f x) (x - u) ≤
      ‖x - u‖ ^ 2 / 2 - ‖step V η f x - u‖ ^ 2 / 2 +
        η ^ 2 / 2 * ‖gradient f x‖ ^ 2 := by
  refine ⟨mul_le_mul_of_nonneg_left (first_order V f hf x u hx hu) hη.le, ?_⟩
  have hp := proposition_2_11 V (x - η • gradient f x) u hu
  have he : ‖x - η • gradient f x - u‖ ^ 2 = ‖x - u‖ ^ 2 -
      2 * η * inner ℝ (gradient f x) (x - u) + η ^ 2 * ‖gradient f x‖ ^ 2 := by
    rw [show x - η • gradient f x - u = (x - u) - η • gradient f x by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (x - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hs : ‖step V η f x - u‖ ^ 2 ≤ ‖x - η • gradient f x - u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hp 2
  nlinarith

/-- Algorithm feasibility includes the initial point and the terminal point. -/
theorem iterate_mem (V : Domain E) (η : ℝ) (loss : ℕ → E → ℝ)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) : iterate V η loss x₁ t ∈ V.carrier := by
  cases t with
  | zero => exact hx₁
  | succ t => exact (project_spec V _).1

/-- Strict-prefix causality: the point output at time `t` does not use loss `t` or later. -/
theorem iterate_prefix (V : Domain E) (η : ℝ) (loss loss' : ℕ → E → ℝ)
    (x₁ : E) (t : ℕ) (h : ∀ s < t, loss s = loss' s) :
    iterate V η loss x₁ t = iterate V η loss' x₁ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iterate, h t (Nat.lt_succ_self t), ih (fun s hs => h s (Nat.lt_succ_of_lt hs))]

/-- Theorem 2.13, fixed step: no bounded-domain premise; negative terminal residual retained. -/
theorem theorem_2_13_fixed (V : Domain E) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, RegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η) := by
  have hscaled : η * regret V η loss x₁ u T ≤
      ‖x₁ - u‖ ^ 2 / 2 - ‖iterate V η loss x₁ T - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) := by
    induction T with
    | zero => simp [regret, iterate]
    | succ T ih =>
      have hi := ih (fun t ht => hloss t (Nat.lt_succ_of_lt ht))
      have hs := lemma_2_12 V (loss T) (hloss T (Nat.lt_succ_self T)) η hη
        (iterate V η loss x₁ T) u (iterate_mem V η loss x₁ hx₁ T) hu
      simp only [regret, sum_range_succ, mul_add] at hi ⊢
      change _ ≤ _ - ‖step V η (loss T) (iterate V η loss x₁ T) - u‖ ^ 2 / 2 + _
      nlinarith [hs.1.trans hs.2]
  apply le_of_mul_le_mul_left (a := η) _ hη
  calc
    η * regret V η loss x₁ u T ≤ _ := hscaled
    _ = η * (‖x₁ - u‖ ^ 2 / (2 * η) +
        η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
        ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η)) := by field_simp; ring

/-- Equation (2.1), with the source gradient bound `L` named `G`.
A distance upper bound suffices; the diameter version below supplies it uniformly. -/
theorem equation_2_1_distance (V : Domain E) (loss : ℕ → E → ℝ)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, RegularLoss V (loss t)) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T,
      ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) :
    regret V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T := by
  have hTreal : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTreal
  have hη : 0 < D / (G * Real.sqrt T) := div_pos hD (mul_pos hG hsqrt)
  have hb := theorem_2_13_fixed V (D / (G * Real.sqrt T)) hη loss x₁ hx₁ T hloss u hu
  have hdist2 : ‖x₁ - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hsum : (∑ t ∈ range T,
      ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ^ 2) ≤
      (T : ℝ) * G ^ 2 := by
    calc
      _ ≤ ∑ _t ∈ range T, G ^ 2 := sum_le_sum fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _) (hgrad t (mem_range.mp ht)) 2
      _ = _ := by simp
  have hinit := div_le_div_of_nonneg_right hdist2 (by positivity :
    0 ≤ 2 * (D / (G * Real.sqrt T)))
  have henergy := mul_le_mul_of_nonneg_left hsum (by positivity :
    0 ≤ (D / (G * Real.sqrt T)) / 2)
  have hterminal : 0 ≤ ‖iterate V (D / (G * Real.sqrt T)) loss x₁ T - u‖ ^ 2 /
      (2 * (D / (G * Real.sqrt T))) := by positivity
  have htune : D ^ 2 / (2 * (D / (G * Real.sqrt T))) +
      (D / (G * Real.sqrt T)) / 2 * ((T : ℝ) * G ^ 2) = D * G * Real.sqrt T := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg T)
    field_simp
    nlinarith
  linarith

/-- Equation (2.1) for one horizon-tuned algorithm and every feasible comparator.
Any positive diameter upper bound is admissible, including the exact diameter. -/
theorem equation_2_1 (V : Domain E) (loss : ℕ → E → ℝ)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (hloss : ∀ t < T, RegularLoss V (loss t))
    (hgrad : ∀ t < T,
      ‖gradient (loss t) (iterate V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) :
    ∀ u ∈ V.carrier,
      regret V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T := by
  intro u hu
  exact equation_2_1_distance V loss x₁ hx₁ T hT D G hD hG hloss u hu (hdiam x₁ hx₁ u hu) hgrad

end BanditRL.OnlineGradientDescent

