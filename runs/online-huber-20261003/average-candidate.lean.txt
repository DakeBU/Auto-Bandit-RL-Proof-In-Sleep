import Mathlib.Analysis.SpecificLimits.Basic
import BanditRLProof.OnlineGradientDescent
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

open Set
namespace BanditRL.OnlineHuber

theorem hasDerivAt_ite_le (f g : ℝ → ℝ) (c d : ℝ)
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (he : f c = g c) :
    HasDerivAt (fun x => if x ≤ c then f x else g x) d c := by
  have hl : HasDerivWithinAt (fun x => if x ≤ c then f x else g x) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx
      simp [show x ≤ c from hx]
    · simp
  have hr : HasDerivWithinAt (fun x => if x ≤ c then f x else g x) d (Ioi c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro x hx
      simp [not_le.mpr (show c < x from hx)]
    · simpa using he
  have hu := hl.union hr
  simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hu
noncomputable def huber (delta r : ℝ) : ℝ :=
  if |r| ≤ delta then r ^ 2 / 2 else delta * (|r| - delta / 2)

theorem huber_three_pieces (delta r : ℝ) (hd : 0 ≤ delta) :
    huber delta r = if r ≤ -delta then -delta * r - delta ^ 2 / 2
      else if r ≤ delta then r ^ 2 / 2 else delta * r - delta ^ 2 / 2 := by
  by_cases hlo : r ≤ -delta
  · have hr : r ≤ 0 := by linarith
    by_cases hin : -r ≤ delta
    · have he : r = -delta := by linarith
      simp only [huber, abs_of_nonpos hr, if_pos hin, if_pos hlo]
      rw [he]
      ring
    · simp only [huber, abs_of_nonpos hr, if_neg hin, if_pos hlo]
      ring
  · by_cases hhi : r ≤ delta
    · have ha : |r| ≤ delta := abs_le.mpr ⟨le_of_lt (not_le.mp hlo), hhi⟩
      simp only [huber, if_pos ha, if_neg hlo, if_pos hhi]
    · have hr : 0 ≤ r := by linarith
      simp only [huber, abs_of_nonneg hr, if_neg hhi, if_neg hlo]
      ring

theorem huber_zero (r : ℝ) : huber 0 r = 0 := by
  unfold huber
  split_ifs with h
  · have hr : r = 0 := abs_nonpos_iff.mp h
    simp [hr]
  · ring

open Filter Topology

theorem hasDerivAt_join (f g df dg : ℝ → ℝ) (c x : ℝ)
    (hf : ∀ r, HasDerivAt f (df r) r) (hg : ∀ r, HasDerivAt g (dg r) r)
    (he : f c = g c) (hd : df c = dg c) :
    HasDerivAt (fun r => if r ≤ c then f r else g r)
      (if x ≤ c then df x else dg x) x := by
  rcases lt_trichotomy x c with h | h | h
  · simp only [if_pos (le_of_lt h)]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h] with r hr
    simp [le_of_lt hr]
  · subst x
    simp only [if_pos le_rfl]
    exact hasDerivAt_ite_le f g c (df c) (hf c) (hd.symm ▸ hg c) he
  · simp only [if_neg (not_le.mpr h)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with r hr
    simp [not_le.mpr hr]

theorem huber_hasDerivAt (delta r : ℝ) (hd : 0 ≤ delta) :
    HasDerivAt (huber delta)
      (if r ≤ -delta then -delta else if r ≤ delta then r else delta) r := by
  have hq : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
    intro x
    simpa using ((hasDerivAt_id x).pow 2).div_const 2
  have hp : ∀ x : ℝ, HasDerivAt (fun x => delta * x - delta ^ 2 / 2) delta x := by
    intro x
    simpa using ((hasDerivAt_id x).const_mul delta).sub_const (delta ^ 2 / 2)
  have hm : ∀ x : ℝ, HasDerivAt (fun x => -delta * x - delta ^ 2 / 2) (-delta) x := by
    intro x
    simpa using ((hasDerivAt_id x).const_mul (-delta)).sub_const (delta ^ 2 / 2)
  have hi : ∀ x : ℝ, HasDerivAt
      (fun x => if x ≤ delta then x ^ 2 / 2 else delta * x - delta ^ 2 / 2)
      (if x ≤ delta then x else delta) x := by
    intro x
    exact hasDerivAt_join _ _ _ _ delta x hq hp (by ring) rfl
  have hboundary : -delta ≤ delta := by linarith
  have hj := hasDerivAt_join
    (fun x => -delta * x - delta ^ 2 / 2)
    (fun x => if x ≤ delta then x ^ 2 / 2 else delta * x - delta ^ 2 / 2)
    (fun _ => -delta) (fun x => if x ≤ delta then x else delta)
    (-delta) r hm hi (by simp only [if_pos hboundary]; ring)
    (by simp only [if_pos hboundary])
  convert hj using 1
  funext x
  exact huber_three_pieces delta x hd
theorem huber_deriv_clamp (delta r : ℝ) (hd : 0 ≤ delta) :
    deriv (huber delta) r = max (-delta) (min r delta) := by
  rw [(huber_hasDerivAt delta r hd).deriv]
  by_cases hlo : r ≤ -delta
  · have hr : r ≤ delta := by linarith
    simp [hlo, min_eq_left hr, max_eq_left hlo]
  · by_cases hhi : r ≤ delta
    · simp [hlo, hhi, min_eq_left hhi, max_eq_right (le_of_lt (not_le.mp hlo))]
    · have hdd : -delta ≤ delta := by linarith
      simp [hlo, hhi, min_eq_right (le_of_lt (not_le.mp hhi)), max_eq_right hdd]

theorem huber_convex (delta : ℝ) (hd : 0 ≤ delta) :
    ConvexOn ℝ Set.univ (huber delta) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun r => (huber_hasDerivAt delta r hd).differentiableAt)
  intro x y hxy
  rw [huber_deriv_clamp delta x hd, huber_deriv_clamp delta y hd]
  exact max_le_max le_rfl (min_le_min hxy le_rfl)

theorem huber_deriv_bound (delta r : ℝ) (hd : 0 ≤ delta) :
    |deriv (huber delta) r| ≤ delta := by
  rw [huber_deriv_clamp delta r hd]
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem huber_deriv_source (delta r : ℝ) (hd : 0 ≤ delta) :
    deriv (huber delta) r = if |r| ≤ delta then r else delta * Real.sign r := by
  rw [huber_deriv_clamp delta r hd]
  by_cases ha : |r| ≤ delta
  · obtain ⟨hl, hr⟩ := abs_le.mp ha
    simp [ha, min_eq_left hr, max_eq_right hl]
  · by_cases hr : r < 0
    · have hlo : r ≤ -delta := by
        rw [abs_of_neg hr] at ha
        linarith
      have hhi : r ≤ delta := by linarith
      simp [ha, Real.sign_of_neg hr, min_eq_left hhi, max_eq_left hlo]
    · have hnonneg : 0 ≤ r := le_of_not_gt hr
      have hhi : delta ≤ r := by
        rw [abs_of_nonneg hnonneg] at ha
        linarith
      have hpos : 0 < r := by
        rw [abs_of_nonneg hnonneg] at ha
        linarith
      have hdd : -delta ≤ delta := by linarith
      simp [ha, Real.sign_of_pos hpos, min_eq_right hhi, max_eq_right hdd]

open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem huber_linear_hasGradientAt (delta y : ℝ) (hd : 0 ≤ delta) (z x : E) :
    HasGradientAt (fun w => huber delta (inner ℝ z w - y))
      (deriv (huber delta) (inner ℝ z x - y) • z) x := by
  have hf := ((innerSL ℝ z).hasFDerivAt (x := x)).sub_const y
  have hg := (huber_hasDerivAt delta (inner ℝ z x - y) hd).differentiableAt.hasDerivAt
  have hh := hg.comp_hasFDerivAt x hf
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left]

theorem huber_linear_convex (delta y : ℝ) (hd : 0 ≤ delta) (z : E) :
    ConvexOn ℝ Set.univ (fun w => huber delta (inner ℝ z w - y)) := by
  let a : E →ᵃ[ℝ] ℝ := (innerSL ℝ z).toLinearMap.toAffineMap - AffineMap.const ℝ E y
  simpa [a, Function.comp_def] using (huber_convex delta hd).comp_affineMap a

theorem huber_linear_gradient_bound (delta y : ℝ) (hd : 0 ≤ delta) (z x : E) :
    ‖gradient (fun w => huber delta (inner ℝ z w - y)) x‖ ≤ delta * ‖z‖ := by
  rw [(huber_linear_hasGradientAt delta y hd z x).gradient, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (huber_deriv_bound delta (inner ℝ z x - y) hd) (norm_nonneg z)

open BanditRL.OnlineGradientDescent Finset

def fullSpace : Domain E :=
  ⟨Set.univ, Set.univ_nonempty, isClosed_univ, convex_univ⟩

noncomputable def linearLoss (delta : ℝ) (z : E) (y : ℝ) (x : E) : ℝ :=
  huber delta (inner ℝ z x - y)

theorem project_fullSpace (x : E) : project (fullSpace : Domain E) x = x := by
  apply project_eq_of_variational fullSpace x x (by trivial)
  intro w hw
  simp

theorem huber_regular (delta y : ℝ) (hd : 0 ≤ delta) (z : E) :
    RegularLoss fullSpace (linearLoss delta z y) := by
  refine ⟨Set.univ, isOpen_univ, Set.Subset.rfl, huber_linear_convex delta y hd z, ?_⟩
  intro x hx
  exact (huber_linear_hasGradientAt delta y hd z x).differentiableAt.differentiableWithinAt

theorem huber_step (delta y eta : ℝ) (hd : 0 ≤ delta) (z x : E) :
    step fullSpace eta (linearLoss delta z y) x =
      x - eta • ((if |inner ℝ z x - y| ≤ delta then inner ℝ z x - y
        else delta * Real.sign (inner ℝ z x - y)) • z) := by
  unfold step
  rw [project_fullSpace]
  unfold linearLoss
  rw [(huber_linear_hasGradientAt delta y hd z x).gradient, huber_deriv_source delta _ hd]

theorem huber_regret_fixed (delta Z eta : ℝ) (hd : 0 ≤ delta)
    (hZ : 0 ≤ Z) (heta : 0 < eta) (z : ℕ → E) (y : ℕ → ℝ)
    (x0 u : E) (T : ℕ) (hz : ∀ t < T, ‖z t‖ ≤ Z) :
    regret fullSpace eta (fun t => linearLoss delta (z t) (y t)) x0 u T ≤
      ‖x0 - u‖ ^ 2 / (2 * eta) + eta / 2 * ((T : ℝ) * (delta * Z) ^ 2) -
      ‖iterate fullSpace eta (fun t => linearLoss delta (z t) (y t)) x0 T - u‖ ^ 2 /
        (2 * eta) := by
  let loss : ℕ → E → ℝ := fun t => linearLoss delta (z t) (y t)
  have hb := theorem_2_13_fixed fullSpace eta heta loss x0 (by trivial) T
    (fun t ht => huber_regular delta (y t) hd (z t)) u (by trivial)
  have hg : ∀ t < T, ‖gradient (loss t) (iterate fullSpace eta loss x0 t)‖ ≤ delta * Z := by
    intro t ht
    exact (huber_linear_gradient_bound delta (y t) hd (z t) _).trans
      (mul_le_mul_of_nonneg_left (hz t ht) hd)
  have hsum : (∑ t ∈ range T, ‖gradient (loss t) (iterate fullSpace eta loss x0 t)‖ ^ 2) ≤
      (T : ℝ) * (delta * Z) ^ 2 := by
    calc
      _ ≤ ∑ _t ∈ range T, (delta * Z) ^ 2 := sum_le_sum fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _) (hg t (mem_range.mp ht)) 2
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hsum (le_of_lt (half_pos heta))
  change regret fullSpace eta loss x0 u T ≤ _
  linarith
theorem huber_average_bound (delta Z : ℝ) (hd : 0 ≤ delta) (hZ : 0 ≤ Z)
    (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (T : ℕ) (hT : 0 < T)
    (hz : ∀ t < T, ‖z t‖ ≤ Z) :
    regret fullSpace (1 / Real.sqrt T) (fun t => linearLoss delta (z t) (y t)) x0 u T / T ≤
      (‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * Real.sqrt T) := by
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr ht
  have he : 0 < 1 / Real.sqrt (T : ℝ) := one_div_pos.mpr hs
  have hb := huber_regret_fixed delta Z (1 / Real.sqrt T) hd hZ he z y x0 u T hz
  have hr : 0 ≤ ‖iterate fullSpace (1 / Real.sqrt T)
      (fun t => linearLoss delta (z t) (y t)) x0 T - u‖ ^ 2 /
        (2 * (1 / Real.sqrt T)) := by positivity
  have hc : ‖x0 - u‖ ^ 2 / (2 * (1 / Real.sqrt T)) +
      (1 / Real.sqrt T) / 2 * ((T : ℝ) * (delta * Z) ^ 2) =
      ((‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * Real.sqrt T)) * T := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg T)
    field_simp
    nlinarith [congrArg (fun q : ℝ => ‖x0 - u‖ ^ 2 * q) hsq]
  apply (div_le_iff₀ ht).mpr
  linarith

theorem huber_rate_tendsto (delta Z : ℝ) (x0 u : E) :
    Filter.Tendsto (fun T : ℕ => (‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * Real.sqrt T))
      Filter.atTop (nhds 0) := by
  have h : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  convert h.const_mul ((‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / 2) using 1 <;>
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem huber_average_eventually (delta Z : ℝ) (hd : 0 ≤ delta) (hZ : 0 ≤ Z)
    (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (hz : ∀ t, ‖z t‖ ≤ Z)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ T : ℕ in Filter.atTop,
      regret fullSpace (1 / Real.sqrt T) (fun t => linearLoss delta (z t) (y t)) x0 u T / T < epsilon := by
  have hsmall := (huber_rate_tendsto delta Z x0 u).eventually (eventually_lt_nhds he)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with T hsmall hT
  exact (huber_average_bound delta Z hd hZ z y x0 u T hT (fun t ht => hz t)).trans_lt hsmall
end BanditRL.OnlineHuber
