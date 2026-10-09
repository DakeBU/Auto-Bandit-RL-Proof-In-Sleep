import BanditRLProof.OnlinePrescientBregman
import Tests.OnlineBregmanExtendedCanary
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Set BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregmanCanary

theorem closed_strict_regularizer_missing_minimum :
    let V : Set ℝ := Iic 0
    let f : ℝ → EReal := fun z => (z : EReal)
    let ψ : ℝ → ℝ := Real.exp
    V.Nonempty ∧ IsClosed V ∧ Convex ℝ V ∧ (0 : ℝ) ∈ V ∧
      SourceProper f ∧
      (∀ z : ℝ, (SourceSubdifferential f z).Nonempty) ∧
      SourceClosed (fun z => ((ψ z : ℝ) : EReal)) ∧
      StrictConvexOn ℝ univ ψ ∧
      (∀ z : ℝ, DifferentiableAt ℝ ψ z) ∧
      (0 : ℝ) ∈ interior (univ : Set ℝ) ∧
      (∀ z : ℝ, f z + ((divergence ψ z 0 : ℝ) : EReal) = ((Real.exp z - 1 : ℝ) : EReal)) ∧
      (¬ ∃ p, p ∈ V ∧ IsMinOn (fun z => f z + ((divergence ψ z 0 : ℝ) : EReal)) V p) ∧
      advance V ψ 1 f 0 = none ∧
      (∀ k : ℕ, iterate V ψ (fun _ => 1) (fun _ => f) 0 (k + 1) = none) := by
  dsimp only
  let V : Set ℝ := Iic 0
  let f : ℝ → EReal := fun z => (z : EReal)
  let ψ : ℝ → ℝ := Real.exp
  have hf : SourceProper f := ⟨fun z => EReal.coe_ne_bot z, 0, 0, rfl⟩
  have hs : ∀ z : ℝ, (SourceSubdifferential f z).Nonempty := by
    intro z
    refine ⟨1, ?_⟩
    intro y
    change (z : EReal) + (inner ℝ (1 : ℝ) (y - z) : EReal) ≤ (y : EReal)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    change z + (y - z) * 1 ≤ y
    linarith
  have hc : SourceClosed (fun z => ((ψ z : ℝ) : EReal)) := by
    intro r
    change IsClosed {z : ℝ | (Real.exp z : EReal) ≤ (r : EReal)}
    simpa only [EReal.coe_le_coe_iff] using
      (isClosed_le Real.continuous_exp (continuous_const : Continuous (fun _ : ℝ => r)))
  have hD (z : ℝ) : divergence ψ z 0 = Real.exp z - 1 - z := by
    rw [divergence, fderiv_eq_deriv_mul]
    simp only [ψ, Real.deriv_exp, Real.exp_zero, sub_zero, one_mul]
  have hO (z : ℝ) : f z + ((divergence ψ z 0 : ℝ) : EReal) =
      ((Real.exp z - 1 : ℝ) : EReal) := by
    change (z : EReal) + ((divergence ψ z 0 : ℝ) : EReal) = _
    rw [← EReal.coe_add, hD]
    congr 1
    ring
  have hn : ¬ ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((divergence ψ z 0 : ℝ) : EReal)) V p := by
    rintro ⟨p, hp, hm⟩
    have hpm : p - 1 ∈ V := by
      change p - 1 ≤ 0
      change p ≤ 0 at hp
      linarith
    have hh := hm hpm
    change f p + ((divergence ψ p 0 : ℝ) : EReal) ≤
      f (p - 1) + ((divergence ψ (p - 1) 0 : ℝ) : EReal) at hh
    rw [hO, hO, EReal.coe_le_coe_iff] at hh
    have he : Real.exp (p - 1) < Real.exp p := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hnone : advance V ψ 1 f 0 = none := by
    apply (advance_none_iff V ψ 1 f 0).mpr
    simpa only [inv_one, one_mul] using hn
  have h1 : iterate V ψ (fun _ => 1) (fun _ => f) 0 1 = none := by
    change advance V ψ 1 f 0 = none
    exact hnone
  refine ⟨⟨0, by norm_num [V]⟩, isClosed_Iic, convex_Iic 0, by norm_num [V], hf, hs, hc,
    strictConvexOn_exp, Real.differentiable_exp, by simp, hO, hn, hnone, ?_⟩
  intro k
  simpa only [Nat.add_comm] using
    iterate_no_recovery V ψ (fun _ => 1) (fun _ => f) 0 1 k h1

theorem interior_extension_boundary_difference :
    let X : Set ℝ := Ici 0
    let ψ : ℝ → ℝ := fun z => z ^ 2 + z
    let φ : ℝ → ℝ := fun z => z ^ 2 + |z|
    EqOn ψ φ X ∧ ψ (-1) ≠ φ (-1) ∧ (1 : ℝ) ∈ interior X ∧ (2 : ℝ) ∈ X ∧
      divergence ψ 2 1 = divergence φ 2 1 ∧ divergence ψ 2 1 = 1 ∧
      divergence ψ 2 0 = 4 ∧ divergence φ 2 0 = 6 ∧ ¬ DifferentiableAt ℝ φ 0 := by
  dsimp only
  let X : Set ℝ := Ici 0
  let ψ : ℝ → ℝ := fun z => z ^ 2 + z
  let φ : ℝ → ℝ := fun z => z ^ 2 + |z|
  have he : EqOn ψ φ X := by
    intro z hz
    change 0 ≤ z at hz
    simp only [ψ, φ, abs_of_nonneg hz]
  have hi : (1 : ℝ) ∈ interior X := by norm_num [X, interior_Ici]
  have ht : (2 : ℝ) ∈ X := by norm_num [X]
  have hd (z : ℝ) : HasDerivAt ψ (2 * z + 1) z := by
    convert ((hasDerivAt_id z).pow 2).add (hasDerivAt_id z) using 1
    dsimp [ψ, id]
    ring
  have hD (a b : ℝ) : divergence ψ a b = (a - b) ^ 2 := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
    dsimp [ψ]
    ring
  have hn : ¬ DifferentiableAt ℝ φ 0 := by
    intro h
    apply not_differentiableAt_abs_zero
    have hh := h.sub (((hasDerivAt_id (0 : ℝ)).pow 2).differentiableAt)
    convert hh using 1
    ext z
    simp [φ]
  have hb : divergence φ 2 0 = 6 := by
    rw [divergence, fderiv_zero_of_not_differentiableAt hn]
    norm_num [φ]
  refine ⟨he, by norm_num [ψ, φ], hi, ht,
    divergence_extension_eq X ψ φ he 2 1 ht hi, ?_, ?_, hb, hn⟩
  · rw [hD]
    norm_num
  · rw [hD]
    norm_num

theorem two_distinct_current_losses :
    let V : Set ℝ := Icc (-1) 1
    let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
    let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
    let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 8 : ℝ) : EReal) else ⊤
    let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
    SourceProper f0 ∧ SourceProper f1 ∧
      (∀ z ∈ V, (SourceSubdifferential f0 z).Nonempty) ∧
      (∀ z ∈ V, (SourceSubdifferential f1 z).Nonempty) ∧
      StrictConvexOn ℝ univ ψ ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      f0 2 = ⊤ ∧ f1 2 = ⊤ ∧
      iterate V ψ (fun _ => 1) loss (1 / 2) 0 = some (1 / 2) ∧
      iterate V ψ (fun _ => 1) loss (1 / 2) 1 = some 0 ∧
      iterate V ψ (fun _ => 1) loss (1 / 2) 2 = some (1 / 2) ∧
      (∀ (η' : ℕ → ℝ) (loss' : ℕ → ℝ → EReal),
        η' 0 = 1 → η' 1 = 1 → loss' 0 = f0 → loss' 1 = f1 →
        iterate V ψ η' loss' (1 / 2) 2 = some (1 / 2)) ∧
      divergence ψ 0 (1 / 2) = 11 / 64 ∧
      divergence ψ (1 / 2) 0 = 9 / 64 ∧
      (∀ u ∈ V, ((f0 0).toReal - (f0 u).toReal) +
        ((f1 (1 / 2)).toReal - (f1 u).toReal) ≤
        divergence ψ u (1 / 2) - divergence ψ u (1 / 2) -
          divergence ψ 0 (1 / 2) - divergence ψ (1 / 2) 0) ∧
      (-1 / 2 : ℝ) ≤ -5 / 16 := by
  dsimp only
  let V : Set ℝ := Icc (-1) 1
  let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
  let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
  let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 8 : ℝ) : EReal) else ⊤
  let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
  obtain ⟨hf0, hs0, _, _, _, hstrict, hm0, hnondiff, hD10, hD01, _, _⟩ :=
    BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic
  have hzero : (0 : ℝ) ∈ V := by norm_num [V]
  have hhalf : (1 / 2 : ℝ) ∈ V := by norm_num [V]
  have hf1 : SourceProper f1 := by
    refine ⟨?_, 0, 0, ?_⟩
    · intro z
      by_cases hz : z ∈ V <;> simp [f1, hz]
    · simp [f1, hzero]
  have hs1 : ∀ z ∈ V, (SourceSubdifferential f1 z).Nonempty := by
    intro z hz
    refine ⟨-5 / 8, ?_⟩
    intro y
    change f1 z + (inner ℝ (-5 / 8 : ℝ) (y - z) : EReal) ≤ f1 y
    by_cases hy : y ∈ V
    · simp only [f1, if_pos hz, if_pos hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      change -5 * z / 8 + (y - z) * (-5 / 8) ≤ -5 * y / 8
      linarith
    · simp only [f1, if_pos hz, if_neg hy]
      exact le_top
  have hd (z : ℝ) : HasDerivAt ψ (z ^ 3 + z) z := by
    convert (((hasDerivAt_id z).pow 4).div_const 4).add
      (((hasDerivAt_id z).pow 2).div_const 2) using 1
    dsimp [ψ, id]
    ring
  have hD (a b : ℝ) : divergence ψ a b = ψ a - ψ b - (b ^ 3 + b) * (a - b) := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
  have hD0 (z : ℝ) : divergence ψ z 0 = z ^ 4 / 4 + z ^ 2 / 2 := by
    rw [hD]
    simp [ψ]
  have huniq0 (p : ℝ) (hp : p ∈ V)
      (hm : IsMinOn (fun z => f0 z + ((divergence ψ z (1 / 2) : ℝ) : EReal)) V p) : p = 0 := by
    have hh : |p| + divergence ψ p (1 / 2) ≤ |(0 : ℝ)| + divergence ψ 0 (1 / 2) := by
      have hh := hm hzero
      simpa only [f0, if_pos hp, if_pos hzero, ← EReal.coe_add, EReal.coe_le_coe_iff] using hh
    rw [hD, hD] at hh
    dsimp [ψ] at hh
    norm_num at hh
    have hpos : 0 ≤ p ^ 4 / 4 + p ^ 2 / 2 := by
      nlinarith [sq_nonneg p, sq_nonneg (p ^ 2)]
    have hle : p ≤ 0 := by nlinarith [le_abs_self p]
    have hge : 0 ≤ p := by nlinarith [neg_le_abs p]
    exact le_antisymm hle hge
  have ha0 : advance V ψ 1 f0 (1 / 2) = some 0 := by
    cases h : advance V ψ 1 f0 (1 / 2) with
    | none =>
        have hn := (advance_none_iff V ψ 1 f0 (1 / 2)).mp h
        exact (hn ⟨0, hzero, by simpa only [inv_one, one_mul] using hm0⟩).elim
    | some p =>
        obtain ⟨hp, hm⟩ := advance_some_spec V ψ 1 f0 (1 / 2) p h
        have he := huniq0 p hp (by simpa only [inv_one, one_mul] using hm)
        exact congrArg some he
  have h1 : iterate V ψ (fun _ => 1) loss (1 / 2) 1 = some 0 := by
    change advance V ψ 1 f0 (1 / 2) = some 0
    exact ha0
  have hfact (z : ℝ) : z ^ 4 / 4 + z ^ 2 / 2 - 5 * z / 8 + 11 / 64 =
      (z - 1 / 2) ^ 2 * ((z + 1 / 2) ^ 2 / 4 + 5 / 8) := by ring
  have hfin1 : ∀ z ∈ V, f1 z ≠ ⊤ ∧ f1 z ≠ ⊥ := by
    intro z hz
    simp only [f1, if_pos hz]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hm1real : IsMinOn (fun z => (f1 z).toReal + (1 : ℝ)⁻¹ * divergence ψ z 0) V (1 / 2) := by
    intro z hz
    change (f1 (1 / 2)).toReal + (1 : ℝ)⁻¹ * divergence ψ (1 / 2) 0 ≤
      (f1 z).toReal + (1 : ℝ)⁻¹ * divergence ψ z 0
    simp only [f1, if_pos hhalf, if_pos hz, EReal.toReal_coe, inv_one, one_mul]
    rw [hD0, hD0]
    have hq : 0 ≤ (z - 1 / 2) ^ 2 * ((z + 1 / 2) ^ 2 / 4 + 5 / 8) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith only [hq, hfact z]
  have hm1 : IsMinOn (fun z => f1 z + ((divergence ψ z 0 : ℝ) : EReal)) V (1 / 2) := by
    simpa only [inv_one, one_mul] using
      (proximal_finitePart_minimizer_iff f1 V ψ 1 0 (1 / 2) hhalf hfin1).mpr hm1real
  have huniq1 (p : ℝ) (hp : p ∈ V)
      (hm : IsMinOn (fun z => f1 z + ((divergence ψ z 0 : ℝ) : EReal)) V p) : p = 1 / 2 := by
    have hh : -5 * p / 8 + divergence ψ p 0 ≤
        -5 * (1 / 2) / 8 + divergence ψ (1 / 2) 0 := by
      have hh := hm hhalf
      simpa only [f1, if_pos hp, if_pos hhalf, ← EReal.coe_add, EReal.coe_le_coe_iff] using hh
    rw [hD0, hD0] at hh
    have hlow : (5 / 8 : ℝ) * (p - 1 / 2) ^ 2 ≤
        p ^ 4 / 4 + p ^ 2 / 2 - 5 * p / 8 + 11 / 64 := by
      rw [hfact]
      nlinarith only [mul_nonneg (sq_nonneg (p - 1 / 2)) (sq_nonneg (p + 1 / 2))]
    have hsq : (p - 1 / 2) ^ 2 = 0 := by
      apply le_antisymm ?_ (sq_nonneg _)
      nlinarith only [hlow, hh]
    have he : p - 1 / 2 = 0 := sq_eq_zero_iff.mp hsq
    linarith
  have hatt : ∀ t < 2, ∀ x, iterate V ψ (fun _ => 1) loss (1 / 2) t = some x →
      ∃ p, p ∈ V ∧ IsMinOn (fun z => loss t z + (((1 : ℝ)⁻¹ * divergence ψ z x : ℝ) : EReal)) V p := by
    intro t ht x hx
    have ht' : t = 0 ∨ t = 1 := by omega
    rcases ht' with ht' | ht'
    · subst t
      have he : x = (1 / 2 : ℝ) := (Option.some.inj hx).symm
      subst x
      refine ⟨0, hzero, ?_⟩
      simpa [loss] using hm0
    · subst t
      have he : x = 0 := Option.some.inj (hx.symm.trans h1)
      subst x
      refine ⟨1 / 2, hhalf, ?_⟩
      simpa [loss] using hm1
  have h2 : iterate V ψ (fun _ => 1) loss (1 / 2) 2 = some (1 / 2) := by
    obtain ⟨p, hp⟩ := iterate_complete_of_step_attained V ψ (fun _ => 1) loss (1 / 2) 2 hatt
    obtain ⟨y, hy, hpV, hm⟩ := iterate_succ_some_spec V ψ (fun _ => 1) loss (1 / 2) p 1 hp
    have he : y = 0 := Option.some.inj (hy.symm.trans h1)
    subst y
    have hpe : p = 1 / 2 := huniq1 p hpV (by simpa [loss] using hm)
    simpa only [hpe] using hp
  have hprefix : ∀ (η' : ℕ → ℝ) (loss' : ℕ → ℝ → EReal),
      η' 0 = 1 → η' 1 = 1 → loss' 0 = f0 → loss' 1 = f1 →
      iterate V ψ η' loss' (1 / 2) 2 = some (1 / 2) := by
    intro η' loss' hη0 hη1 hl0 hl1
    have he := iterate_prefix V ψ η' (fun _ => 1) loss' loss (1 / 2) 2
      (by
        intro s hs
        have ht : s = 0 ∨ s = 1 := by omega
        rcases ht with rfl | rfl
        · exact hη0
        · exact hη1)
      (by
        intro s hs
        have ht : s = 0 ∨ s = 1 := by omega
        rcases ht with rfl | rfl
        · simpa [loss] using hl0
        · simpa [loss] using hl1)
    exact he.trans h2
  have hb : ∀ u ∈ V, ((f0 0).toReal - (f0 u).toReal) +
      ((f1 (1 / 2)).toReal - (f1 u).toReal) ≤
      divergence ψ u (1 / 2) - divergence ψ u (1 / 2) -
        divergence ψ 0 (1 / 2) - divergence ψ (1 / 2) 0 := by
    intro u hu
    have a := iterate_one_step V (convex_Icc (-1 : ℝ) 1) ψ (fun _ => 1) loss
      (1 / 2) (1 / 2) 0 0 rfl h1 (by norm_num) hf0 hs0
      (hd (1 / 2)).differentiableAt (hd 0).differentiableAt u hu
    have b := iterate_one_step V (convex_Icc (-1 : ℝ) 1) ψ (fun _ => 1) loss
      (1 / 2) 0 (1 / 2) 1 h1 h2 (by norm_num) hf1 hs1
      (hd 0).differentiableAt (hd (1 / 2)).differentiableAt u hu
    change 1 * ((f0 0).toReal - (f0 u).toReal) ≤
      divergence ψ u (1 / 2) - divergence ψ u 0 - divergence ψ 0 (1 / 2) at a
    change 1 * ((f1 (1 / 2)).toReal - (f1 u).toReal) ≤
      divergence ψ u 0 - divergence ψ u (1 / 2) - divergence ψ (1 / 2) 0 at b
    linarith only [a, b]
  refine ⟨hf0, hf1, hs0, hs1, hstrict, hnondiff, by norm_num [f0, V],
    by norm_num [f1, V], rfl, h1, h2, hprefix, hD01, hD10, hb, ?_⟩
  have hh := hb (1 / 2) hhalf
  have hl : ((f0 0).toReal - (f0 (1 / 2)).toReal) +
      ((f1 (1 / 2)).toReal - (f1 (1 / 2)).toReal) = -1 / 2 := by
    norm_num [f0, f1, V]
  have hr : divergence ψ (1 / 2) (1 / 2) - divergence ψ (1 / 2) (1 / 2) -
      divergence ψ 0 (1 / 2) - divergence ψ (1 / 2) 0 = -5 / 16 := by
    rw [hD01, hD10]
    ring
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh

theorem boundary_outside_center_run :
    let V : Set ℝ := Icc 0 1
    let f : ℝ → EReal := fun z => if z ∈ V then (z : EReal) else ⊤
    let ψ : ℝ → ℝ := fun z => z ^ 2 / 2
    SourceProper f ∧
      (∀ z ∈ V, (SourceSubdifferential f z).Nonempty) ∧
      StrictConvexOn ℝ univ ψ ∧ f (-1) = ⊤ ∧ (-1 : ℝ) ∉ V ∧
      iterate V ψ (fun _ => 1) (fun _ => f) (-1) 1 = some 0 ∧
      divergence ψ 0 (-1) = 1 / 2 ∧
      (∀ u ∈ V, -u ≤ divergence ψ u (-1) - divergence ψ u 0 - divergence ψ 0 (-1)) ∧
      (-1 / 2 : ℝ) ≤ 1 / 2 := by
  dsimp only
  let V : Set ℝ := Icc 0 1
  let f : ℝ → EReal := fun z => if z ∈ V then (z : EReal) else ⊤
  let ψ : ℝ → ℝ := fun z => z ^ 2 / 2
  obtain ⟨hf, hs, htop, hout, _, _, hstrict, hm, hmove, _, _⟩ :=
    BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center
  have hz : (0 : ℝ) ∈ V := by norm_num [V]
  have hd (z : ℝ) : HasDerivAt ψ z z := by
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;> dsimp [ψ, id] <;> ring
  have hD (a b : ℝ) : divergence ψ a b = (a - b) ^ 2 / 2 := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
    dsimp [ψ]
    ring
  have huniq (p : ℝ) (hp : p ∈ V)
      (hmin : IsMinOn (fun z => f z + ((divergence ψ z (-1) : ℝ) : EReal)) V p) : p = 0 := by
    have hh : p + divergence ψ p (-1) ≤ 0 + divergence ψ 0 (-1) := by
      have hh := hmin hz
      simpa only [f, if_pos hp, if_pos hz, ← EReal.coe_add, EReal.coe_le_coe_iff] using hh
    rw [hD, hD] at hh
    have hpos : 0 ≤ p := hp.1
    nlinarith [sq_nonneg p]
  have ha : advance V ψ 1 f (-1) = some 0 := by
    cases h : advance V ψ 1 f (-1) with
    | none =>
        have hn := (advance_none_iff V ψ 1 f (-1)).mp h
        exact (hn ⟨0, hz, by simpa only [inv_one, one_mul] using hm⟩).elim
    | some p =>
        obtain ⟨hp, hmin⟩ := advance_some_spec V ψ 1 f (-1) p h
        have he := huniq p hp (by simpa only [inv_one, one_mul] using hmin)
        exact congrArg some he
  have hrun : iterate V ψ (fun _ => 1) (fun _ => f) (-1) 1 = some 0 := by
    change advance V ψ 1 f (-1) = some 0
    exact ha
  have hb : ∀ u ∈ V, -u ≤ divergence ψ u (-1) - divergence ψ u 0 - divergence ψ 0 (-1) := by
    intro u hu
    have hh := iterate_one_step V (convex_Icc (0 : ℝ) 1) ψ (fun _ => 1) (fun _ => f)
      (-1) (-1) 0 0 rfl hrun (by norm_num) hf hs (hd (-1)).differentiableAt
      (hd 0).differentiableAt u hu
    simpa only [f, if_pos hz, if_pos hu, EReal.toReal_coe, one_mul, zero_sub] using hh
  refine ⟨hf, hs, hstrict, htop, hout, hrun, hmove, hb, ?_⟩
  have hh := hb (1 / 2) (by norm_num [V])
  have hl : -(1 / 2 : ℝ) = -1 / 2 := by norm_num
  have hr : divergence ψ (1 / 2) (-1) - divergence ψ (1 / 2) 0 -
      divergence ψ 0 (-1) = 1 / 2 := by
    rw [hD, hD, hD]
    norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh

end BanditRL.OnlinePrescientBregmanCanary
