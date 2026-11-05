import BanditRLProof.OnlineStrongConvexSupport
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import BanditRLProof.OnlineSubgradientDifferentiability
import BanditRLProof.OnlineEntropyWeightedPairing
import Mathlib.Analysis.Normed.Lp.PiLp
import BanditRLProof.OnlineStrongMonotonicity

noncomputable section
namespace BanditRL.OnlineEntropy

abbrev EntropyL1 (d : ℕ) := PiLp 1 (fun _ : Fin d => ℝ)

abbrev entropyCoordinates {d : ℕ} : EntropyL1 d ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin d => ℝ)

abbrev entropyOnL1 {d : ℕ} (c : Fin d → ℝ) (x : EntropyL1 d) : ℝ :=
  weightedEntropy c (entropyCoordinates x)

abbrev entropyFeasible {d : ℕ} (c : Fin d → ℝ) : Set (EntropyL1 d) :=
  entropyCoordinates ⁻¹' weightedSimplex c

open Set Filter
open scoped Topology
open BanditRL.OnlineConvex

private abbrev Pos {d : ℕ} : Set (Fin d → ℝ) := {x | ∀ i, 0 < x i}

private theorem pos_convex {d : ℕ} : Convex ℝ (Pos (d := d)) := by
  intro x hx y hy a b ha hb hab i
  change 0 < a * x i + b * y i
  rcases ha.eq_or_lt with h | h
  · have hb' : b = 1 := by linarith
    simpa [← h,hb'] using hy i
  · exact add_pos_of_pos_of_nonneg (mul_pos h (hx i)) (mul_nonneg hb (hy i).le)

private theorem pos_open {d : ℕ} : IsOpen (Pos (d := d)) := by
  have h : Pos (d := d) = ⋂ i : Fin d, {x : Fin d → ℝ | 0 < x i} := by
    ext x; simp [Pos]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

private theorem simplex_convex {d : ℕ} (c : Fin d → ℝ) : Convex ℝ (weightedSimplex c) := by
  intro x hx y hy a b ha hb hab
  refine ⟨pos_convex hx.1 hy.1 ha hb hab, ?_⟩
  change ∑ i, (a*x i+b*y i)/c i = 1
  calc
    _ = ∑ i, (a*(x i/c i)+b*(y i/c i)) := by
      apply Finset.sum_congr rfl; intro i _; ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]; simpa using hab

private theorem weighted_convex {d : ℕ} (c : Fin d → ℝ) (hc : ∀ i, 0 < c i) :
    ConvexOn ℝ Pos (weightedEntropy c) := by
  refine ⟨pos_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  change (∑ i, c i*(a*x i+b*y i)*Real.log (a*x i+b*y i)) ≤
    a*(∑ i, c i*x i*Real.log (x i)) + b*(∑ i, c i*y i*Real.log (y i))
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi := Real.convexOn_mul_log.2 (hx i).le (hy i).le ha hb hab
  change (a*x i+b*y i)*Real.log (a*x i+b*y i) ≤
    a*(x i*Real.log (x i))+b*(y i*Real.log (y i)) at hi
  linarith only [mul_le_mul_of_nonneg_left hi (hc i).le]

private noncomputable def extendedVia {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : E ≃L[ℝ] (Fin d → ℝ)) (c : Fin d → ℝ) (x : E) : EReal := by
  classical
  exact if t x ∈ Pos then (weightedEntropy c (t x) : EReal) else ⊤

private theorem chart_facts {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : E ≃L[ℝ] (Fin d → ℝ)) (c : Fin d → ℝ) (hc : ∀ i, 0 < c i) :
    SourceProper (extendedVia t c) ∧ IsConvexExtended (extendedVia t c) ∧
      effectiveDomain (extendedVia t c) = t ⁻¹' Pos := by
  classical
  have nb (x : E) : extendedVia t c x ≠ ⊥ := by
    by_cases h : t x ∈ Pos <;> simp [extendedVia,h]
  have dom : effectiveDomain (extendedVia t c) = t ⁻¹' Pos := by
    ext x
    change (extendedVia t c x < ⊤) ↔ t x ∈ Pos
    by_cases h : t x ∈ Pos
    · rw [show extendedVia t c x = (weightedEntropy c (t x) : EReal) by exact if_pos h]
      exact iff_of_true (EReal.coe_lt_top _) h
    · rw [show extendedVia t c x = ⊤ by exact if_neg h]
      exact iff_of_false (lt_irrefl _) h
  have ones : (fun _ : Fin d => (1:ℝ)) ∈ Pos := fun _ => zero_lt_one
  refine ⟨⟨nb, t.symm (fun _ => 1), weightedEntropy c (fun _ => 1), ?_⟩, ?_, dom⟩
  · simp [extendedVia,ones]
  · apply (convexExtended_iff_toReal _ nb).mpr
    rw [dom]
    apply ((weighted_convex c hc).comp_linearMap t.toLinearEquiv.toLinearMap).congr
    intro x hx
    change t x ∈ Pos at hx
    simp [extendedVia,hx,Function.comp_def]

private abbrev EC (d : ℕ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
private abbrev chart (d : ℕ) := (entropyCoordinates (d := d)).trans (EC d).symm

private theorem global_support {d : ℕ} (c : Fin d → ℝ) (hc : ∀ i, 0 < c i)
    (p : EntropyL1 d) (hp : p ∈ entropyFeasible c) :
    SourceSubdifferential (fun u => extendedVia entropyCoordinates c ((chart d).symm u))
        (chart d p) =
      {gradient (fun u => weightedEntropy c (EC d u)) (chart d p)} := by
  have heq : (fun u => extendedVia entropyCoordinates c ((chart d).symm u)) =
      extendedVia (EC d) c := by
    funext u
    rfl
  rw [heq]
  let u := chart d p
  have hu : EC d u ∈ Pos := by simpa [u,chart] using (hp.1 : ∀ i, 0 < entropyCoordinates p i)
  have hopen := (pos_open.preimage (EC d).continuous).mem_nhds hu
  apply theorem_2_22_gradient _ (chart_facts (EC d) c hc).2.1 u
    ⟨weightedEntropy c (EC d u), by simp [extendedVia,hu]⟩
  · filter_upwards [hopen] with v hv
    change EC d v ∈ Pos at hv
    simp [extendedVia,hv]
  · exact ((weightedEntropy_differential c (EC d u) hu).1).comp u (EC d).differentiableAt

private theorem gradient_pair {d : ℕ} (c : Fin d → ℝ) (p v : EntropyL1 d)
    (hp : p ∈ entropyFeasible c) :
    inner ℝ (gradient (fun u => weightedEntropy c (EC d u)) (chart d p)) (chart d v) =
      fderiv ℝ (weightedEntropy c) (entropyCoordinates p) (entropyCoordinates v) := by
  have hd := (weightedEntropy_differential c (entropyCoordinates p) hp.1).1
  have hp' : EC d (chart d p) = entropyCoordinates p := rfl
  have hd' : DifferentiableAt ℝ (weightedEntropy c) (EC d (chart d p)) := by rw [hp']; exact hd
  have hcomp := hd'.hasFDerivAt.comp (chart d p) ((EC d).hasFDerivAt)
  change inner ℝ (gradient (weightedEntropy c ∘ EC d) (chart d p)) (chart d v) = _
  rw [inner_gradient_left hcomp.differentiableAt, hcomp.fderiv]
  rfl

private theorem repaired_interpolation {d : ℕ} (c : Fin d → ℝ) (hc : ∀ i, 0 < c i) :
    ∀ x ∈ entropyFeasible c, ∀ y ∈ entropyFeasible c, ∀ a : ℝ, 0 < a → a < 1 →
      extendedVia entropyCoordinates c (a • x + (1-a) • y) ≤
        (a:EReal)*extendedVia entropyCoordinates c x +
          ((1-a:ℝ):EReal)*extendedVia entropyCoordinates c y -
          (((1:ℝ)/2*a*(1-a)*‖x-y‖^2:ℝ):EReal) := by
  have hV : Convex ℝ (entropyFeasible c) :=
    (simplex_convex c).linear_preimage entropyCoordinates.toLinearEquiv.toLinearMap
  have hs := chart_facts (entropyCoordinates (d := d)) c hc
  apply (SupportCarrierExample.convex_carrier_equivalence d (chart d).toLinearEquiv
    (extendedVia entropyCoordinates c) (entropyFeasible c) 1 hs.1 hs.2.1 hV zero_le_one
    (fun p hp => by
      change (SourceSubdifferential (fun u => extendedVia entropyCoordinates c ((chart d).symm u)) (chart d p)).Nonempty
      rw [global_support c hc p hp]
      exact Set.singleton_nonempty _)).mpr
  intro p hp q hq g hg j hj
  change g ∈ SourceSubdifferential (fun u => extendedVia entropyCoordinates c ((chart d).symm u)) (chart d p) at hg
  change j ∈ SourceSubdifferential (fun u => extendedVia entropyCoordinates c ((chart d).symm u)) (chart d q) at hj
  change 1 * ‖p-q‖^2 ≤ inner ℝ (g-j) (chart d (p-q))
  rw [global_support c hc p hp] at hg
  rw [global_support c hc q hq] at hj
  rw [Set.mem_singleton_iff] at hg hj
  subst g; subst j
  rw [inner_sub_left, gradient_pair c p (p-q) hp, gradient_pair c q (p-q) hq]
  have hh := weightedEntropy_pairing c (entropyCoordinates p) (entropyCoordinates q) hc hp hq
  have normid : ‖p-q‖ = ∑ i, |entropyCoordinates p i - entropyCoordinates q i| := by
    rw [PiLp.norm_eq_of_L1]
    apply Finset.sum_congr rfl
    intro i _
    exact Real.norm_eq_abs _
  rw [one_mul, normid, map_sub]
  simpa only [ContinuousLinearMap.sub_apply, Pi.sub_apply] using hh.1.trans hh.2

end BanditRL.OnlineEntropy

namespace BanditRL.OnlineEntropy
open Set BanditRL.OnlineConvex

private theorem lifted_feasible {d : ℕ} (c : Fin d → ℝ) {x : EntropyL1 d}
    (hx : x ∈ entropyFeasible c) :
    extendedVia entropyCoordinates c x = (entropyOnL1 c x : EReal) :=
  if_pos hx.1

theorem weightedEntropy_l1_interpolation {d : ℕ} (c : Fin d → ℝ)
    (hc : ∀ i, 0 < c i) :
    Convex ℝ (entropyFeasible c) ∧
    ∀ x ∈ entropyFeasible c, ∀ y ∈ entropyFeasible c, ∀ a : ℝ, 0 < a → a < 1 →
      entropyOnL1 c (a • x + (1 - a) • y) ≤
        a * entropyOnL1 c x + (1 - a) * entropyOnL1 c y -
          a * (1 - a) / 2 * ‖x - y‖ ^ 2 := by
  have hV : Convex ℝ (entropyFeasible c) :=
    (simplex_convex c).linear_preimage entropyCoordinates.toLinearEquiv.toLinearMap
  refine ⟨hV,?_⟩
  intro x hx y hy a ha ha1
  have hm := hV hx hy ha.le (by linarith : 0 ≤ 1-a) (by ring)
  have h := repaired_interpolation c hc x hx y hy a ha ha1
  rw [lifted_feasible c hm, lifted_feasible c hx, lifted_feasible c hy,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
  linarith only [h]

theorem weightedEntropy_l1_support_growth {d : ℕ} (c : Fin d → ℝ)
    (hc : ∀ i, 0 < c i) (x y : EntropyL1 d)
    (hx : x ∈ entropyFeasible c) (hy : y ∈ entropyFeasible c) :
    entropyOnL1 c y +
        fderiv ℝ (weightedEntropy c) (entropyCoordinates y) (entropyCoordinates (x - y)) +
        ‖x - y‖ ^ 2 / 2 ≤ entropyOnL1 c x ∧
    ∀ L : EntropyL1 d →L[ℝ] ℝ,
      (∀ z ∈ entropyFeasible c, entropyOnL1 c y + L (z - y) ≤ entropyOnL1 c z) →
      entropyOnL1 c y + L (x - y) + ‖x - y‖ ^ 2 / 2 ≤ entropyOnL1 c x := by
  have hV := (weightedEntropy_l1_interpolation c hc).1
  have hF := chart_facts (entropyCoordinates (d := d)) c hc
  have hdom : entropyFeasible c ⊆ effectiveDomain (extendedVia entropyCoordinates c) := by
    rw [hF.2.2]
    intro p hp
    exact hp.1
  have allL (L : EntropyL1 d →L[ℝ] ℝ)
      (hl : ∀ z ∈ entropyFeasible c, entropyOnL1 c y + L (z-y) ≤ entropyOnL1 c z) :
      entropyOnL1 c y + L (x-y) + ‖x-y‖^2/2 ≤ entropyOnL1 c x := by
    have hh := stronglyConvex_support_growth _ _ 1 hF.1 hV hdom zero_le_one
      (repaired_interpolation c hc) y hy L (fun z hz => by
        rw [lifted_feasible c hy,lifted_feasible c hz, ← EReal.coe_add,EReal.coe_le_coe_iff]
        exact hl z hz) x hx
    rw [lifted_feasible c hx,lifted_feasible c hy] at hh
    simp only [EReal.toReal_coe] at hh
    linarith only [hh]
  refine ⟨?_,allL⟩
  let L := (fderiv ℝ (weightedEntropy c) (entropyCoordinates y)).comp
    (entropyCoordinates (d := d)).toContinuousLinearMap
  apply allL L
  intro z hz
  let g := gradient (fun u => weightedEntropy c (EC d u)) (chart d y)
  have hg : g ∈ SourceSubdifferential
      (fun u => extendedVia entropyCoordinates c ((chart d).symm u)) (chart d y) := by
    rw [global_support c hc y hy]
    exact Set.mem_singleton _
  have hh := hg (chart d z)
  dsimp only at hh
  rw [(chart d).symm_apply_apply, (chart d).symm_apply_apply,
    lifted_feasible c hy, lifted_feasible c hz, ← EReal.coe_add,EReal.coe_le_coe_iff,
    ← (chart d).map_sub] at hh
  change entropyOnL1 c y + inner ℝ (gradient _ (chart d y)) (chart d (z-y)) ≤ entropyOnL1 c z at hh
  rw [gradient_pair c y (z-y) hy] at hh
  exact hh

end BanditRL.OnlineEntropy
