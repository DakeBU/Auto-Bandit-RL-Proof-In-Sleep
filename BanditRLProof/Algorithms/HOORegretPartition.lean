import BanditRLProof.HOOPartition
import BanditRLProof.Algorithms.HOOExpectedVisits

/-! Pathwise regret contributions for the actual fresh-node HOO trace. -/
namespace BanditRLProof.HOO
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

theorem action_singleton_count_le_one (ν ρ : ℝ) (Y : ℕ → ℝ) (N : ℕ) (p : Node) :
    (∑ n ∈ Finset.range N, if action ν ρ Y n=p then (1:ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have hh : ((Finset.range N).filter (fun n => action ν ρ Y n=p)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact action_injective ν ρ Y ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  exact_mod_cast hh

theorem RegularCovering.deep_regret_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hw : WeaklyLipschitz f C.ell best)
    (H N : ℕ) (Y : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, if action C.nu1 C.rho Y n ∈ C.deepGoodNodes f best H
      then best-f (C.toCovering.arm C.nu1 C.rho Y n) else 0) ≤ 4*(C.nu1*C.rho^H)*N := by
  calc
    _ ≤ ∑ _n ∈ Finset.range N, 4*(C.nu1*C.rho^H) := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with he
      · obtain ⟨p, hp, hpv⟩ := he
        exact C.descendant_nearOptimal_gap f best hw hp hpv
      · exact mul_nonneg (by norm_num) (mul_pos C.nu1_pos (pow_pos C.rho_pos _)).le
    _ = _ := by simp; ring

theorem RegularCovering.shallow_regret_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hw : WeaklyLipschitz f C.ell best)
    (H N : ℕ) (Y : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, if action C.nu1 C.rho Y n ∈ C.shallowGoodNodes f best H
      then best-f (C.toCovering.arm C.nu1 C.rho Y n) else 0) ≤
      ∑ h ∈ Finset.range H, 4*(C.nu1*C.rho^h)*(C.nearOptimalNodes f best h).card := by
  let a := action C.nu1 C.rho Y
  let D := fun h => 4*(C.nu1*C.rho^h)
  have hD (h : ℕ) : 0≤D h := mul_nonneg (by norm_num) (mul_pos C.nu1_pos (pow_pos C.rho_pos _)).le
  have hi (n : ℕ) : (if a n ∈ C.shallowGoodNodes f best H then
      best-f (C.toCovering.representative (a n)) else 0) ≤
      ∑ h ∈ Finset.range H, ∑ p ∈ C.nearOptimalNodes f best h, if a n=p then D h else 0 := by
    have hnon (h : ℕ) : 0≤∑ p ∈ C.nearOptimalNodes f best h, if a n=p then D h else 0 := by
      apply Finset.sum_nonneg; intro p hp; split_ifs <;> simp_all only [le_refl]
    split_ifs with he
    · obtain ⟨hl, hg⟩ := he
      have hgap := C.descendant_nearOptimal_gap f best hw hg (show a n <+: a n from ⟨[], by simp⟩)
      have hp := Finset.single_le_sum (s := C.nearOptimalNodes f best (a n).length)
        (f := fun p => if a n=p then D (a n).length else 0)
        (fun p _ => by dsimp only; split_ifs <;> simp_all only [le_refl]) hg
      have hh := Finset.single_le_sum (fun h _ => hnon h) (Finset.mem_range.mpr hl)
      dsimp only at hp
      rw [if_pos rfl] at hp
      exact hgap.trans (hp.trans hh)
    · exact Finset.sum_nonneg (fun h _ => hnon h)
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∑ h ∈ Finset.range H,
        ∑ p ∈ C.nearOptimalNodes f best h, if a n=p then D h else 0 :=
      Finset.sum_le_sum (fun n _ => hi n)
    _ = ∑ h ∈ Finset.range H, ∑ p ∈ C.nearOptimalNodes f best h,
        D h * (∑ n ∈ Finset.range N, if a n=p then (1:ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ ≤ ∑ h ∈ Finset.range H, ∑ _p ∈ C.nearOptimalNodes f best h, D h := by
      apply Finset.sum_le_sum; intro h hh
      apply Finset.sum_le_sum; intro p hp
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (action_singleton_count_le_one C.nu1 C.rho Y N p) (hD h)
    _ = _ := by simp [D, mul_comm]


/-- Poor-subtree contribution on each actual reward path. Its prefix
indicators are exactly the history's visits, including unvisited nodes. -/
theorem RegularCovering.bad_regret_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hw : WeaklyLipschitz f C.ell best)
    (H N : ℕ) (Y : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, if action C.nu1 C.rho Y n ∈ C.badSubtreeNodes f best H
      then best-f (C.toCovering.arm C.nu1 C.rho Y n) else 0) ≤
      ∑ h ∈ Finset.range H, ∑ p ∈ C.boundaryNodes f best h,
        4*(C.nu1*C.rho^h)*(visits (history C.nu1 C.rho Y N) p : ℝ) := by
  let a := action C.nu1 C.rho Y
  let D := fun h => 4*(C.nu1*C.rho^h)
  have hD (h : ℕ) : 0≤D h := mul_nonneg (by norm_num) (mul_pos C.nu1_pos (pow_pos C.rho_pos _)).le
  have hi (n : ℕ) : (if a n ∈ C.badSubtreeNodes f best H then
      best-f (C.toCovering.representative (a n)) else 0) ≤
      ∑ h ∈ Finset.range H, ∑ p ∈ C.boundaryNodes f best h, if p <+: a n then D h else 0 := by
    have hnon (h : ℕ) : 0≤∑ p ∈ C.boundaryNodes f best h, if p <+: a n then D h else 0 := by
      apply Finset.sum_nonneg; intro p hp; split_ifs <;> simp_all only [le_refl]
    split_ifs with he
    · obtain ⟨h, hl, p, hp, hpv⟩ := he
      have hgap := C.descendant_boundary_gap f best hw hp hpv
      have hsingle := Finset.single_le_sum (s := C.boundaryNodes f best h)
        (f := fun p => if p <+: a n then D h else 0)
        (fun p _ => by dsimp only; split_ifs <;> simp_all only [le_refl]) hp
      have hh := Finset.single_le_sum (fun h _ => hnon h) (Finset.mem_range.mpr hl)
      simp only [if_pos hpv] at hsingle
      exact hgap.trans (hsingle.trans hh)
    · exact Finset.sum_nonneg (fun h _ => hnon h)
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∑ h ∈ Finset.range H,
        ∑ p ∈ C.boundaryNodes f best h, if p <+: a n then D h else 0 :=
      Finset.sum_le_sum (fun n _ => hi n)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← sum_regionCount_eq_visits, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [regionCount, a, D]
      split_ifs <;> simp

/-- The actual pathwise three-term regret bound before expectation or depth
optimization. No partition, visit count or one-play property is assumed. -/
theorem RegularCovering.pathwise_regret_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hf : ∀x, f x≤best)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (H N : ℕ) (Y : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n))) ≤
      4*(C.nu1*C.rho^H)*N +
      (∑ h ∈ Finset.range H, 4*(C.nu1*C.rho^h)*(C.nearOptimalNodes f best h).card) +
      ∑ h ∈ Finset.range H, ∑ p ∈ C.boundaryNodes f best h,
        4*(C.nu1*C.rho^h)*(visits (history C.nu1 C.rho Y N) p : ℝ) := by
  rw [C.actual_regret_partition f best hf hbest H N Y]
  exact add_le_add (add_le_add (C.deep_regret_le f best hw H N Y)
    (C.shallow_regret_le f best hw H N Y)) (C.bad_regret_le f best hw H N Y)

/-- Source first-step simplification for the actual boundary nodes. -/
theorem RegularCovering.boundary_expected_visits {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hf : ∀ x, f x≤best) (hbest : regionSup f Set.univ=best)
    (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    {h : ℕ} {v : Node} (hv : v ∈ C.boundaryNodes f best h) (N : ℕ) :
    (∫ Y, (visits (history C.nu1 C.rho Y N) v : ℝ)
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      8*Real.log (max (N:ℝ) 2)/(C.nu1*C.rho^(h+1))^2+4 := by
  obtain ⟨hl, hp⟩ := C.boundaryNodes_poor f best hv
  have hD : 0<C.nu1*C.rho^(h+1) := mul_pos C.nu1_pos (pow_pos C.rho_pos _)
  have hpoor : C.nu1*C.rho^v.length < best-regionSup f (C.region v) := by rw [hl]; linarith
  have he := C.poor_region_expected_visits law f best hmean hf hbest hw hbound v hpoor N
  rw [hl] at he
  apply he.trans
  refine add_le_add ?_ (le_refl (4:ℝ))
  have hL : 0≤8*Real.log (max (N:ℝ) 2) := mul_nonneg (by norm_num)
    (Real.log_nonneg (le_max_of_le_right (by norm_num)))
  apply div_le_div_of_nonneg_left hL (sq_pos_of_pos hD)
  nlinarith

end BanditRLProof.HOO

