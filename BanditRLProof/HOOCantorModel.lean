import BanditRLProof.Algorithms.HOOExpectedVisits
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.List.GetD

/-! An infinite-arm, noisy HOO model on binary sequences. -/
namespace BanditRLProof.HOO.CantorModel
open MeasureTheory ProbabilityTheory

abbrev Arm := ℕ → Bool
noncomputable local instance : Dist Arm := PiNat.dist

def center (v : Node) : Arm := fun i => v.getD i false
def region (v : Node) : Set Arm := PiNat.cylinder (center v) v.length
noncomputable def ell (x y : Arm) : ℝ := dist x y

theorem center_child_of_lt (v : Node) (b : Bool) (i : ℕ) (hi : i < v.length) :
    center (child v b) i = center v i := by
  exact List.getD_append v [b] false i hi

@[simp] theorem center_child_last (v : Node) (b : Bool) : center (child v b) v.length = b := by
  simp [center, child]

theorem mem_child_iff (v : Node) (b : Bool) (x : Arm) :
    x ∈ region (child v b) ↔ x ∈ region v ∧ x v.length = b := by
  constructor
  · intro hx
    constructor
    · intro i hi
      have hh := hx i (by simpa only [child_length] using Nat.lt_succ_of_lt hi)
      rwa [center_child_of_lt v b i hi] at hh
    · simpa using hx v.length (by simp)
  · rintro ⟨hx, hb⟩ i hi
    have hlen : i < v.length+1 := by simpa only [child_length] using hi
    by_cases hil : i < v.length
    · rw [center_child_of_lt v b i hil]
      exact hx i hil
    · have he : i=v.length := by omega
      simpa only [he, center_child_last] using hb

theorem region_children (v : Node) : region v = region (child v false) ∪ region (child v true) := by
  ext x
  simp only [Set.mem_union, mem_child_iff]
  constructor
  · intro hx
    cases hb : x v.length
    · exact Or.inl ⟨hx, rfl⟩
    · exact Or.inr ⟨hx, rfl⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

theorem region_measurable (v : Node) : MeasurableSet (region v) := by
  change MeasurableSet {x : Arm | ∀ i, i < v.length → x i = center v i}
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const

theorem region_diameter (v : Node) (x : Arm) (hx : x ∈ region v)
    (y : Arm) (hy : y ∈ region v) : ell x y ≤ (1/2:ℝ)^v.length := by
  apply PiNat.mem_cylinder_iff_dist_le.mp
  intro i hi
  exact (hx i hi).trans (hy i hi).symm

theorem ball_subset_region (v : Node) :
    {y : Arm | ell (center v) y < (1/2:ℝ)^v.length} ⊆ region v := by
  intro y hy i hi
  exact (PiNat.apply_eq_of_dist_lt hy hi.le).symm

theorem region_disjoint {v w : Node} (hl : v.length=w.length) (hne : v≠w) :
    Disjoint (region v) (region w) := by
  apply Set.disjoint_left.mpr
  intro x hv hw
  apply hne
  apply List.ext_getElem hl
  intro i hi hj
  have hh := (hv i hi).symm.trans (hw i hj)
  simpa only [center, List.getD_eq_getElem v false hi, List.getD_eq_getElem w false hj] using hh

noncomputable def covering : RegularCovering Arm where
  region := region
  root := PiNat.cylinder_zero _
  children := region_children
  nonempty v := ⟨center v, PiNat.self_mem_cylinder _ _⟩
  measurable_region := region_measurable
  ell := ell
  ell_nonneg := PiNat.dist_nonneg
  ell_self := PiNat.dist_self
  nu1 := 1
  nu2 := 1
  rho := 1/2
  nu1_pos := by norm_num
  nu2_pos := by norm_num
  rho_pos := by norm_num
  rho_lt_one := by norm_num
  diameter_bound v x hx y hy := by simpa only [one_mul] using region_diameter v x hx y hy
  center := center
  center_mem v := PiNat.self_mem_cylinder _ _
  ball_subset v := by simpa only [one_mul] using ball_subset_region v
  balls_disjoint v w hl hn := by
    simp only [one_mul]
    exact (region_disjoint hl hn).mono (ball_subset_region v) (ball_subset_region w)

noncomputable def mean (x : Arm) : ℝ := if x 0 then 1/4 else 1/2

theorem mean_le_best (x : Arm) : mean x ≤ 1/2 := by unfold mean; split_ifs <;> norm_num

theorem first_coordinate_distance (x y : Arm) (h : x 0 ≠ y 0) : ell x y = 1 := by
  have hne : x ≠ y := fun he => h (congrFun he 0)
  have hz : PiNat.firstDiff x y = 0 := by
    by_contra hn
    exact h (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hn))
  simp only [ell, PiNat.dist_eq_of_ne hne, hz, pow_zero]

theorem weaklyLipschitz : WeaklyLipschitz mean ell (1/2) := by
  intro x y
  have he := PiNat.dist_nonneg x y
  by_cases hx : x 0 = true <;> by_cases hy : y 0 = true
  · simp [mean, hx, hy, ell, he]
  · simp [mean, hx, hy]
    positivity
  · have hd : ell x y = 1 := first_coordinate_distance x y (by simpa [hy] using hx)
    norm_num [mean, hx, hy, hd]
  · simpa [mean, hx, hy, max_eq_right (show 0 ≤ ell x y from he)] using he

noncomputable def bitReward (b : Bool) : Measure ℝ :=
  (1/2 : ENNReal) • Measure.dirac 0 +
    (1/2 : ENNReal) • Measure.dirac (if b then 1/2 else 1)

instance bitReward_probability (b : Bool) : IsProbabilityMeasure (bitReward b) := by
  constructor
  norm_num [bitReward, ENNReal.inv_two_add_inv_two]

noncomputable def bitKernel : Kernel Bool ℝ := Kernel.ofFunOfCountable bitReward
instance bitKernel_markov : IsMarkovKernel bitKernel := ⟨bitReward_probability⟩

noncomputable def law : Kernel Arm ℝ := bitKernel.comap (fun x => x 0) (measurable_pi_apply 0)
instance law_markov : IsMarkovKernel law := by unfold law; infer_instance

theorem law_bounded (x : Arm) : ∀ᵐ y ∂law x, y ∈ Set.Icc (0 : ℝ) 1 := by
  change ∀ᵐ y ∂bitReward (x 0), y ∈ Set.Icc (0 : ℝ) 1
  simp only [bitReward, ae_add_measure_iff]
  constructor
  · simp
  · split_ifs <;> norm_num

theorem law_zero_mass (x : Arm) : law x {0} = (1/2 : ENNReal) := by
  change bitReward (x 0) {0} = _
  cases hx : x 0 <;> norm_num [bitReward]

theorem law_not_dirac (x : Arm) (r : ℝ) : law x ≠ Measure.dirac r := by
  intro he
  have hh := law_zero_mass x
  rw [he] at hh
  by_cases hr : r=0 <;> norm_num [Measure.dirac_apply', hr] at hh
  all_goals
    have ht := congrArg ENNReal.toReal hh
    norm_num at ht

theorem law_mean (x : Arm) : (∫ y, y ∂law x) = mean x := by
  change (∫ y, y ∂bitReward (x 0)) = mean x
  unfold bitReward
  rw [integral_add_measure]
  · simp [integral_smul_measure, mean]
    split_ifs <;> norm_num
  · exact (integrable_dirac (by simp) : Integrable (fun y : ℝ => y) (Measure.dirac 0)).smul_measure (by norm_num)
  · exact (integrable_dirac (by simp) : Integrable (fun y : ℝ => y) (Measure.dirac _)).smul_measure (by norm_num)

theorem global_sup : regionSup mean Set.univ = 1/2 := by
  have hb : BddAbove (mean '' Set.univ) := ⟨1/2, by rintro y ⟨x, _, rfl⟩; exact mean_le_best x⟩
  apply le_antisymm
  · exact csSup_le ⟨mean (fun _ => false), ⟨_, Set.mem_univ _, rfl⟩⟩
      (by rintro y ⟨x, _, rfl⟩; exact mean_le_best x)
  · apply le_csSup hb
    exact ⟨fun _ => false, Set.mem_univ _, by norm_num [mean]⟩

def poorNode : Node := [true, false, false]

theorem poor_region_mean (x : Arm) (hx : x ∈ region poorNode) : mean x = 1/4 := by
  have hh := hx 0 (by decide)
  norm_num [center, poorNode] at hh
  simp [mean, hh]

theorem poor_sup : regionSup mean (region poorNode) = 1/4 := by
  have he : mean '' region poorNode = {(1/4 : ℝ)} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact poor_region_mean x hx
    · intro hy
      have hy' : y = 1/4 := hy
      refine ⟨center poorNode, PiNat.self_mem_cylinder _ _, ?_⟩
      rw [poor_region_mean _ (PiNat.self_mem_cylinder _ _), hy']
  simp only [regionSup, he, csSup_singleton]

/-- A concrete nontrivial poor region in the infinite-arm model consumes the
complete algorithm-to-expected-visits chain. -/
theorem expected_poor_visits (N : ℕ) :
    (∫ Y, (visits (history 1 (1/2) Y N) poorNode : ℝ)
      ∂trajectory 1 (1/2) (covering.toCovering.nodeLaw law)) ≤
      512 * Real.log (max (N:ℝ) 2) + 4 := by
  have hg : covering.nu1*covering.rho^poorNode.length <
      (1/2 : ℝ)-regionSup mean (covering.region poorNode) := by
    change 1*(1/2:ℝ)^3 < 1/2-regionSup mean (region poorNode)
    rw [poor_sup]
    norm_num
  have h := covering.poor_region_expected_visits law mean (1/2) law_mean mean_le_best global_sup
    weaklyLipschitz law_bounded poorNode hg N
  change (∫ Y, (visits (history 1 (1/2) Y N) poorNode : ℝ)
      ∂trajectory 1 (1/2) (covering.toCovering.nodeLaw law)) ≤
      8*Real.log (max (N:ℝ) 2)/((1/2)-regionSup mean (region poorNode)-1*(1/2)^3)^2+4 at h
  rw [poor_sup] at h
  norm_num at h
  nlinarith

end BanditRLProof.HOO.CantorModel
