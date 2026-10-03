import BanditRLProof.OnlineSubgradientDifferentiability
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.Convex.Join
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import BanditRLProof.OnlineNormalCone
noncomputable section
open Set Filter Topology
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SourceFiniteMax {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : EReal := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)

def SourceActiveSubgradientUnion {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : Set E :=
  {g | ∃ i, f i x = SourceFiniteMax f x ∧ g ∈ SourceSubdifferential (f i) x}

theorem active_subgradient_support_max
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (x : E) :
    SourceActiveSubgradientUnion f x ⊆ SourceSubdifferential (SourceFiniteMax f) x := by
  classical
  rintro g ⟨i, hi, hg⟩ y
  have hiy : f i y ≤ SourceFiniteMax f y :=
    Finset.le_sup' (fun j => f j y) (Finset.mem_univ i)
  rw [← hi]
  exact (hg y).trans hiy



theorem finiteMax_attained {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : ∃ i, SourceFiniteMax f x = f i x := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => f i x)
  exact ⟨i, he⟩

theorem finiteMax_point_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (hp : ∀ i, SourceProper (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i)) :
    ∃ a : ℝ, SourceFiniteMax f x = (a : EReal) := by
  obtain ⟨i, hi⟩ := finiteMax_attained f x
  exact ⟨(f i x).toReal, hi.trans (EReal.coe_toReal (ne_of_lt (hx i)) ((hp i).1 x)).symm⟩

theorem subgradient_iff_real_support (f : E → EReal)
    (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ effectiveDomain f) (g : E) :
    g ∈ SourceSubdifferential f x ↔
      ∀ y, f y ≠ ⊤ → (f x).toReal + inner ℝ g (y - x) ≤ (f y).toReal := by
  have hxf := EReal.coe_toReal (ne_of_lt hx) (hbot x)
  constructor
  · intro hg y hyt
    have hyf := EReal.coe_toReal hyt (hbot y)
    have hi := hg y
    rw [← hxf, ← hyf, ← EReal.coe_add] at hi
    exact EReal.coe_le_coe_iff.mp hi
  · intro hg y
    by_cases hyt : f y = ⊤
    · rw [hyt]
      exact le_top
    · have hyf := EReal.coe_toReal hyt (hbot y)
      change f x + (inner ℝ g (y - x) : EReal) ≤ f y
      rw [← hxf, ← hyf, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (hg y hyt)

theorem convex_sourceSubdifferential (f : E → EReal)
    (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ effectiveDomain f) :
    Convex ℝ (SourceSubdifferential f x) := by
  intro g hg k hk a b ha hb hab
  rw [subgradient_iff_real_support f hbot x hx] at hg hk ⊢
  intro y hyt
  have h1 := mul_le_mul_of_nonneg_left (hg y hyt) ha
  have h2 := mul_le_mul_of_nonneg_left (hk y hyt) hb
  simp only [inner_add_left, real_inner_smul_left]
  have hxsum : a * (f x).toReal + b * (f x).toReal = (f x).toReal := by
    rw [← add_mul, hab, one_mul]
  have hysum : a * (f y).toReal + b * (f y).toReal = (f y).toReal := by
    rw [← add_mul, hab, one_mul]
  nlinarith

theorem continuousAt_mem_domain_interior (f : E → EReal) (x : E)
    (hx : x ∈ effectiveDomain f) (hc : ContinuousAt f x) :
    x ∈ interior (effectiveDomain f) := by
  apply mem_interior_iff_mem_nhds.mpr
  exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hx)


theorem finiteMax_ne_bot {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (hp : ∀ i, SourceProper (f i)) (y : E) :
    SourceFiniteMax f y ≠ ⊥ := by
  obtain ⟨i, hi⟩ := finiteMax_attained f y
  rw [hi]
  exact (hp i).1 y

theorem convexHull_active_support_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (hp : ∀ i, SourceProper (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i)) :
    convexHull ℝ (SourceActiveSubgradientUnion f x) ⊆
      SourceSubdifferential (SourceFiniteMax f) x := by
  obtain ⟨a, ha⟩ := finiteMax_point_finite f hp x hx
  have hm : x ∈ effectiveDomain (SourceFiniteMax f) := by
    change SourceFiniteMax f x < ⊤
    rw [ha]
    exact EReal.coe_lt_top a
  exact convexHull_min (active_subgradient_support_max f x)
    (convex_sourceSubdifferential (SourceFiniteMax f) (finiteMax_ne_bot f hp) x hm)

theorem isClosed_sourceSubdifferential (f : E → EReal)
    (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ effectiveDomain f) :
    IsClosed (SourceSubdifferential f x) := by
  have he : SourceSubdifferential f x =
      ⋂ y : E, ⋂ (_hy : f y ≠ ⊤),
        {g : E | (f x).toReal + inner ℝ g (y - x) ≤ (f y).toReal} := by
    ext g
    simp only [mem_iInter, mem_setOf_eq]
    exact subgradient_iff_real_support f hbot x hx g
  rw [he]
  exact isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le (continuous_const.add (continuous_id.inner continuous_const)) continuous_const

theorem isCompact_sourceSubdifferential [FiniteDimensional ℝ E]
    (f : E → EReal) (hp : SourceProper f) (hf : IsConvexExtended f)
    (x : E) (hx : x ∈ interior (effectiveDomain f)) :
    IsCompact (SourceSubdifferential f x) := by
  obtain ⟨r, hr, K, hb⟩ := subgradients_locally_bounded f hp.1 hf x hx
  have hbound : SourceSubdifferential f x ⊆ Metric.closedBall 0 (K : ℝ) := by
    intro g hg
    have hgK := hb x (by simpa using hr) g hg
    simpa using hgK
  exact (isCompact_closedBall (0 : E) (K : ℝ)).of_isClosed_subset
    (isClosed_sourceSubdifferential f hp.1 x (interior_subset hx)) hbound


theorem isCompact_convexJoin (s t : Set E) (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  have he : convexJoin ℝ s t =
      (fun p : ℝ × (E × E) => (1 - p.1) • p.2.1 + p.1 • p.2.2) ''
        (Icc (0 : ℝ) 1 ×ˢ (s ×ˢ t)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, hz⟩ := mem_convexJoin.mp hz
      rw [segment_eq_image] at hz
      obtain ⟨a, ha, he⟩ := hz
      exact ⟨(a, x, y), ⟨ha, hx, hy⟩, he⟩
    · rintro ⟨⟨a, x, y⟩, ⟨ha, hx, hy⟩, rfl⟩
      apply mem_convexJoin.mpr
      refine ⟨x, hx, y, hy, ?_⟩
      rw [segment_eq_image]
      exact ⟨a, ha, rfl⟩
  rw [he]
  exact (isCompact_Icc.prod (hs.prod ht)).image (by fun_prop)

theorem isCompact_convexHull_finite_convex_union {ι : Type*}
    (s : ι → Set E) (F : Finset ι)
    (hc : ∀ i ∈ F, Convex ℝ (s i)) (hk : ∀ i ∈ F, IsCompact (s i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ F, s i)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    have hcF : ∀ j ∈ F, Convex ℝ (s j) := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hkF : ∀ j ∈ F, IsCompact (s j) := fun j hj => hk j (Finset.mem_insert_of_mem hj)
    have hci := hc i (Finset.mem_insert_self i F)
    have hki := hk i (Finset.mem_insert_self i F)
    have hkU := ih hcF hkF
    have he : (⋃ j ∈ insert i F, s j) = s i ∪ (⋃ j ∈ F, s j) := by
      ext z
      simp
    rw [he]
    by_cases hsi : (s i).Nonempty
    · by_cases hU : (⋃ j ∈ F, s j).Nonempty
      · rw [convexHull_union hsi hU, hci.convexHull_eq]
        exact isCompact_convexJoin _ _ hki hkU
      · rw [not_nonempty_iff_eq_empty.mp hU, union_empty, hci.convexHull_eq]
        exact hki
    · rw [not_nonempty_iff_eq_empty.mp hsi, empty_union]
      exact hkU


theorem isCompact_active_subgradient_hull [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal)
    (hp : ∀ i, SourceProper (f i)) (hc : ∀ i, IsConvexExtended (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i))
    (hcont : ∀ i, ContinuousAt (f i) x) :
    IsCompact (convexHull ℝ (SourceActiveSubgradientUnion f x)) := by
  classical
  let s : ι → Set E := fun i => if f i x = SourceFiniteMax f x then
    SourceSubdifferential (f i) x else ∅
  have he : SourceActiveSubgradientUnion f x = ⋃ i ∈ (Finset.univ : Finset ι), s i := by
    ext g
    simp only [SourceActiveSubgradientUnion, mem_setOf_eq, Finset.mem_univ, mem_iUnion,
      exists_prop, true_and]
    constructor
    · rintro ⟨i, hi, hg⟩
      exact ⟨i, by simpa [s, hi] using hg⟩
    · rintro ⟨i, hg⟩
      by_cases hi : f i x = SourceFiniteMax f x
      · exact ⟨i, hi, by simpa [s, hi] using hg⟩
      · simp [s, hi] at hg
  rw [he]
  apply isCompact_convexHull_finite_convex_union
  · intro i _
    by_cases hi : f i x = SourceFiniteMax f x
    · simpa [s, hi] using convex_sourceSubdifferential (f i) (hp i).1 x (hx i)
    · simpa [s, hi] using (convex_empty : Convex ℝ (∅ : Set E))
  · intro i _
    by_cases hi : f i x = SourceFiniteMax f x
    · simpa [s, hi] using isCompact_sourceSubdifferential (f i) (hp i) (hc i) x
        (continuousAt_mem_domain_interior (f i) x (hx i) (hcont i))
    · simp [s, hi]


theorem continuousAt_finite_toReal (f : E → EReal) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hc : ContinuousAt f x) :
    ContinuousAt (fun y => (f y).toReal) x := by
  have ho : IsOpen ({(⊥ : EReal), ⊤}ᶜ : Set EReal) := by
    exact (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hm : f x ∈ ({(⊥ : EReal), ⊤}ᶜ : Set EReal) := by simp [ht, hb]
  exact (EReal.continuousOn_toReal.continuousAt (ho.mem_nhds hm)).comp hc

theorem max_support_displacement_compare {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (hp : ∀ i, SourceProper (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i))
    (y : E) (i : ι) (hy : y ∈ effectiveDomain (f i))
    (hi : SourceFiniteMax f y = f i y) (g k : E)
    (hg : g ∈ SourceSubdifferential (SourceFiniteMax f) x)
    (hk : k ∈ SourceSubdifferential (f i) y) :
    inner ℝ g (y - x) ≤ inner ℝ k (y - x) := by
  obtain ⟨a, ha⟩ := finiteMax_point_finite f hp x hx
  have hix := EReal.coe_toReal (ne_of_lt (hx i)) ((hp i).1 x)
  have hiy := EReal.coe_toReal (ne_of_lt hy) ((hp i).1 y)
  have hg1 := hg y
  have hk1 := hk x
  rw [ha, hi, ← hiy, ← EReal.coe_add] at hg1
  rw [← hiy, ← hix, ← EReal.coe_add] at hk1
  have h1 := EReal.coe_le_coe_iff.mp hg1
  have h2 := EReal.coe_le_coe_iff.mp hk1
  have hmax : (f i x).toReal ≤ a := by
    apply EReal.coe_le_coe_iff.mp
    rw [hix, ← ha]
    exact Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)
  simp only [inner_sub_right] at h1 h2 ⊢
  linarith


theorem max_subgradient_direction_witness [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal)
    (hp : ∀ i, SourceProper (f i)) (hc : ∀ i, IsConvexExtended (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i))
    (hcont : ∀ i, ContinuousAt (f i) x) (g d : E)
    (hg : g ∈ SourceSubdifferential (SourceFiniteMax f) x) :
    ∃ k ∈ SourceActiveSubgradientUnion f x, inner ℝ g d ≤ inner ℝ k d := by
  classical
  have hix : ∀ i, x ∈ interior (effectiveDomain (f i)) := fun i =>
    continuousAt_mem_domain_interior (f i) x (hx i) (hcont i)
  let ys : ℕ → E := fun n => x + (1 / ((n : ℝ) + 1)) • d
  have ht : Tendsto ys atTop (𝓝 x) := by
    have h := (tendsto_const_nhds (x := x)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul (tendsto_const_nhds (x := d)))
    simpa [ys] using h
  have hin : ∀ᶠ n in atTop, ∀ i, ys n ∈ interior (effectiveDomain (f i)) := by
    apply eventually_all.mpr
    intro i
    exact ht.eventually (isOpen_interior.mem_nhds (hix i))
  have hb0 : ∀ i, ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ y in 𝓝 x, ∀ q ∈ SourceSubdifferential (f i) y, ‖q‖ ≤ K := by
    intro i
    obtain ⟨r, hr, K, hb⟩ := subgradients_locally_bounded (f i) (hp i).1 (hc i) x (hix i)
    refine ⟨K, K.2, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    exact hb y hy
  choose K hK hKB using hb0
  have hbseq : ∀ᶠ n in atTop, ∀ i, ∀ q ∈ SourceSubdifferential (f i) (ys n), ‖q‖ ≤ K i := by
    exact eventually_all.mpr (fun i => ht.eventually (hKB i))
  choose idx hidx using (fun n => finiteMax_attained f (ys n))
  have hq : ∀ n, ∃ q : E, ys n ∈ interior (effectiveDomain (f (idx n))) →
      q ∈ SourceSubdifferential (f (idx n)) (ys n) := by
    intro n
    by_cases hi : ys n ∈ interior (effectiveDomain (f (idx n)))
    · obtain ⟨q, hq⟩ := subgradient_exists_of_domain_interior
        (f (idx n)) (hp (idx n)) (hc (idx n)) (ys n) hi
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose qs hqs using hq
  have hsub : ∀ᶠ n in atTop, qs n ∈ SourceSubdifferential (f (idx n)) (ys n) := by
    filter_upwards [hin] with n hn
    exact hqs n (hn (idx n))
  let B : ℝ := ∑ i, K i
  have hnorm : ∀ᶠ n in atTop, qs n ∈ Metric.closedBall (0 : E) B := by
    filter_upwards [hsub, hbseq] with n hn hb
    have hKle : K (idx n) ≤ B := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ (idx n))
    have hh := (hb (idx n) (qs n) hn).trans hKle
    simpa using hh
  obtain ⟨k, hkB, φ, hφ, hkt⟩ := (isCompact_closedBall (0 : E) B).tendsto_subseq' hnorm.frequently
  have hfreq : ∃ᶠ n in atTop, ∃ i, idx (φ n) = i :=
    Frequently.of_forall (fun n => ⟨idx (φ n), rfl⟩)
  obtain ⟨i, hi⟩ := frequently_exists.mp hfreq
  let l : Filter ℕ := atTop ⊓ 𝓟 {n | idx (φ n) = i}
  haveI : NeBot l := frequently_iff_neBot.mp hi
  have hilt : ∀ᶠ n in l, idx (φ n) = i := by
    rw [eventually_inf_principal]
    exact Eventually.of_forall (fun _ h => h)
  have hyt : Tendsto (ys ∘ φ) l (𝓝 x) := (ht.comp hφ.tendsto_atTop).mono_left inf_le_left
  have hqt : Tendsto (qs ∘ φ) l (𝓝 k) := hkt.mono_left inf_le_left
  have hsubφ : ∀ᶠ n in l, qs (φ n) ∈ SourceSubdifferential (f i) (ys (φ n)) := by
    have hh : ∀ᶠ n in l, qs (φ n) ∈ SourceSubdifferential (f (idx (φ n))) (ys (φ n)) :=
      (hφ.tendsto_atTop.eventually hsub).filter_mono inf_le_left
    filter_upwards [hh, hilt] with n hn hi
    simpa only [hi] using hn
  have hkr : k ∈ SourceSubdifferential (f i) x :=
    subgradient_limit_of_continuousAt l (f i) (hp i).1 x k (hix i)
      (continuousAt_finite_toReal (f i) x (ne_of_lt (hx i)) ((hp i).1 x) (hcont i))
      (ys ∘ φ) (qs ∘ φ) hyt hqt hsubφ
  have hactive : f i x = SourceFiniteMax f x := by
    apply le_antisymm
    · exact Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)
    · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun j => f j x)).mpr
      intro j _
      apply le_of_tendsto_of_tendsto ((hcont j).tendsto.comp hyt) ((hcont i).tendsto.comp hyt)
      filter_upwards [hilt] with n hi
      have hmax : f j (ys (φ n)) ≤ SourceFiniteMax f (ys (φ n)) :=
        Finset.le_sup' (fun j => f j (ys (φ n))) (Finset.mem_univ j)
      simpa only [hidx (φ n), hi, Function.comp_apply] using hmax
  refine ⟨k, ⟨i, hactive, hkr⟩, ?_⟩
  have hcomp : ∀ᶠ n in atTop, inner ℝ g d ≤ inner ℝ (qs n) d := by
    filter_upwards [hsub, hin] with n hn hi
    have he := max_support_displacement_compare f hp x hx (ys n) (idx n)
      (interior_subset (hi (idx n))) (hidx n) g (qs n) hg hn
    have htpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [ys, add_sub_cancel_left, real_inner_smul_right] at he
    exact le_of_mul_le_mul_left he htpos
  have hcompl : ∀ᶠ n in l, inner ℝ g d ≤ inner ℝ (qs (φ n)) d :=
    (hφ.tendsto_atTop.eventually hcomp).filter_mono inf_le_left
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (hqt.inner (tendsto_const_nhds (x := d))) hcompl


theorem theorem_2_26 [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal)
    (hp : ∀ i, SourceProper (f i)) (hc : ∀ i, IsConvexExtended (f i))
    (x : E) (hx : ∀ i, x ∈ effectiveDomain (f i))
    (hcont : ∀ i, ContinuousAt (f i) x) :
    SourceSubdifferential (SourceFiniteMax f) x =
      convexHull ℝ (SourceActiveSubgradientUnion f x) := by
  apply Subset.antisymm
  · intro g hg
    by_contra hnot
    obtain ⟨L, c, hL, hgL⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (SourceActiveSubgradientUnion f x))
      (isCompact_active_subgradient_hull f hp hc x hx hcont).isClosed hnot
    let d : E := (InnerProductSpace.toDual ℝ E).symm L
    have hLd (v : E) : inner ℝ v d = L v := by
      dsimp only [d]
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    obtain ⟨k, hk, hdir⟩ := max_subgradient_direction_witness f hp hc x hx hcont g d hg
    rw [hLd, hLd] at hdir
    have hkL := hL k (subset_convexHull ℝ (SourceActiveSubgradientUnion f x) hk)
    linarith
  · exact convexHull_active_support_max f hp x hx


end BanditRL.OnlineConvex

namespace MaximumProbe
open BanditRL.OnlineConvex Set
noncomputable def family (i : Bool) (y : ℝ) : EReal := if i then (y : EReal) else ((-y : ℝ) : EReal)

theorem family_proper (i : Bool) : SourceProper (family i) := by
  constructor
  · intro y
    cases i <;> simp [family]
  · exact ⟨0, 0, by cases i <;> simp [family]⟩

theorem family_domain (i : Bool) (x : ℝ) : x ∈ effectiveDomain (family i) := by
  cases i
  · change ((-x : ℝ) : EReal) < ⊤
    exact EReal.coe_lt_top (-x)
  · change (x : EReal) < ⊤
    exact EReal.coe_lt_top x

theorem family_convex (i : Bool) : IsConvexExtended (family i) := by
  rw [convexExtended_iff_toReal (family i) (family_proper i).1]
  have hd : effectiveDomain (family i) = univ := eq_univ_of_forall (family_domain i)
  rw [hd]
  cases i
  · change ConvexOn ℝ univ (fun y : ℝ => (((-y : ℝ) : EReal)).toReal)
    simpa only [EReal.toReal_coe, Pi.neg_apply, id_eq] using
      (concaveOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))).neg
  · change ConvexOn ℝ univ (fun y : ℝ => (y : EReal).toReal)
    simpa only [EReal.toReal_coe, id_eq] using
      (convexOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ)))

theorem family_continuous (i : Bool) (x : ℝ) : ContinuousAt (family i) x := by
  cases i
  · change ContinuousAt (fun y : ℝ => ((-y : ℝ) : EReal)) x
    exact (continuous_coe_real_ereal.comp continuous_neg).continuousAt
  · change ContinuousAt ((↑) : ℝ → EReal) x
    exact continuous_coe_real_ereal.continuousAt

theorem affine_support (a x : ℝ) :
    SourceSubdifferential (fun y : ℝ => ((a * y : ℝ) : EReal)) x = {a} := by
  ext g
  change (∀ y, ((a * x : ℝ) : EReal) + (inner ℝ g (y - x) : EReal) ≤ ((a * y : ℝ) : EReal)) ↔ g = a
  constructor
  · intro hg
    have h1 := hg (x + 1)
    have h2 := hg (x - 1)
    rw [← EReal.coe_add] at h1 h2
    have h1r := EReal.coe_le_coe_iff.mp h1
    have h2r := EReal.coe_le_coe_iff.mp h2
    change a*x + (x+1-x)*g ≤ a*(x+1) at h1r
    change a*x + (x-1-x)*g ≤ a*(x-1) at h2r
    nlinarith
  · intro hg
    subst g
    intro y
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    change a*x + (y-x)*a ≤ a*y
    nlinarith

theorem maximum_zero : SourceFiniteMax family 0 = 0 := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun i => family i 0)).mpr
    intro i _
    cases i <;> simp [family]
  · have h := Finset.le_sup' (fun i => family i 0) (Finset.mem_univ true)
    change family true 0 ≤ SourceFiniteMax family 0 at h
    simpa only [family, if_true] using h

theorem tie_active_union : SourceActiveSubgradientUnion family 0 = {(-1 : ℝ), 1} := by
  have hs (i : Bool) : SourceSubdifferential (family i) 0 = {if i then (1 : ℝ) else -1} := by
    cases i
    · simpa [family] using affine_support (-1) 0
    · simpa [family] using affine_support 1 0
  ext g
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq, maximum_zero]
  constructor
  · rintro ⟨i, hi, hg⟩
    cases i <;> simp_all [hs, family]
  · intro hg
    rcases hg with h | h
    · exact ⟨false, by simp [family], by simpa [hs] using h⟩
    · exact ⟨true, by simp [family], by simpa [hs] using h⟩

theorem full_tie_hull_canary :
    SourceSubdifferential (SourceFiniteMax family) 0 = convexHull ℝ {(-1 : ℝ), 1} := by
  simpa only [tie_active_union] using theorem_2_26 family family_proper family_convex 0
    (fun i => family_domain i 0) (fun i => family_continuous i 0)



theorem full_tie_interval_canary :
    SourceSubdifferential (SourceFiniteMax family) 0 = Icc (-1 : ℝ) 1 := by
  rw [full_tie_hull_canary, convexHull_pair, segment_eq_Icc (by norm_num)]

theorem mixture_and_rejection_canary :
    (1 / 2 : ℝ) ∈ SourceSubdifferential (SourceFiniteMax family) 0 ∧
    (1 / 2 : ℝ) ∉ SourceActiveSubgradientUnion family 0 ∧
    (2 : ℝ) ∉ SourceSubdifferential (SourceFiniteMax family) 0 := by
  norm_num [full_tie_interval_canary, tie_active_union]

theorem maximum_two : SourceFiniteMax family 2 = (2 : EReal) := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun i => family i 2)).mpr
    intro i _
    cases i <;> norm_num [family]
  · have h := Finset.le_sup' (fun i => family i 2) (Finset.mem_univ true)
    change family true 2 ≤ SourceFiniteMax family 2 at h
    simpa only [family, if_true] using h

theorem inactive_union_canary : SourceActiveSubgradientUnion family 2 = {(1 : ℝ)} := by
  have hs (i : Bool) : SourceSubdifferential (family i) 2 = {if i then (1 : ℝ) else -1} := by
    cases i
    · simpa [family] using affine_support (-1) 2
    · simpa [family] using affine_support 1 2
  ext g
  simp only [SourceActiveSubgradientUnion, mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hg⟩
    cases i
    · norm_num [family, maximum_two] at hi
    · simpa only [hs, if_true] using hg
  · intro hg
    refine ⟨true, ?_, ?_⟩
    · simp [family, maximum_two]
    · simpa only [hs, if_true] using hg

theorem strict_active_canary :
    SourceSubdifferential (SourceFiniteMax family) 2 = {(1 : ℝ)} ∧
    (-1 : ℝ) ∉ SourceSubdifferential (SourceFiniteMax family) 2 := by
  have he := theorem_2_26 family family_proper family_convex 2
    (fun i => family_domain i 2) (fun i => family_continuous i 2)
  rw [inactive_union_canary, convexHull_singleton] at he
  exact ⟨he, by rw [he]; norm_num⟩

#print axioms full_tie_hull_canary
#print axioms full_tie_interval_canary
#print axioms mixture_and_rejection_canary
#print axioms strict_active_canary
end MaximumProbe

namespace MaximumExtendedProbe
open BanditRL.OnlineConvex Set Filter Topology
noncomputable def constrained (_ : Unit) : ℝ → EReal := extendedIndicator (Icc (-1 : ℝ) 1)

theorem constrained_proper (i : Unit) : SourceProper (constrained i) :=
  sourceProper_indicator_iff _ |>.mpr ⟨0, by norm_num⟩

theorem constrained_convex (i : Unit) : IsConvexExtended (constrained i) :=
  convex_indicator_iff _ |>.mpr (convex_Icc (-1 : ℝ) 1)

theorem constrained_domain (i : Unit) : (0 : ℝ) ∈ effectiveDomain (constrained i) := by
  rw [constrained, effectiveDomain_indicator]
  norm_num

theorem constrained_continuous (i : Unit) : ContinuousAt (constrained i) (0 : ℝ) := by
  have he : constrained i =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : EReal)) := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with y hy
    simp only [constrained, extendedIndicator, if_pos (show y ∈ Icc (-1 : ℝ) 1 from ⟨hy.1.le, hy.2.le⟩)]
  exact continuousAt_const.congr_of_eventuallyEq he.symm

theorem singleton_max (y : ℝ) : SourceFiniteMax constrained y = constrained () y := by
  obtain ⟨i, hi⟩ := finiteMax_attained constrained y
  cases i
  exact hi

theorem singleton_extended_domain_canary :
    SourceSubdifferential (SourceFiniteMax constrained) 0 = {(0 : ℝ)} ∧
    SourceFiniteMax constrained 2 = ⊤ := by
  have hs : SourceSubdifferential (constrained ()) 0 = {(0 : ℝ)} := by
    have hi : (0 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) := by
      rw [interior_Icc]
      norm_num
    rw [constrained, indicator_subdifferential_eq_normalCone _ ⟨0, by norm_num⟩ (convex_Icc _ _),
      normalCone_interior_eq_zero _ ⟨0, by norm_num⟩ (convex_Icc _ _) 0 hi]
  have hU : SourceActiveSubgradientUnion constrained 0 = {(0 : ℝ)} := by
    ext g
    simp only [SourceActiveSubgradientUnion, mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hg⟩
      cases i
      simpa only [hs] using hg
    · intro hg
      exact ⟨(), (singleton_max 0).symm, by simpa only [hs] using hg⟩
  have he := theorem_2_26 constrained constrained_proper constrained_convex 0
    constrained_domain constrained_continuous
  rw [hU, convexHull_singleton] at he
  refine ⟨he, ?_⟩
  rw [singleton_max]
  norm_num [constrained, extendedIndicator]

#print axioms singleton_extended_domain_canary
end MaximumExtendedProbe
