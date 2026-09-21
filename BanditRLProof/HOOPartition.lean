import BanditRLProof.HOODimension

/-! Source Theorem 6's actual covering-tree partition. Boundary nodes are
children of near-optimal parents which fail the next-level near-optimal test. -/
namespace BanditRLProof.HOO
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

@[simp] theorem RegularCovering.mem_nearOptimalNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (v : Node) (h : ℕ) :
    v ∈ C.nearOptimalNodes f best h ↔
      v.length=h ∧ best-regionSup f (C.region v) ≤ 2*(C.nu1*C.rho^h) := by
  classical
  simp [nearOptimalNodes]

theorem RegularCovering.root_nearOptimal {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ)
    (hbest : regionSup f Set.univ = best) : [] ∈ C.nearOptimalNodes f best 0 := by
  rw [C.mem_nearOptimalNodes]
  simp only [List.length_nil, C.root, hbest, sub_self, pow_zero, mul_one, true_and]
  exact mul_nonneg (by norm_num) C.nu1_pos.le

theorem RegularCovering.nearOptimal_prefix {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hf : ∀x, f x ≤ best)
    {v w : Node} (hp : v <+: w) (hw : w ∈ C.nearOptimalNodes f best w.length) :
    v ∈ C.nearOptimalNodes f best v.length := by
  rw [C.mem_nearOptimalNodes] at hw ⊢
  have hs : regionSup f (C.region w) ≤ regionSup f (C.region v) := by
    apply csSup_le_csSup
    · exact ⟨best, by rintro _ ⟨x, _, rfl⟩; exact hf x⟩
    · exact (C.nonempty w).image f
    · exact Set.image_mono (C.toCovering.descendant_subset hp)
  have hd := mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one C.rho_pos.le C.rho_lt_one.le hp.length_le) C.nu1_pos.le
  exact ⟨rfl, by linarith [hw.2]⟩

/-- Indexed by the parent's depth: this is source J_(h+1). -/
noncomputable def RegularCovering.boundaryNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (h : ℕ) : Finset Node :=
  ((C.nearOptimalNodes f best h ×ˢ (Finset.univ : Finset Bool)).image
    (fun p => child p.1 p.2)).filter (fun v => v ∉ C.nearOptimalNodes f best (h+1))

theorem RegularCovering.mem_boundaryNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (h : ℕ) (v : Node) :
    v ∈ C.boundaryNodes f best h ↔
      (∃ p ∈ C.nearOptimalNodes f best h, ∃ b, child p b=v) ∧
        v ∉ C.nearOptimalNodes f best (h+1) := by
  classical
  simp [boundaryNodes, Finset.mem_image, Prod.exists, and_assoc]

theorem RegularCovering.boundaryNodes_card_le {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (h : ℕ) :
    (C.boundaryNodes f best h).card ≤ 2*(C.nearOptimalNodes f best h).card := by
  unfold boundaryNodes
  calc
    _ ≤ _ := Finset.card_filter_le _ _
    _ ≤ _ := Finset.card_image_le
    _ = _ := by simp [Finset.card_product, Nat.mul_comm]

theorem RegularCovering.boundaryNodes_poor {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) {h : ℕ} {v : Node}
    (hv : v ∈ C.boundaryNodes f best h) :
    v.length=h+1 ∧ 2*(C.nu1*C.rho^(h+1)) < best-regionSup f (C.region v) := by
  obtain ⟨⟨p, hp, b, rfl⟩, hn⟩ := (C.mem_boundaryNodes f best h v).mp hv
  have hl := ((C.mem_nearOptimalNodes f best p h).mp hp).1
  have hc : (child p b).length=h+1 := by simp [hl]
  exact ⟨hc, lt_of_not_ge (fun hh => hn ((C.mem_nearOptimalNodes _ _ _ _).mpr ⟨hc, hh⟩))⟩

/-- Any word either lies below a good depth-H prefix, is itself a shallow
near-optimal word, or lies below a first bad child of a near-optimal parent. -/
theorem RegularCovering.node_partition_cover {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ)
    (hbest : regionSup f Set.univ=best) (H : ℕ) (v : Node) :
    (∃ p ∈ C.nearOptimalNodes f best H, p <+: v) ∨
    (v.length<H ∧ v ∈ C.nearOptimalNodes f best v.length) ∨
    (∃ h < H, ∃ p ∈ C.boundaryNodes f best h, p <+: v) := by
  classical
  let k := min H v.length
  have hk : k ≤ v.length := min_le_right _ _
  have htake (i : ℕ) (hi : i≤v.length) : (v.take i).length=i := by simp [hi]
  have hpref (i : ℕ) : v.take i <+: v := ⟨v.drop i, List.take_append_drop i v⟩
  by_cases hg : v.take k ∈ C.nearOptimalNodes f best k
  · by_cases hH : H≤v.length
    · exact Or.inl ⟨v.take k, by simpa [k, min_eq_left hH] using hg, hpref k⟩
    · right; left
      exact ⟨lt_of_not_ge hH, by simpa [k, min_eq_right (le_of_not_ge hH)] using hg⟩
  · have hex : ∃ i : ℕ, v.take i ∉ C.nearOptimalNodes f best i := ⟨k, hg⟩
    let j := Nat.find hex
    have hj : j≤k := Nat.find_min' hex hg
    have hjbad : v.take j ∉ C.nearOptimalNodes f best j := Nat.find_spec hex
    have hjpos : 0<j := by
      by_contra hn
      have he : j=0 := by omega
      have hr := C.root_nearOptimal f best hbest
      simp only [he, List.take_zero] at hjbad
      exact hjbad hr
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
    have hil : i<v.length := by omega
    have higood : v.take i ∈ C.nearOptimalNodes f best i := by
      by_contra hn
      exact Nat.find_min hex (show i<j by omega) hn
    have hb : child (v.take i) v[i] ∈ C.boundaryNodes f best i := by
      apply (C.mem_boundaryNodes f best i _).mpr
      refine ⟨⟨v.take i, higood, v[i], rfl⟩, ?_⟩
      simpa only [hi, List.take_succ_eq_append_getElem hil, child] using hjbad
    right; right
    refine ⟨i, by have := min_le_left H v.length; omega, child (v.take i) v[i], hb, ?_⟩
    simpa only [List.take_succ_eq_append_getElem hil, child] using hpref (i+1)

/-- The deep-good and shallow-good regret bounds use Lemma 3 on the actual
representative in a descendant region. -/
theorem RegularCovering.descendant_nearOptimal_gap {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hw : WeaklyLipschitz f C.ell best)
    {p v : Node} {h : ℕ} (hp : p ∈ C.nearOptimalNodes f best h) (hv : p <+: v) :
    best-f (C.toCovering.representative v) ≤ 4*(C.nu1*C.rho^h) := by
  obtain ⟨hl, hg⟩ := (C.mem_nearOptimalNodes _ _ _ _).mp hp
  have hy := C.toCovering.descendant_subset hv (C.toCovering.representative_mem v)
  have hh := C.region_near_optimal f best 2 p hw (by simpa only [hl] using hg) _ hy
  norm_num only [hl, mul_one, max_eq_left (by norm_num : (3:ℝ)≤4)] at hh
  exact hh

/-- Poor subtrees inherit their parent's gap bound, not the poor child's gap. -/
theorem RegularCovering.descendant_boundary_gap {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hw : WeaklyLipschitz f C.ell best)
    {p v : Node} {h : ℕ} (hp : p ∈ C.boundaryNodes f best h) (hv : p <+: v) :
    best-f (C.toCovering.representative v) ≤ 4*(C.nu1*C.rho^h) := by
  obtain ⟨⟨q, hq, b, rfl⟩, _⟩ := (C.mem_boundaryNodes _ _ _ _).mp hp
  exact C.descendant_nearOptimal_gap f best hw hq
    ((show q <+: child q b from ⟨[b], rfl⟩).trans hv)


private theorem prefix_of_prefixes_length {p q v : Node} (hp : p <+: v) (hq : q <+: v)
    (hl : p.length≤q.length) : p <+: q := by
  rcases List.prefix_or_prefix_of_prefix hp hq with he | he
  · exact he
  · have hh : q=p := he.eq_of_length (Nat.le_antisymm he.length_le hl)
    rw [hh]

def RegularCovering.deepGoodNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (H : ℕ) : Set Node :=
  {v | ∃ p ∈ C.nearOptimalNodes f best H, p <+: v}

def RegularCovering.shallowGoodNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (H : ℕ) : Set Node :=
  {v | v.length<H ∧ v ∈ C.nearOptimalNodes f best v.length}

def RegularCovering.badSubtreeNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (H : ℕ) : Set Node :=
  {v | ∃ h<H, ∃ p ∈ C.boundaryNodes f best h, p <+: v}

theorem RegularCovering.deep_shallow_disjoint {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (H : ℕ) :
    Disjoint (C.deepGoodNodes f best H) (C.shallowGoodNodes f best H) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨p, hp, hpv⟩ ⟨hv, _⟩
  have hl := ((C.mem_nearOptimalNodes _ _ _ _).mp hp).1
  have := hpv.length_le
  omega

theorem RegularCovering.deep_bad_disjoint {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hf : ∀x, f x≤best) (H : ℕ) :
    Disjoint (C.deepGoodNodes f best H) (C.badSubtreeNodes f best H) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨q, hq, hqv⟩ ⟨h, hh, p, hp, hpv⟩
  have hql := ((C.mem_nearOptimalNodes _ _ _ _).mp hq).1
  have hpl := (C.boundaryNodes_poor f best hp).1
  have hpq := prefix_of_prefixes_length hpv hqv (by omega)
  have he := C.nearOptimal_prefix f best hf hpq (by simpa only [hql] using hq)
  exact ((C.mem_boundaryNodes _ _ _ _).mp hp).2 (by simpa only [hpl] using he)

theorem RegularCovering.shallow_bad_disjoint {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hf : ∀x, f x≤best) (H : ℕ) :
    Disjoint (C.shallowGoodNodes f best H) (C.badSubtreeNodes f best H) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨_, hv⟩ ⟨h, _, p, hp, hpv⟩
  have he := C.nearOptimal_prefix f best hf hpv hv
  have hpl := (C.boundaryNodes_poor f best hp).1
  exact ((C.mem_boundaryNodes _ _ _ _).mp hp).2 (by simpa only [hpl] using he)

/-- Exact three-part identity for the actual HOO action trace, before any
inequality or expectation. Cover and disjointness are derived above. -/
theorem RegularCovering.actual_regret_partition {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (hf : ∀x, f x≤best)
    (hbest : regionSup f Set.univ=best) (H N : ℕ) (Y : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n))) =
    (∑ n ∈ Finset.range N, if action C.nu1 C.rho Y n ∈ C.deepGoodNodes f best H
      then best-f (C.toCovering.arm C.nu1 C.rho Y n) else 0) +
    (∑ n ∈ Finset.range N, if action C.nu1 C.rho Y n ∈ C.shallowGoodNodes f best H
      then best-f (C.toCovering.arm C.nu1 C.rho Y n) else 0) +
    (∑ n ∈ Finset.range N, if action C.nu1 C.rho Y n ∈ C.badSubtreeNodes f best H
      then best-f (C.toCovering.arm C.nu1 C.rho Y n) else 0) := by
  classical
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  let v := action C.nu1 C.rho Y n
  have hd := Set.disjoint_left.mp (C.deep_shallow_disjoint f best H)
  have hb := Set.disjoint_left.mp (C.deep_bad_disjoint f best hf H)
  have hs := Set.disjoint_left.mp (C.shallow_bad_disjoint f best hf H)
  rcases C.node_partition_cover f best hbest H v with h | h | h
  · have h1 : v ∈ C.deepGoodNodes f best H := h
    have h2 : v ∉ C.shallowGoodNodes f best H := fun he => hd h1 he
    have h3 : v ∉ C.badSubtreeNodes f best H := fun he => hb h1 he
    simp only [v] at h1 h2 h3
    simp [h1, h2, h3]
  · have h2 : v ∈ C.shallowGoodNodes f best H := h
    have h1 : v ∉ C.deepGoodNodes f best H := fun he => hd he h2
    have h3 : v ∉ C.badSubtreeNodes f best H := fun he => hs h2 he
    simp only [v] at h1 h2 h3
    simp [h1, h2, h3]
  · have h3 : v ∈ C.badSubtreeNodes f best H := h
    have h1 : v ∉ C.deepGoodNodes f best H := fun he => hb he h3
    have h2 : v ∉ C.shallowGoodNodes f best H := fun he => hs he h3
    simp only [v] at h1 h2 h3
    simp [h1, h2, h3]

end BanditRLProof.HOO

