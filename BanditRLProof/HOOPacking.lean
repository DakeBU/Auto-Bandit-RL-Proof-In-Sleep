import BanditRLProof.HOOLevels
import Mathlib.Data.Nat.Lattice

/-! Source Definition 4: whole open balls, not merely their centers, are
contained in the target set. Under A1 every positive-radius packing is finite. -/
namespace BanditRLProof.HOO

structure ContainedBallPacking {X I : Type*} (ell : X → X → ℝ)
    (A : Set X) (ε : ℝ) (centers : I → X) : Prop where
  contained : ∀ i, {y | ell (centers i) y < ε} ⊆ A
  disjoint : Pairwise (fun i j => Disjoint {y | ell (centers i) y < ε}
    {y | ell (centers j) y < ε})

def packingSizes {X : Type*} (ell : X → X → ℝ) (A : Set X) (ε : ℝ) : Set ℕ :=
  {k | ∃ centers : Fin k → X, ContainedBallPacking ell A ε centers}

theorem zero_mem_packingSizes {X : Type*} (ell : X → X → ℝ) (A : Set X) (ε : ℝ) :
    0 ∈ packingSizes ell A ε :=
  ⟨Fin.elim0, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩

theorem RegularCovering.packingSizes_bddAbove {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (A : Set X) (ε : ℝ) (hε : 0 < ε) :
    BddAbove (packingSizes C.ell A ε) := by
  obtain ⟨M, hM⟩ := C.exists_finite_packing_bound ε hε
  refine ⟨M, ?_⟩
  rintro k ⟨centers, hc⟩
  simpa only [Fintype.card_fin] using hM (Fin k) centers hc.disjoint

/-- Natural-valued source packing number on an A1 space. All semantic
theorems below require positive radius, where finiteness is proved. -/
noncomputable def RegularCovering.packingNumber {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (A : Set X) (ε : ℝ) : ℕ := sSup (packingSizes C.ell A ε)

theorem RegularCovering.packingNumber_attained {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (A : Set X) (ε : ℝ) (hε : 0 < ε) :
    ∃ centers : Fin (C.packingNumber A ε) → X, ContainedBallPacking C.ell A ε centers :=
  Nat.sSup_mem ⟨0, zero_mem_packingSizes _ _ _⟩ (C.packingSizes_bddAbove A ε hε)

theorem RegularCovering.packingNumber_mono {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) {A B : Set X} (hAB : A ⊆ B) (ε : ℝ) (hε : 0 < ε) :
    C.packingNumber A ε ≤ C.packingNumber B ε := by
  apply csSup_le_csSup (C.packingSizes_bddAbove B ε hε) ⟨0, zero_mem_packingSizes _ _ _⟩
  rintro k ⟨centers, hc⟩
  exact ⟨centers, ⟨fun i => (hc.contained i).trans hAB, hc.disjoint⟩⟩

theorem RegularCovering.containedPacking_card_le {X I : Type*} [MeasurableSpace X]
    [Fintype I] (C : RegularCovering X) (A : Set X) (ε : ℝ) (hε : 0 < ε)
    (centers : I → X) (hc : ContainedBallPacking C.ell A ε centers) :
    Fintype.card I ≤ C.packingNumber A ε := by
  classical
  apply le_csSup (C.packingSizes_bddAbove A ε hε)
  refine ⟨fun j => centers ((Fintype.equivFin I).symm j), ?_⟩
  constructor
  · intro j
    exact hc.contained _
  · intro i j hij
    apply hc.disjoint
    exact fun he => hij ((Fintype.equivFin I).symm.injective he)

noncomputable def RegularCovering.nearOptimalNodes {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ) (h : ℕ) : Finset Node :=
  (nodesAtDepth h).filter (fun v => best-regionSup f (C.region v) ≤ 2*(C.nu1*C.rho^h))

/-- Source Theorem 6, second-step packing producer for the actual near-optimal
nodes. It constructs contained balls via A1 and Lemma 3 with c=2. -/
theorem RegularCovering.nearOptimalNodes_card_le_packing {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (f : X → ℝ) (best : ℝ)
    (hw : WeaklyLipschitz f C.ell best) (h : ℕ) :
    (C.nearOptimalNodes f best h).card ≤
      C.packingNumber {y | best-f y ≤ 4*(C.nu1*C.rho^h)} (C.nu2*C.rho^h) := by
  classical
  have hn (v : {v // v ∈ C.nearOptimalNodes f best h}) : v.val.length=h :=
    (mem_nodesAtDepth _ h).mp (Finset.mem_filter.mp v.property).1
  have hp : ContainedBallPacking C.ell {y | best-f y ≤ 4*(C.nu1*C.rho^h)}
      (C.nu2*C.rho^h) (fun v : {v // v ∈ C.nearOptimalNodes f best h} => C.center v.val) := by
    constructor
    · intro v y hy
      have hgap := (Finset.mem_filter.mp v.property).2
      have hmem : y ∈ C.region v.val := C.ball_subset v.val (by simpa only [hn v] using hy)
      have hh := C.region_near_optimal f best 2 v.val hw (by simpa only [hn v] using hgap) y hmem
      norm_num only [hn v, mul_one, max_eq_left (by norm_num : (3:ℝ) ≤ 4)] at hh
      convert hh using 1
    · intro v w hne
      have hh := C.balls_disjoint v.val w.val ((hn v).trans (hn w).symm)
        (fun he => hne (Subtype.ext he))
      simpa only [hn v, hn w] using hh
  simpa only [Fintype.card_coe] using C.containedPacking_card_le _ _
    (mul_pos C.nu2_pos (pow_pos C.rho_pos _)) _ hp


/-- Larger-radius contained packings inject into an ambient smaller-radius
packing by shrinking every ball, without symmetry or a triangle inequality. -/
theorem RegularCovering.packingNumber_le_ambient {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (A : Set X) {δ ε : ℝ} (hδ : 0<δ) (hδε : δ≤ε) :
    C.packingNumber A ε ≤ C.packingNumber Set.univ δ := by
  obtain ⟨centers, hc⟩ := C.packingNumber_attained A ε (hδ.trans_le hδε)
  have hp : ContainedBallPacking C.ell Set.univ δ centers := by
    constructor
    · intro i y hy
      trivial
    · intro i j hij
      exact (hc.disjoint hij).mono (fun y hy => lt_of_lt_of_le hy hδε)
        (fun y hy => lt_of_lt_of_le hy hδε)
  simpa only [Fintype.card_fin] using C.containedPacking_card_le Set.univ δ hδ centers hp

end BanditRLProof.HOO

