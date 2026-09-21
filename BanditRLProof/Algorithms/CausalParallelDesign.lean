import BanditRLProof.Algorithms.CausalOptimalAllocation

/-! Constructed rarity parameter and normalized finite intervention design. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

structure ParallelParameters (N : ℕ) where
  q : Fin N → ℝ
  nonneg : ∀ i, 0 ≤ q i
  le_one : ∀ i, q i ≤ 1
  two_le : 2 ≤ N

namespace ParallelParameters
variable {N : ℕ} (p : ParallelParameters N)

noncomputable def rareIndices (tau : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => min (p.q i) (1-p.q i) < 1/(tau:ℝ)

theorem exists_rarity : ∃ m : ℕ, 2 ≤ m ∧ m ≤ N ∧ (p.rareIndices m).card ≤ m := by
  refine ⟨N,p.two_le,le_rfl,?_⟩
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)

noncomputable def rarity : ℕ := Nat.find p.exists_rarity

theorem rarity_spec : 2 ≤ p.rarity ∧ p.rarity ≤ N ∧ (p.rareIndices p.rarity).card ≤ p.rarity :=
  Nat.find_spec p.exists_rarity

theorem rarity_minimal (tau : ℕ) (h2 : 2 ≤ tau) (hN : tau ≤ N)
    (hc : (p.rareIndices tau).card ≤ tau) : p.rarity ≤ tau :=
  Nat.find_min' p.exists_rarity ⟨h2,hN,hc⟩

def valueProbability (a : Fin N × Bool) : ℝ := if a.2 then p.q a.1 else 1-p.q a.1

theorem valueProbability_nonneg (a : Fin N × Bool) : 0 ≤ p.valueProbability a := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [valueProbability, p.nonneg, p.le_one]

theorem rarity_pos : (0 : ℝ) < p.rarity := by
  have h := p.rarity_spec.1
  exact_mod_cast (show 0 < p.rarity by omega)

theorem rarity_reciprocal_le_half : 1/(p.rarity:ℝ) ≤ 1/2 := by
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
  exact_mod_cast p.rarity_spec.1

noncomputable def rareActions : Finset (Fin N × Bool) :=
  Finset.univ.filter fun a => p.valueProbability a < 1/(p.rarity:ℝ)

theorem rareActions_card_le : p.rareActions.card ≤ p.rarity := by
  apply le_trans _ p.rarity_spec.2.2
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro a ha
    change a ∈ p.rareActions at ha
    simp only [rareActions, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    change a.1 ∈ p.rareIndices p.rarity
    simp only [rareIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases a with ⟨i,b⟩
    cases b
    · exact (min_le_right _ _).trans_lt ha
    · exact (min_le_left _ _).trans_lt ha
  · intro a ha b hb heq
    change a ∈ p.rareActions at ha
    change b ∈ p.rareActions at hb
    rcases a with ⟨i,x⟩
    rcases b with ⟨j,y⟩
    change i = j at heq
    subst j
    simp only [rareActions, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hh := p.rarity_reciprocal_le_half
    cases x <;> cases y <;> simp_all [valueProbability] <;> linarith

noncomputable def rareWeight : ℝ := 1/(2*p.rarity)
noncomputable def atomicTotal : ℝ := p.rareActions.card * p.rareWeight

theorem rareWeight_pos : 0 < p.rareWeight := by
  unfold rareWeight
  exact one_div_pos.mpr (mul_pos (by norm_num) p.rarity_pos)

theorem atomicTotal_bounds : 0 ≤ p.atomicTotal ∧ p.atomicTotal ≤ 1/2 := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) p.rareWeight_pos.le
  · have hc : (p.rareActions.card:ℝ) ≤ p.rarity := by exact_mod_cast p.rareActions_card_le
    have h := mul_le_mul_of_nonneg_right hc p.rareWeight_pos.le
    have heq : (p.rarity:ℝ)*p.rareWeight = 1/2 := by
      unfold rareWeight
      field_simp [p.rarity_pos.ne']
    exact h.trans_eq heq

noncomputable def allocationWeight : Option (Fin N × Bool) → ℝ
  | none => 1-p.atomicTotal
  | some a => if a ∈ p.rareActions then p.rareWeight else 0

theorem allocationWeight_nonneg (a : Option (Fin N × Bool)) : 0 ≤ p.allocationWeight a := by
  cases a with
  | none => change 0 ≤ 1-p.atomicTotal; linarith [p.atomicTotal_bounds.2]
  | some a => simp only [allocationWeight]; split_ifs; exact p.rareWeight_pos.le; exact le_rfl

theorem allocationWeight_sum : ∑ a, p.allocationWeight a = 1 := by
  rw [Fintype.sum_option]
  simp only [allocationWeight]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  change (1-p.atomicTotal)+p.atomicTotal = 1
  ring

noncomputable def allocation : PMF (Option (Fin N × Bool)) :=
  allocationOfWeights p.allocationWeight ⟨p.allocationWeight_nonneg,p.allocationWeight_sum⟩

theorem allocation_mass (a : Option (Fin N × Bool)) : mass p.allocation a = p.allocationWeight a := by
  exact allocationOfWeights_mass _ _ _

theorem allocation_empty_ge_half : 1/2 ≤ mass p.allocation none := by
  rw [allocation_mass]
  change 1/2 ≤ 1-p.atomicTotal
  linarith [p.atomicTotal_bounds.2]

end ParallelParameters

theorem covers_of_mass_domination {A Z : Type*} (p : A → PMF Z) (q : PMF Z)
    (C : ℝ) (h : ∀ a z, mass (p a) z ≤ C*mass q z) : Covers p q := by
  intro a z hp hq
  have hh := h a z
  rw [hq,mul_zero] at hh
  exact hp (le_antisymm hh (mass_nonneg _ _))

theorem ratio_le_of_mass_domination {Z : Type*} (p q : PMF Z) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ z, mass p z ≤ C*mass q z) (z : Z) : ratio p q z ≤ C := by
  by_cases hz : mass q z = 0
  · simpa [ratio,hz] using hC
  · exact (div_le_iff₀ (lt_of_le_of_ne (mass_nonneg q z) (Ne.symm hz))).2 (h z)

theorem secondMoment_le_of_mass_domination {Z : Type*} [Fintype Z]
    (p q : PMF Z) (C : ℝ) (hC : 0 ≤ C) (h : ∀ z, mass p z ≤ C*mass q z) :
    secondMoment p q ≤ C := by
  calc
    _ ≤ ∑ z, mass p z*C := Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (ratio_le_of_mass_domination p q C hC h z) (mass_nonneg p z)
    _ = C := by rw [← Finset.sum_mul, sum_mass, one_mul]

end BanditRLProof.Causal
