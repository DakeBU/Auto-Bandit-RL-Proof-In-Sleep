import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
The exact piecewise sampling threshold of Chen et al. (JMLR 2016).
Normalized analysis counters repair the mixed triggering-probability step.
This file does not assert a CUCB trajectory or regret theorem.
-/
namespace BanditRLProof.CUCB
set_option autoImplicit false

/-- `u` is the positive inverse-smoothness value at the current gap. -/
noncomputable def thresholdCoefficient (u p : ℝ) : ℝ :=
  if p = 1 then 6 / u^2 else max (12 / (u^2*p)) (24/p)

noncomputable def samplingThreshold (n : ℕ) (u p : ℝ) : ℝ :=
  Real.log n * thresholdCoefficient u p

theorem thresholdCoefficient_pos {u p : ℝ} (hu : 0<u) (hp : 0<p) :
    0<thresholdCoefficient u p := by
  unfold thresholdCoefficient
  split_ifs
  · positivity
  · exact lt_of_lt_of_le (by positivity : (0:ℝ)<24/p) (le_max_right _ _)

theorem samplingThreshold_deterministic (n : ℕ) (u : ℝ) :
    samplingThreshold n u 1 = 6 * Real.log n / u^2 := by
  simp [samplingThreshold, thresholdCoefficient]
  ring

theorem samplingThreshold_probabilistic {n : ℕ} {u p : ℝ}
    (hn : 1≤n) (hp : p≠1) :
    samplingThreshold n u p =
      max (12*Real.log n/(u^2*p)) (24*Real.log n/p) := by
  have hlog : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  simp only [samplingThreshold, thresholdCoefficient, if_neg hp]
  rw [mul_max_of_nonneg _ _ hlog]
  congr 1 <;> ring

/-- A definite, tie-fixed analysis choice. Its arguments depend only on the
past counters, the current action and fixed instance parameters. -/
noncomputable def normalizedCharge {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (N c : ι → ℝ) : ι :=
  Classical.choose (s.exists_min_image (fun j => N j / c j) hs)

theorem normalizedCharge_spec {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (N c : ι → ℝ) :
    normalizedCharge s hs N c ∈ s ∧
      ∀j∈s, N (normalizedCharge s hs N c) / c (normalizedCharge s hs N c)
        ≤ N j / c j :=
  Classical.choose_spec (s.exists_min_image (fun j => N j / c j) hs)

theorem normalizedCharge_sufficient {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (N c : ι → ℝ) (hc : ∀i∈s, 0<c i)
    (L : ℝ) (hL : L*c (normalizedCharge s hs N c)<N (normalizedCharge s hs N c)) :
    ∀j∈s, L*c j<N j := by
  have h := normalizedCharge_spec s hs N c
  intro j hj
  exact (lt_div_iff₀ (hc j hj)).1
    (lt_of_lt_of_le ((lt_div_iff₀ (hc _ h.1)).2 hL) (h.2 j hj))

/-- For any finite nonempty possible-trigger set, an analysis charge exists
whose sufficient sampling forces sufficient sampling of every member.
The threshold coefficients may differ across arms, including p=1 vs p<1.
No claim of predictability is made here; that requires the actual history. -/
theorem exists_normalized_charge {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (N c : ι → ℝ) (hc : ∀i∈s, 0<c i) :
    ∃i∈s, ∀j∈s, ∀L : ℝ, L*c i<N i → L*c j<N j := by
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun j => N j / c j) hs
  refine ⟨i, hi, ?_⟩
  intro j hj L hL
  have hLi : L<N i/c i := (lt_div_iff₀ (hc i hi)).2 hL
  have hLj : L<N j/c j := lt_of_lt_of_le hLi (hmin j hj)
  exact (lt_div_iff₀ (hc j hj)).1 hLj

theorem exists_threshold_charge {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (N p : ι → ℝ) (u : ℝ) (hu : 0<u) (hp : ∀i∈s, 0<p i) :
    ∃i∈s, ∀j∈s, ∀n : ℕ,
      samplingThreshold n u (p i)<N i → samplingThreshold n u (p j)<N j := by
  obtain ⟨i, hi, h⟩ := exists_normalized_charge s hs N
    (fun j => thresholdCoefficient u (p j))
    (fun j hj => thresholdCoefficient_pos hu (hp j hj))
  exact ⟨i, hi, fun j hj n => h j hj (Real.log n)⟩

end BanditRLProof.CUCB

