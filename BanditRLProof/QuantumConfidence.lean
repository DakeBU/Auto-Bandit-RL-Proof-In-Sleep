import BanditRLProof.ProbabilityUnionBound
import BanditRLProof.FiniteRealArgmax
import Mathlib.Tactic

/-! Deterministic decision leaves shared by finite-coherence regret and
fixed-systematic-bias best-arm identification. This file does not construct
a quantum estimator, assign a noise law to its output, or claim a query speedup. -/
namespace BanditRLProof.QuantumConfidence

/-- Uses the library's fixed enumeration and tie convention. Exact-real
comparisons are a mathematical decision model, not a finite-bit runtime claim. -/
noncomputable def recommend {K : ℕ} [Nonempty (Fin K)] (estimate : Fin K → ℝ) : Fin K :=
  FiniteRealArgmax.choose estimate

/-- Fixed circuit bias and statistical error compose on their actual good event. -/
theorem bias_statistical_composition {μ ν estimate b s : ℝ}
    (hb : |ν - μ| ≤ b) (hs : |estimate - ν| ≤ s) :
    |estimate - μ| ≤ b + s := by
  calc
    _ = |(estimate - ν) + (ν - μ)| := by congr 1; ring
    _ ≤ |estimate - ν| + |ν - μ| := abs_add_le _ _
    _ ≤ b + s := by linarith

/-- Strictly disjoint intervals remove arms; touching intervals and ties survive. -/
noncomputable def survivors {K : ℕ} (active : Finset (Fin K))
    (estimate radius : Fin K → ℝ) : Finset (Fin K) :=
  active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i

theorem optimal_survives {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star : Fin K) (hstar : star ∈ active)
    (hopt : ∀ i ∈ active, μ i ≤ μ star)
    (hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i) :
    star ∈ survivors active estimate radius := by
  classical
  simp only [survivors, Finset.mem_filter]
  refine ⟨hstar, fun i hi => ?_⟩
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hi)).2
  linarith [hopt i hi]

theorem large_gap_removed {K : ℕ} (active : Finset (Fin K))
    (μ estimate radius : Fin K → ℝ) (star i : Fin K) (hstar : star ∈ active)
    {r : ℝ} (hwidth : ∀ j ∈ active, radius j ≤ r)
    (hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
    (hgap : 4 * r < μ star - μ i) :
    i ∉ survivors active estimate radius := by
  classical
  intro hi
  obtain ⟨hia, hkeep⟩ := Finset.mem_filter.mp hi
  have hcmp := hkeep star hstar
  have hs := (abs_le.mp (hconf star hstar)).1
  have hi' := (abs_le.mp (hconf i hia)).2
  linarith [hwidth star hstar, hwidth i hia]

/-- The selected estimate may be any maximizer. No unique optimum is assumed. -/
theorem recommendation_epsilon_optimal {K : ℕ} (μ estimate : Fin K → ℝ)
    (selected : Fin K) {ε : ℝ}
    (hselect : ∀ i, estimate i ≤ estimate selected)
    (hconf : ∀ i, |estimate i - μ i| ≤ ε / 2) :
    ∀ i, μ i ≤ μ selected + ε := by
  intro i
  have hi := (abs_le.mp (hconf i)).1
  have hj := (abs_le.mp (hconf selected)).2
  linarith [hselect i]

theorem fixed_fidelity_recommendation {K : ℕ}
    (μ ν estimate bias statistical : Fin K → ℝ) (selected : Fin K) {ε : ℝ}
    (hselect : ∀ i, estimate i ≤ estimate selected)
    (hb : ∀ i, |ν i - μ i| ≤ bias i)
    (hs : ∀ i, |estimate i - ν i| ≤ statistical i)
    (hbudget : ∀ i, bias i + statistical i ≤ ε / 2) :
    ∀ i, μ i ≤ μ selected + ε :=
  recommendation_epsilon_optimal μ estimate selected hselect
    (fun i => (bias_statistical_composition (hb i) (hs i)).trans (hbudget i))

/-- Finite-horizon event accounting needs marginal bad-event bounds only;
conditional confidence must still be supplied by the actual estimator. -/
theorem finite_failure_union {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) (bad : Fin N → Set Ω) (share : Fin N → ℝ)
    (hb : ∀ i, μ (bad i) ≤ ENNReal.ofReal (share i)) :
    μ (⋃ i, bad i) ≤ ∑ i, ENNReal.ofReal (share i) := by
  exact (ProbabilityUnionBound.measure_iUnion_fintype_le_sum μ bad).trans
    (Finset.sum_le_sum fun i _ => hb i)

/-- Confidence-only PAC transport. The estimator tail producer remains an
explicit dependency of the full quantum algorithm, rather than an assumed
sub-Gaussian noise law. No independence of estimates is required here. -/
theorem fixed_fidelity_failure_bound {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (law : MeasureTheory.Measure Ω) (μ ν bias statistical : Fin K → ℝ)
    (estimate : Fin K → Ω → ℝ) (selected : Ω → Fin K) {ε : ℝ}
    (hselect : ∀ ω i, estimate i ω ≤ estimate (selected ω) ω)
    (hb : ∀ i, |ν i - μ i| ≤ bias i)
    (hbudget : ∀ i, bias i + statistical i ≤ ε / 2)
    (share : Fin K → ℝ)
    (htail : ∀ i, law {ω | statistical i < |estimate i ω - ν i|} ≤
      ENNReal.ofReal (share i)) :
    law {ω | ∃ i, μ (selected ω) + ε < μ i} ≤
      ∑ i, ENNReal.ofReal (share i) := by
  classical
  have hsubset : {ω | ∃ i, μ (selected ω) + ε < μ i} ⊆
      ⋃ i, {ω | statistical i < |estimate i ω - ν i|} := by
    intro ω hbad
    by_contra hout
    have hgood : ∀ i, |estimate i ω - ν i| ≤ statistical i := by
      intro i
      by_contra hi
      exact hout (Set.mem_iUnion.mpr ⟨i, lt_of_not_ge hi⟩)
    have h := fixed_fidelity_recommendation μ ν (fun i => estimate i ω)
      bias statistical (selected ω) (hselect ω) hb hgood hbudget
    obtain ⟨i, hi⟩ := hbad
    exact (not_lt_of_ge (h i)) hi
  exact (MeasureTheory.measure_mono hsubset).trans
    (finite_failure_union law _ share htail)

/-- The actual fixed-enumeration recommendation consumes the confidence
transport without assuming an unexplained maximizer certificate. -/
theorem recommend_fixed_fidelity_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    {K : ℕ} [Nonempty (Fin K)]
    (law : MeasureTheory.Measure Ω) (μ ν bias statistical : Fin K → ℝ)
    (estimate : Fin K → Ω → ℝ) {ε : ℝ}
    (hb : ∀ i, |ν i - μ i| ≤ bias i)
    (hbudget : ∀ i, bias i + statistical i ≤ ε / 2)
    (share : Fin K → ℝ)
    (htail : ∀ i, law {ω | statistical i < |estimate i ω - ν i|} ≤
      ENNReal.ofReal (share i)) :
    law {ω | ∃ i, μ (recommend (fun j => estimate j ω)) + ε < μ i} ≤
      ∑ i, ENNReal.ofReal (share i) :=
  fixed_fidelity_failure_bound law μ ν bias statistical estimate _
    (fun ω i => FiniteRealArgmax.score_le_choose (fun j => estimate j ω) i)
    hb hbudget share htail

end BanditRLProof.QuantumConfidence
