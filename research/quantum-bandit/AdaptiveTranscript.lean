import QuantumBlockEncoding.ResetBlockProcess
import Mathlib.Tactic

namespace BanditRLProof.AdaptiveTranscript

open QuantumBlockEncoding
open scoped Matrix.Norms.L2Operator

theorem hellingerSq_expand {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ h, 0 ≤ q h) :
    BasisHellinger.hellingerSq p q =
      (∑ h, p h) + (∑ h, q h) - 2 * ∑ h, Real.sqrt (p h) * Real.sqrt (q h) := by
  unfold BasisHellinger.hellingerSq
  calc
    _ = ∑ h, (p h + q h - 2 * (Real.sqrt (p h) * Real.sqrt (q h))) := by
      apply Finset.sum_congr rfl
      intro h _
      nlinarith [Real.sq_sqrt (hp h), Real.sq_sqrt (hq h)]
    _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem finite_kernel_chain {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (k l : α → β → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ h, 0 ≤ q h)
    (hk : ∀ h j, 0 ≤ k h j) (hl : ∀ h j, 0 ≤ l h j)
    (hk1 : ∀ h, ∑ j, k h j = 1) (hl1 : ∀ h, ∑ j, l h j = 1) :
    BasisHellinger.hellingerSq (fun h : α × β => p h.1 * k h.1 h.2)
      (fun h : α × β => q h.1 * l h.1 h.2) =
      BasisHellinger.hellingerSq p q + ∑ h,
        Real.sqrt (p h) * Real.sqrt (q h) * BasisHellinger.hellingerSq (k h) (l h) := by
  have row (h : α) :
      (∑ j, (Real.sqrt (p h * k h j) - Real.sqrt (q h * l h j)) ^ 2) =
        (Real.sqrt (p h) - Real.sqrt (q h)) ^ 2 +
          Real.sqrt (p h) * Real.sqrt (q h) * BasisHellinger.hellingerSq (k h) (l h) := by
    change BasisHellinger.hellingerSq (fun j => p h * k h j)
      (fun j => q h * l h j) = _
    rw [hellingerSq_expand _ _ (fun j => mul_nonneg (hp h) (hk h j))
      (fun j => mul_nonneg (hq h) (hl h j))]
    simp_rw [Real.sqrt_mul (hp h), Real.sqrt_mul (hq h)]
    have cross : (∑ j, Real.sqrt (p h) * Real.sqrt (k h j) *
        (Real.sqrt (q h) * Real.sqrt (l h j))) =
        Real.sqrt (p h) * Real.sqrt (q h) * ∑ j, Real.sqrt (k h j) * Real.sqrt (l h j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [cross, ← Finset.mul_sum, ← Finset.mul_sum, hk1 h, hl1 h,
      hellingerSq_expand _ _ (hk h) (hl h), hk1 h, hl1 h]
    nlinarith [Real.sq_sqrt (hp h), Real.sq_sqrt (hq h)]
  unfold BasisHellinger.hellingerSq
  rw [Fintype.sum_prod_type]
  simp_rw [row]
  rw [Finset.sum_add_distrib]
  rfl

universe u

def Trace (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Trace ι n × ι

instance traceFintype {ι : Type*} [Fintype ι] (n : ℕ) : Fintype (Trace ι n) :=
  match n with
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd (Trace ι n) ι (traceFintype n) inferInstance

def history {ι : Type*} : {n : ℕ} → Trace ι n → List ι
  | 0, _ => []
  | _ + 1, h => history h.1 ++ [h.2]

theorem history_length {ι : Type*} {n : ℕ} (h : Trace ι n) : (history h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

theorem history_injective {ι : Type*} (n : ℕ) : Function.Injective (history (ι := ι) (n := n)) := by
  induction n with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
      intro a b hab
      have lengths : (history a.1).length = (history b.1).length := by rw [history_length, history_length]
      obtain ⟨ha, hb⟩ := List.append_inj hab lengths
      exact Prod.ext (ih ha) (List.singleton_inj.mp hb)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K D : ℕ}

noncomputable def kernel (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (h : List ι) (j : ι) : ℝ :=
  BasisHellinger.basisProbability
    (BasisHellinger.wordOutput (policy h).word (oracle (policy h).arm) ψ) j

noncomputable def density (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    (n : ℕ) → Trace ι n → ℝ
  | 0, _ => 1
  | n + 1, h => density policy oracle ψ n h.1 * kernel policy oracle ψ (history h.1) h.2

noncomputable def weightedCost (policy : List ι → ResetBlockProcess.Plan K D ι)
    (η : Fin K → ℝ) : {n : ℕ} → Trace ι n → ℝ
  | 0, _ => 0
  | _ + 1, h => weightedCost policy η h.1 +
      (QuantumQueryWord.queryCount (policy (history h.1)).word : ℝ) *
        η (policy (history h.1)).arm ^ 2

noncomputable def expectedCost (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (η : Fin K → ℝ) (n : ℕ) : ℝ :=
  ∑ h : Trace ι n, density policy oracle ψ n h * weightedCost policy η h

theorem kernel_nonneg (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (h : List ι) (j : ι) : 0 ≤ kernel policy oracle ψ h j :=
  BasisHellinger.basisProbability_nonneg _ _

theorem kernel_normalized (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (h : List ι) : ∑ j, kernel policy oracle ψ h j = 1 :=
  BasisHellinger.wordOutput_probability_normalized (policy h).word
    (oracle (policy h).arm) ψ hψ (oracle (policy h).arm).property

theorem density_nonneg (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (n : ℕ) (h : Trace ι n) : 0 ≤ density policy oracle ψ n h := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih h.1) (kernel_nonneg _ _ _ _ _)

theorem density_normalized (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) : ∑ h, density policy oracle ψ n h = 1 := by
  induction n with
  | zero => simp [Trace, density]
  | succ n ih =>
      change (∑ h : Trace ι n × ι,
        density policy oracle ψ n h.1 * kernel policy oracle ψ (history h.1) h.2) = 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, kernel_normalized policy oracle ψ hψ, mul_one]
      exact ih

theorem expectedCost_succ (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ) (n : ℕ) :
    expectedCost policy oracle ψ η (n + 1) = expectedCost policy oracle ψ η n +
      ∑ h : Trace ι n, density policy oracle ψ n h *
        ((QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2) := by
  unfold expectedCost
  change (∑ h : Trace ι n × ι,
      (density policy oracle ψ n h.1 * kernel policy oracle ψ (history h.1) h.2) *
        (weightedCost policy η h.1 +
          (QuantumQueryWord.queryCount (policy (history h.1)).word : ℝ) *
            η (policy (history h.1)).arm ^ 2)) = _
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = density policy oracle ψ n h *
        (weightedCost policy η h + (QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2) * ∑ j, kernel policy oracle ψ (history h) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [kernel_normalized policy oracle ψ hψ, mul_one]; ring

theorem kernel_hellinger_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η i)
    (h : List ι) :
    BasisHellinger.hellingerSq (kernel policy oracleE ψ h) (kernel policy oracleF ψ h) ≤
      (D : ℝ) * ((QuantumQueryWord.queryCount (policy h).word : ℝ) *
        η (policy h).arm ^ 2) := by
  have bound := BasisHellinger.bounded_word_hellingerSq_le (policy h).word
    (oracleE (policy h).arm) (oracleF (policy h).arm) ψ hψ
    (oracleE (policy h).arm).property (oracleF (policy h).arm).property
    (hEF (policy h).arm) (policy h).bounded
  simpa only [kernel, mul_assoc] using bound

theorem adaptive_hellinger_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η i)
    (n : ℕ) :
    BasisHellinger.hellingerSq (density policy oracleE ψ n) (density policy oracleF ψ n) ≤
      (D : ℝ) / 2 *
        (expectedCost policy oracleE ψ η n + expectedCost policy oracleF ψ η n) := by
  induction n with
  | zero => simp [expectedCost, weightedCost, density, Trace, BasisHellinger.hellingerSq]
  | succ n ih =>
      change BasisHellinger.hellingerSq
        (fun h : Trace ι n × ι => density policy oracleE ψ n h.1 *
          kernel policy oracleE ψ (history h.1) h.2)
        (fun h : Trace ι n × ι => density policy oracleF ψ n h.1 *
          kernel policy oracleF ψ (history h.1) h.2) ≤ _
      rw [finite_kernel_chain _ _ _ _ (density_nonneg policy oracleE ψ n)
        (density_nonneg policy oracleF ψ n)
        (fun h => kernel_nonneg policy oracleE ψ (history h))
        (fun h => kernel_nonneg policy oracleF ψ (history h))
        (fun h => kernel_normalized policy oracleE ψ hψ (history h))
        (fun h => kernel_normalized policy oracleF ψ hψ (history h))]
      let step : Trace ι n → ℝ := fun h =>
        (QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2
      have hstep :
          (∑ h : Trace ι n, Real.sqrt (density policy oracleE ψ n h) *
            Real.sqrt (density policy oracleF ψ n h) *
            BasisHellinger.hellingerSq (kernel policy oracleE ψ (history h))
              (kernel policy oracleF ψ (history h))) ≤
          (D : ℝ) / 2 * ((∑ h, density policy oracleE ψ n h * step h) +
            ∑ h, density policy oracleF ψ n h * step h) := by
        calc
          _ ≤ ∑ h : Trace ι n, (D : ℝ) / 2 *
              (density policy oracleE ψ n h * step h + density policy oracleF ψ n h * step h) := by
            apply Finset.sum_le_sum
            intro h _
            have hinfo := kernel_hellinger_le policy oracleE oracleF ψ hψ η hEF (history h)
            have ha := Real.sq_sqrt (density_nonneg policy oracleE ψ n h)
            have hb := Real.sq_sqrt (density_nonneg policy oracleF ψ n h)
            have ham : 2 * Real.sqrt (density policy oracleE ψ n h) *
                Real.sqrt (density policy oracleF ψ n h) ≤
                density policy oracleE ψ n h + density policy oracleF ψ n h := by
              nlinarith [sq_nonneg (Real.sqrt (density policy oracleE ψ n h) -
                Real.sqrt (density policy oracleF ψ n h))]
            have hs : 0 ≤ step h := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
            have hmul := mul_le_mul_of_nonneg_left hinfo
              (mul_nonneg (Real.sqrt_nonneg (density policy oracleE ψ n h))
                (Real.sqrt_nonneg (density policy oracleF ψ n h)))
            have ham' := mul_le_mul_of_nonneg_right ham (mul_nonneg (Nat.cast_nonneg D) hs)
            change _ ≤ (D : ℝ) * step h at hinfo
            change _ ≤ Real.sqrt (density policy oracleE ψ n h) *
              Real.sqrt (density policy oracleF ψ n h) * ((D : ℝ) * step h) at hmul
            nlinarith
          _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have he := expectedCost_succ policy oracleE ψ hψ η n
      have hf := expectedCost_succ policy oracleF ψ hψ η n
      change expectedCost policy oracleE ψ η (n + 1) =
        expectedCost policy oracleE ψ η n + ∑ h, density policy oracleE ψ n h * step h at he
      change expectedCost policy oracleF ψ η (n + 1) =
        expectedCost policy oracleF ψ η n + ∑ h, density policy oracleF ψ n h * step h at hf
      rw [he, hf]
      exact (add_le_add ih hstep).trans_eq (by ring)

noncomputable def traceLaw (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) : (n : ℕ) → PMF (Trace ι n)
  | 0 => PMF.pure PUnit.unit
  | n + 1 => (traceLaw policy oracle ψ hψ n).bind fun h =>
      (ResetBlockProcess.blockPMF (policy (history h)) oracle ψ hψ).map (Prod.mk h)

open scoped Classical in
theorem map_pair_apply {α β : Type*} [Fintype β]
    (p : PMF β) (a : α) (h : α × β) :
    p.map (Prod.mk a) h = if h.1 = a then p h.2 else 0 := by
  classical
  rcases h with ⟨x, y⟩
  by_cases ha : x = a
  · subst x
    simp [PMF.map_apply, tsum_fintype]
  · simp [PMF.map_apply, tsum_fintype, Prod.mk.injEq, ha]

theorem traceLaw_apply (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    traceLaw policy oracle ψ hψ n h = ENNReal.ofReal (density policy oracle ψ n h) := by
  classical
  induction n with
  | zero => cases h; simp [traceLaw, density]
  | succ n ih =>
      change ((traceLaw policy oracle ψ hψ n).bind fun previous =>
        (ResetBlockProcess.blockPMF (policy (history previous)) oracle ψ hψ).map (Prod.mk previous)) h = _
      rw [PMF.bind_apply, tsum_fintype]
      simp_rw [map_pair_apply, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [ih, ResetBlockProcess.blockPMF_apply, ← ENNReal.ofReal_mul
        (density_nonneg policy oracle ψ n h.1)]
      rfl

theorem traceLaw_history_eq (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) :
    (traceLaw policy oracle ψ hψ n).map history =
      ResetBlockProcess.historyLaw policy oracle ψ hψ n := by
  induction n with
  | zero => simp [traceLaw, ResetBlockProcess.historyLaw, PMF.pure_map, history]
  | succ n ih =>
      calc
        _ = (traceLaw policy oracle ψ hψ n).bind fun h =>
            (ResetBlockProcess.blockPMF (policy (history h)) oracle ψ hψ).map
              (fun j => history h ++ [j]) := by
          simp only [traceLaw, PMF.map_bind, PMF.map_comp]
          rfl
        _ = ((traceLaw policy oracle ψ hψ n).map history).bind fun h =>
            (ResetBlockProcess.blockPMF (policy h) oracle ψ hψ).bind fun j =>
              PMF.pure (h ++ [j]) := by
          rw [PMF.bind_map]
          rfl
        _ = _ := by rw [ih]; rfl

theorem traceLaw_toReal (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    (traceLaw policy oracle ψ hψ n h).toReal = density policy oracle ψ n h := by
  rw [traceLaw_apply, ENNReal.toReal_ofReal (density_nonneg policy oracle ψ n h)]

theorem historyLaw_apply_at_trace (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    ResetBlockProcess.historyLaw policy oracle ψ hψ n (history h) =
      ENNReal.ofReal (density policy oracle ψ n h) := by
  classical
  rw [← traceLaw_history_eq, PMF.map_apply, tsum_fintype]
  simp only [(history_injective n).eq_iff, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact traceLaw_apply _ _ _ _ _ _

theorem historyQueryCost_append (policy : List ι → ResetBlockProcess.Plan K D ι)
    (h : List ι) (j : ι) :
    ResetBlockProcess.historyQueryCost policy (h ++ [j]) =
      ResetBlockProcess.historyQueryCost policy h + QuantumQueryWord.queryCount (policy h).word := by
  unfold ResetBlockProcess.historyQueryCost
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.mp ht))]
  · simp

theorem weightedCost_uniform (policy : List ι → ResetBlockProcess.Plan K D ι)
    (η : ℝ) {n : ℕ} (h : Trace ι n) :
    weightedCost policy (fun _ => η) h =
      (ResetBlockProcess.historyQueryCost policy (history h) : ℝ) * η ^ 2 := by
  induction n with
  | zero => simp [weightedCost, history, ResetBlockProcess.historyQueryCost]
  | succ n ih =>
      change weightedCost policy (fun _ => η) h.1 +
        (QuantumQueryWord.queryCount (policy (history h.1)).word : ℝ) * η ^ 2 =
        (ResetBlockProcess.historyQueryCost policy (history h.1 ++ [h.2]) : ℝ) * η ^ 2
      rw [ih, historyQueryCost_append, Nat.cast_add]
      ring

theorem expectedCost_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ) (n : ℕ) (B : ℝ)
    (hB : ∀ h : Trace ι n, weightedCost policy η h ≤ B) :
    expectedCost policy oracle ψ η n ≤ B := by
  calc
    _ ≤ ∑ h : Trace ι n, density policy oracle ψ n h * B :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hB h) (density_nonneg _ _ _ _ _)
    _ = B := by rw [← Finset.sum_mul, density_normalized policy oracle ψ hψ n, one_mul]

theorem adaptive_hellinger_budget (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η)
    (n T : ℕ)
    (hT : ∀ h : Trace ι n, ResetBlockProcess.historyQueryCost policy (history h) ≤ T) :
    BasisHellinger.hellingerSq
      (fun h => (traceLaw policy oracleE ψ hψ n h).toReal)
      (fun h => (traceLaw policy oracleF ψ hψ n h).toReal) ≤ (D : ℝ) * T * η ^ 2 := by
  simp_rw [traceLaw_toReal]
  have hcost (h : Trace ι n) : weightedCost policy (fun _ => η) h ≤ (T : ℝ) * η ^ 2 := by
    rw [weightedCost_uniform]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT h) (sq_nonneg η)
  have he := expectedCost_le policy oracleE ψ hψ (fun _ => η) n _ hcost
  have hf := expectedCost_le policy oracleF ψ hψ (fun _ => η) n _ hcost
  calc
    _ ≤ (D : ℝ) / 2 * (expectedCost policy oracleE ψ (fun _ => η) n +
        expectedCost policy oracleF ψ (fun _ => η) n) :=
      adaptive_hellinger_le policy oracleE oracleF ψ hψ (fun _ => η) hEF n
    _ ≤ (D : ℝ) / 2 * ((T : ℝ) * η ^ 2 + (T : ℝ) * η ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add he hf) (by positivity)
    _ = _ := by ring

end BanditRLProof.AdaptiveTranscript
