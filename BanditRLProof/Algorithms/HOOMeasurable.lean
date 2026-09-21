import BanditRLProof.Algorithms.HOOHistory
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.List.OfFn

/-! Measurability of the actual finite tree computations. Node labels are
countable and discrete; the confidence comparisons remain real-valued. -/
namespace BanditRLProof.HOO
open MeasureTheory

instance : MeasurableSpace Node := ⊤
instance : DiscreteMeasurableSpace Node := inferInstanceAs (@DiscreteMeasurableSpace Node ⊤)

theorem measurable_backward {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset Node) (U : Ω → Node → WithTop ℝ)
    (hU : ∀ v, Measurable (fun ω => U ω v)) (k : ℕ) (v : Node) :
    Measurable (fun ω => backward S (U ω) k v) := by
  induction k generalizing v with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hv : v ∈ S
    · simpa only [backward, if_pos hv] using (hU v).min ((ih (child v false)).max (ih (child v true)))
    · simpa only [backward, if_neg hv] using (measurable_const : Measurable (fun _ : Ω => (⊤ : WithTop ℝ)))

theorem measurable_walk {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset Node) (B : Ω → Node → WithTop ℝ)
    (hB : ∀ v, Measurable (fun ω => B ω v)) (k : ℕ) (v : Node) :
    Measurable (fun ω => walk S (B ω) k v) := by
  classical
  induction k generalizing v with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hv : v ∈ S
    · have h : Measurable (fun ω => if B ω (child v true) ≤ B ω (child v false)
          then walk S (B ω) k (child v false) else walk S (B ω) k (child v true)) :=
        (ih (child v false)).ite
          (measurableSet_le (hB (child v true)) (hB (child v false))) (ih (child v true))
      convert h using 1
      funext ω
      simp only [walk, if_pos hv, preferred]
      split <;> rfl
    · simpa only [walk, if_neg hv] using (measurable_const : Measurable (fun _ : Ω => v))

theorem measurable_select {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset Node) (U : Ω → Node → WithTop ℝ)
    (hU : ∀ v, Measurable (fun ω => U ω v)) :
    Measurable (fun ω => select S (U ω)) :=
  measurable_walk S (fun ω v => bValue S (U ω) v)
    (fun v => measurable_backward S U hU _ v) _ []

theorem visits_ofFn {n : ℕ} (a : Fin n → Node) (r : Fin n → ℝ) (v : Node) :
    visits (List.ofFn (fun i => (a i, r i))) v =
      (List.ofFn a).countP (fun w => decide (v <+: w)) := by
  unfold visits
  rw [List.ofFn_comp' (fun i : Fin n => i) (fun i => (a i, r i)),
    List.ofFn_comp' (fun i : Fin n => i) a]
  simp only [List.countP_map, Function.comp_def]

theorem expanded_ofFn {n : ℕ} (a : Fin n → Node) (r : Fin n → ℝ) :
    expanded (List.ofFn (fun i => (a i, r i))) = insert [] (List.ofFn a).toFinset := by
  simp [expanded, List.map_ofFn, Function.comp_def]

/-- A genuine history-to-action map: discrete past nodes and real past rewards. -/
theorem measurable_next_ofFn (ν ρ : ℝ) (n : ℕ) :
    Measurable (fun p : (Fin n → Node) × (Fin n → ℝ) =>
      next ν ρ (List.ofFn (fun i => (p.1 i, p.2 i)))) := by
  classical
  apply measurable_from_prod_countable_right
  intro a
  simp only [next, expanded_ofFn]
  apply measurable_select
  intro v
  simp only [upper, visits_ofFn, List.length_ofFn]
  split
  · exact measurable_const
  · apply Measurable.withTop_coe
    have hs : Measurable (fun r : Fin n → ℝ => rewardSum (List.ofFn (fun i => (a i, r i))) v) := by
      simp only [rewardSum, List.map_ofFn, Function.comp_def, List.sum_ofFn]
      apply Finset.measurable_sum
      intro i _
      split <;> fun_prop
    exact ((hs.div_const _).add_const _).add_const _

theorem measurable_action (ν ρ : ℝ) (n : ℕ) :
    Measurable (fun Y : ℕ → ℝ => action ν ρ Y n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    change Measurable (fun Y => next ν ρ (history ν ρ Y n))
    simp_rw [history_eq_ofFn]
    have hn : Measurable (fun Y : ℕ → ℝ => fun i : Fin n => action ν ρ Y i.val) :=
      measurable_pi_lambda _ (fun i => ih i.val i.isLt)
    have hr : Measurable (fun Y : ℕ → ℝ => fun i : Fin n => Y i.val) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
    have hc := (measurable_next_ofFn ν ρ n).comp (hn.prodMk hr)
    simpa only [Function.comp_def] using hc

end BanditRLProof.HOO
