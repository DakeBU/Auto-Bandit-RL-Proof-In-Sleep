import BanditRLProof.Algorithms.HOOTree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.OfFn

/-! Causal HOO history recursion. Input rewards are chronological observations;
the sequential reward law is a separate mandatory probability construction. -/
namespace BanditRLProof.HOO

abbrev Observations := List (Node × ℝ)

def expanded (h : Observations) : Finset Node := insert [] (h.map Prod.fst).toFinset

def visits (h : Observations) (v : Node) : ℕ :=
  h.countP (fun p => decide (v <+: p.1))

noncomputable def rewardSum (h : Observations) (v : Node) : ℝ :=
  (h.map (fun p => if v <+: p.1 then p.2 else 0)).sum

noncomputable def upper (ν ρ : ℝ) (h : Observations) (v : Node) : WithTop ℝ :=
  if visits h v = 0 then ⊤ else
    ↑(rewardSum h v / visits h v +
      Real.sqrt (2 * Real.log (max (h.length : ℝ) 2) / visits h v) + ν * ρ^v.length)

noncomputable def next (ν ρ : ℝ) (h : Observations) : Node :=
  select (expanded h) (upper ν ρ h)

noncomputable def step (ν ρ : ℝ) (h : Observations) (y : ℝ) : Observations :=
  h ++ [(next ν ρ h, y)]

noncomputable def history (ν ρ : ℝ) (Y : ℕ → ℝ) : ℕ → Observations
  | 0 => []
  | n+1 => step ν ρ (history ν ρ Y n) (Y n)

noncomputable def action (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) : Node :=
  next ν ρ (history ν ρ Y n)

@[simp] theorem step_length (ν ρ : ℝ) (h : Observations) (y : ℝ) :
    (step ν ρ h y).length = h.length + 1 := by simp [step]

@[simp] theorem history_length (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    (history ν ρ Y n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [history, step_length, ih]

theorem expanded_step (ν ρ : ℝ) (h : Observations) (y : ℝ) :
    expanded (step ν ρ h y) = insert (next ν ρ h) (expanded h) := by
  ext v
  simp [expanded, step]
  tauto

theorem next_not_expanded (ν ρ : ℝ) (h : Observations) : next ν ρ h ∉ expanded h :=
  select_not_mem _ _

theorem next_ne_root (ν ρ : ℝ) (h : Observations) : next ν ρ h ≠ [] := by
  intro hn
  have ht := next_not_expanded ν ρ h
  apply ht
  simp [hn, expanded]

theorem next_not_previously_played (ν ρ : ℝ) (h : Observations) :
    next ν ρ h ∉ h.map Prod.fst := by
  intro hn
  exact next_not_expanded ν ρ h (Finset.mem_insert_of_mem (by simpa using hn))

theorem visits_step (ν ρ : ℝ) (h : Observations) (y : ℝ) (v : Node) :
    visits (step ν ρ h y) v = visits h v + if v <+: next ν ρ h then 1 else 0 := by
  simp [visits, step, List.countP_append]

theorem rewardSum_step (ν ρ : ℝ) (h : Observations) (y : ℝ) (v : Node) :
    rewardSum (step ν ρ h y) v = rewardSum h v + if v <+: next ν ρ h then y else 0 := by
  simp [rewardSum, step]

/-- Generated state uses only rewards strictly before the current round. -/
theorem history_causal (ν ρ : ℝ) (Y Z : ℕ → ℝ) (n : ℕ)
    (hYZ : ∀ i < n, Y i = Z i) : history ν ρ Y n = history ν ρ Z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [history, history, ih (fun i hi => hYZ i (by omega)), hYZ n (by omega)]

theorem action_causal (ν ρ : ℝ) (Y Z : ℕ → ℝ) (n : ℕ)
    (hYZ : ∀ i < n, Y i = Z i) : action ν ρ Y n = action ν ρ Z n := by
  unfold action
  rw [history_causal ν ρ Y Z n hYZ]

theorem expanded_card_history (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    (expanded (history ν ρ Y n)).card = n+1 := by
  induction n with
  | zero => simp [history, expanded]
  | succ n ih =>
    rw [history, expanded_step, Finset.card_insert_of_notMem (next_not_expanded _ _ _), ih]

theorem depthBound_history (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    depthBound (expanded (history ν ρ Y n)) ≤ n := by
  induction n with
  | zero => simp [history, expanded, depthBound]
  | succ n ih =>
    rw [history, expanded_step]
    change (insert _ _ : Finset Node).sup List.length ≤ n+1
    rw [Finset.sup_insert]
    apply max_le
    · exact (select_length_le _ _).trans (by omega)
    · exact ih.trans (by omega)

theorem action_depth_le (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    (action ν ρ Y n).length ≤ n+1 :=
  (select_length_le _ _).trans (Nat.add_le_add_right (depthBound_history ν ρ Y n) 1)

/-- The stored history is precisely the generated action/reward trace. -/
theorem history_eq_ofFn (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    history ν ρ Y n = List.ofFn (fun i : Fin n => (action ν ρ Y i, Y i)) := by
  induction n with
  | zero => simp [history]
  | succ n ih =>
    change history ν ρ Y n ++ [(action ν ρ Y n, Y n)] = _
    rw [ih, List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.coe_castSucc, Fin.val_last]

theorem action_ne_of_lt (ν ρ : ℝ) (Y : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    action ν ρ Y n ≠ action ν ρ Y m := by
  intro he
  have h := next_not_previously_played ν ρ (history ν ρ Y n)
  apply h
  change action ν ρ Y n ∈ _
  rw [he, history_eq_ofFn]
  simp only [List.map_ofFn, Function.comp_def, List.mem_ofFn]
  exact ⟨⟨m, hmn⟩, rfl⟩

theorem action_injective (ν ρ : ℝ) (Y : ℕ → ℝ) : Function.Injective (action ν ρ Y) := by
  intro m n he
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (action_ne_of_lt ν ρ Y h he.symm)
  · exact h
  · exact False.elim (action_ne_of_lt ν ρ Y h he)

end BanditRLProof.HOO
