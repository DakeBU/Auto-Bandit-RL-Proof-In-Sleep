import BanditRLProof.OnlineFTRLFiniteIdentity
noncomputable section
open Set Finset
attribute [local instance] Classical.propDecidable
namespace BanditRL.OnlineFTRLCanary
abbrev E := EuclideanSpace ℝ (Fin 1)
def v (s : ℝ) : E := EuclideanSpace.single (0 : Fin 1) s
def coord (w : E) : ℝ := w 0
def X : Set E := {v 0, v 1, v 2}
def V : Set E := {v 0, v 1}
def loss (_ : ℕ) (w : E) : EReal := if w = v 3 then ⊤ else (coord w : EReal)
def psi (t : ℕ) (w : E) : ℝ := if t = 0 then (coord w)^2 else (coord w - 3)^2
def run (t : ℕ) : E := if t = 0 then v 0 else v 1
def objective (r : ℕ → E → ℝ) (t : ℕ) (w : E) : EReal :=
  (r t w : EReal) + ∑ i ∈ range t, loss i w
def otherExtension (t : ℕ) (w : E) : ℝ := if w ∈ X then psi t w else psi t w + 7
def terminalSquare (_ : ℕ) (w : E) : ℝ := (coord w)^2
def zeroRun (_ : ℕ) : E := v 0
def shiftedSquare (_ : ℕ) (w : E) : ℝ := (coord w - 1)^2

@[simp] private theorem coord_v (s : ℝ) : coord (v s) = s := by simp [coord, v]
@[simp] private theorem v_eq (a b : ℝ) : v a = v b ↔ a = b := by
  constructor
  · intro h; simpa using congrArg coord h
  · rintro rfl; rfl
private theorem hVX : V ⊆ X := by simp [V, X, Set.insert_subset_iff]
private theorem hclosed : IsClosed V := by exact (Set.finite_singleton (v 1)).insert (v 0) |>.isClosed
private theorem hnonempty : V.Nonempty := ⟨v 0, by simp [V]⟩
private theorem hbot : ∀ i < 1, ∀ w, loss i w ≠ ⊥ := by
  intro i hi w; simp only [loss]; split <;> simp
private theorem hx : ∀ t ≤ 1, run t ∈ V := by
  intro t ht; interval_cases t <;> simp [run, V]
private theorem hmin : ∀ t ≤ 1, IsMinOn (objective psi t) V (run t) := by
  intro t ht w hw
  simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl <;> interval_cases t <;>
    norm_num [objective, psi, run, loss, coord_v, v_eq] <;> norm_cast <;> norm_num
private theorem hfinite : ∀ t ≤ 1, objective psi t (run t) ≠ ⊤ := by
  intro t ht; interval_cases t <;> norm_num [objective, psi, run, loss] <;> norm_cast
  exact EReal.natCast_ne_top 5
private theorem hplayed : ∀ t < 1, loss t (run t) ≠ ⊤ := by
  intro t ht; have : t = 0 := by omega
  subst t; norm_num [loss, run]
private theorem hcomp : ∀ t < 1, loss t (v 2) ≠ ⊤ := by
  intro t ht; norm_num [loss]
private theorem initial_inf : sInf (psi 0 '' V) = 0 := by
  norm_num [V, psi, Set.image_insert_eq, Set.image_singleton]
theorem finite_nonconvex_unused_top :
    ((∑ t ∈ range 1, ((loss t (run t)).toReal - (loss t (v 2)).toReal)) =
      psi 1 (v 2) - sInf (psi 0 '' V) +
      (∑ t ∈ range 1, ((objective psi t (run t)).toReal -
        (objective psi (t + 1) (run (t + 1))).toReal + (loss t (run t)).toReal)) +
      (objective psi 1 (run 1)).toReal - (objective psi 1 (v 2)).toReal) ∧
    IsClosed V ∧ ¬ Convex ℝ V ∧ v 2 ∈ X ∧ v 2 ∉ V ∧ loss 0 (v 3) = ⊤ ∧
    (∑ t ∈ range 1, ((loss t (run t)).toReal - (loss t (v 2)).toReal)) = -2 ∧
    psi 1 (v 2) - sInf (psi 0 '' V) = 1 ∧
    (∑ t ∈ range 1, ((objective psi t (run t)).toReal -
      (objective psi (t + 1) (run (t + 1))).toReal + (loss t (run t)).toReal)) = -5 ∧
    (objective psi 1 (run 1)).toReal - (objective psi 1 (v 2)).toReal = 2 := by
  constructor
  · exact OnlineFTRL.lemma7_1_finite_values 1 1 X V hVX hclosed hnonempty psi loss hbot run (v 2) (by simp [X]) hx hmin hfinite hplayed hcomp
  · refine ⟨hclosed, ?_, ?_⟩
    · intro hc
      have hh := hc (by simp [V] : v 0 ∈ V) (by simp [V] : v 1 ∈ V)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
      simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with hh | hh
      · have := congrArg (fun w : E => w 0) hh
        norm_num [v] at this
      · have := congrArg (fun w : E => w 0) hh
        norm_num [v] at this
    · rw [initial_inf]
      norm_num [X, V, loss, run, psi, objective, ← EReal.coe_one, ← EReal.coe_add]

private theorem heq : ∀ t ≤ 1, ∀ w ∈ X, psi t w = otherExtension t w := by
  intro t ht w hw; simp [otherExtension, hw]
theorem off_domain_extension_invariance :
    ((∀ t ≤ 1, ∀ w ∈ X, objective psi t w = objective otherExtension t w) ∧
      (∀ t ≤ 1, ∀ p ∈ V,
        IsMinOn (objective psi t) V p ↔ IsMinOn (objective otherExtension t) V p) ∧
      sInf (psi 0 '' V) = sInf (otherExtension 0 '' V)) ∧
    (∀ t ≤ 1, ∀ w ∈ X, psi t w = otherExtension t w) ∧
    v 3 ∉ X ∧ psi 0 (v 3) = 9 ∧ otherExtension 0 (v 3) = 16 ∧
    psi 0 (v 3) ≠ otherExtension 0 (v 3) := by
  refine ⟨OnlineFTRL.ftrl_regularizer_restriction_invariance 1 1 X V hVX psi otherExtension loss heq, heq, ?_⟩
  norm_num [X, psi, otherExtension]
private theorem square_min : ∀ t ≤ 1, IsMinOn (objective terminalSquare t) V (v 0) := by
  intro t ht w hw
  simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl <;> interval_cases t <;>
    norm_num [objective, terminalSquare, loss] <;> norm_cast
theorem changed_terminal_same_prefix :
    (let x' := fun t => if t = 1 then v 0 else run t;
      (∀ t < 1, x' t = run t) ∧
      (∀ t ≤ 1, x' t ∈ V ∧ IsMinOn (objective terminalSquare t) V (x' t))) ∧
    run 0 = v 0 ∧ run 1 = v 1 ∧ v 0 ≠ run 1 ∧
    psi 1 (v 0) = 9 ∧ terminalSquare 1 (v 0) = 0 ∧
    objective terminalSquare 1 (v 0) = (0 : EReal) ∧
    objective terminalSquare 1 (v 1) = (2 : EReal) := by
  constructor
  · exact OnlineFTRL.ftrl_terminal_regularizer_coupled_run 1 1 X V hVX psi terminalSquare loss
      (by
        intro t ht w hw
        have ht0 : t = 0 := by omega
        subst t
        simp [psi, terminalSquare])
      run (by intro t ht; exact hx t (by omega))
      (by intro t ht; exact hmin t (by omega)) (v 0) (by simp [V]) (square_min 1 (by omega))
  · norm_num [run, psi, terminalSquare, objective, loss, ← EReal.coe_one, ← EReal.coe_add] <;> norm_cast
private theorem square_inf : sInf (terminalSquare 0 '' V) = 0 := by
  norm_num [V, terminalSquare, Set.image_insert_eq, Set.image_singleton]
theorem zero_horizon_and_nonunique_selector_boundary :
    ((∑ t ∈ range 0, ((loss t (zeroRun t)).toReal - (loss t (v 2)).toReal)) =
      terminalSquare 0 (v 2) - sInf (terminalSquare 0 '' V) +
      (∑ t ∈ range 0, ((objective terminalSquare t (zeroRun t)).toReal -
        (objective terminalSquare (t + 1) (zeroRun (t + 1))).toReal +
        (loss t (zeroRun t)).toReal)) +
      (objective terminalSquare 0 (zeroRun 0)).toReal -
      (objective terminalSquare 0 (v 2)).toReal) ∧
    (let x' := fun t => if t = 0 then v 1 else zeroRun t;
      (∀ t < 0, x' t = zeroRun t) ∧
      (∀ t ≤ 0, x' t ∈ V ∧ IsMinOn (objective shiftedSquare t) V (x' t))) ∧
    terminalSquare 0 (v 2) = 4 ∧ sInf (terminalSquare 0 '' V) = 0 ∧
    (objective terminalSquare 0 (v 2)).toReal = 4 ∧
    zeroRun 0 = v 0 ∧ v 1 ≠ zeroRun 0 ∧
    terminalSquare 0 (v 0) = 0 ∧ shiftedSquare 0 (v 0) = 1 ∧
    IsMinOn (fun _ : E => (0 : EReal)) V (v 0) ∧
    IsMinOn (fun _ : E => (0 : EReal)) V (v 1) ∧ v 0 ≠ v 1 := by
  constructor
  · exact OnlineFTRL.lemma7_1_finite_values 1 0 X V hVX hclosed hnonempty terminalSquare loss
      (by intro i hi; omega) zeroRun (v 2) (by simp [X])
      (by intro t ht; simp [zeroRun, V])
      (by
        intro t ht
        have ht0 : t = 0 := by omega
        subst t
        exact square_min 0 (by omega))
      (by
        intro t ht
        have ht0 : t = 0 := by omega
        subst t
        norm_num [objective, terminalSquare, zeroRun])
      (by intro t ht; omega) (by intro t ht; omega)
  constructor
  · exact OnlineFTRL.ftrl_terminal_regularizer_coupled_run 1 0 X V hVX terminalSquare shiftedSquare loss
      (by intro t ht; omega) zeroRun (by intro t ht; omega) (by intro t ht; omega)
      (v 1) (by simp [V]) (by
        intro w hw
        simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl <;> norm_num [objective, shiftedSquare, ← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_pow])
  · rw [square_inf]
    norm_num [terminalSquare, shiftedSquare, objective, zeroRun, IsMinOn, IsMinFilter]
end BanditRL.OnlineFTRLCanary
