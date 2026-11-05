import Mathlib

noncomputable section
open Set Finset
namespace BanditRL.OnlineFTRL

private def extendRegularizer {E : Type*} (X : Set E) (r : ℕ → X → ℝ) : ℕ → E → ℝ :=
  fun t => Function.extend Subtype.val (r t) (fun _ => 0)

private theorem extendRegularizer_restrict {E : Type*} (X : Set E)
    (r : ℕ → X → ℝ) (t : ℕ) (v : X) :
    extendRegularizer X r t v.val = r t v := by
  exact Subtype.val_injective.extend_apply (r t) (fun _ => 0) v

private theorem finite_prefix_coe {E : Type*} (loss : ℕ → E → EReal)
    (T : ℕ) (u : E) (hbot : ∀ i < T, loss i u ≠ ⊥)
    (htop : ∀ i < T, loss i u ≠ ⊤) :
    (∑ i ∈ range T, loss i u) = ((∑ i ∈ range T, (loss i u).toReal : ℝ) : EReal) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ,
      ih (fun i hi => hbot i (Nat.lt_succ_of_lt hi))
        (fun i hi => htop i (Nat.lt_succ_of_lt hi)),
      ← EReal.coe_toReal (htop n (Nat.lt_succ_self n)) (hbot n (Nat.lt_succ_self n)),
      EReal.coe_add]
    simp only [EReal.toReal_coe]

private theorem prefix_ne_bot {E : Type*} (loss : ℕ → E → EReal)
    (T : ℕ) (u : E) (hbot : ∀ i < T, loss i u ≠ ⊥) :
    (∑ i ∈ range T, loss i u) ≠ ⊥ := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    exact EReal.add_ne_bot_iff.mpr
      ⟨ih (fun i hi => hbot i (Nat.lt_succ_of_lt hi)), hbot n (Nat.lt_succ_self n)⟩

private theorem finite_used_interpretation {E : Type*}
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (T : ℕ)
    (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hFfinite : ∀ t ≤ T, (psi t (x t) : EReal) + ∑ i ∈ range t, loss i (x t) ≠ ⊤)
    (hplayed : ∀ t < T, loss t (x t) ≠ ⊤)
    (hcomp : ∀ t < T, loss t u ≠ ⊤) :
    let F := fun t v => (psi t v : EReal) + ∑ i ∈ range t, loss i v
    (∀ t ≤ T, ((F t (x t)).toReal : EReal) = F t (x t)) ∧
    (∀ t < T, ((loss t (x t)).toReal : EReal) = loss t (x t)) ∧
    (∀ t < T, ((loss t u).toReal : EReal) = loss t u) ∧
    F T u = ((psi T u + ∑ i ∈ range T, (loss i u).toReal : ℝ) : EReal) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact EReal.coe_toReal (hFfinite t ht)
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _,
        prefix_ne_bot loss t (x t) (fun i hi => hbot i (lt_of_lt_of_le hi ht) _)⟩)
  · intro t ht
    exact EReal.coe_toReal (hplayed t ht) (hbot t ht _)
  · intro t ht
    exact EReal.coe_toReal (hcomp t ht) (hbot t ht _)
  · rw [finite_prefix_coe loss T u (fun i hi => hbot i hi u) hcomp, EReal.coe_add]

theorem lemma7_1_finite_values
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn
      (fun v => (psi t v : EReal) + ∑ i ∈ Finset.range t, loss i v) V (x t))
    (hFfinite : ∀ t ≤ T,
      (psi t (x t) : EReal) + ∑ i ∈ Finset.range t, loss i (x t) ≠ ⊤)
    (hplayed : ∀ t < T, loss t (x t) ≠ ⊤)
    (hcomparator : ∀ t < T, loss t u ≠ ⊤) :
    let F := fun t v => (psi t v : EReal) + ∑ i ∈ Finset.range t, loss i v
    (∑ t ∈ Finset.range T, ((loss t (x t)).toReal - (loss t u).toReal)) =
      psi T u - sInf (psi 0 '' V) +
      (∑ t ∈ Finset.range T,
        ((F t (x t)).toReal - (F (t + 1) (x (t + 1))).toReal +
          (loss t (x t)).toReal)) +
      (F T (x T)).toReal - (F T u).toReal := by
  classical
  let F := fun t v => (psi t v : EReal) + ∑ i ∈ range t, loss i v
  change (∑ t ∈ range T, ((loss t (x t)).toReal - (loss t u).toReal)) =
    psi T u - sInf (psi 0 '' V) +
    (∑ t ∈ range T, ((F t (x t)).toReal - (F (t+1) (x (t+1))).toReal +
      (loss t (x t)).toReal)) + (F T (x T)).toReal - (F T u).toReal
  have hdata := finite_used_interpretation psi loss T x u hbot hFfinite hplayed hcomparator
  have hterminal : (F T u).toReal = psi T u + ∑ i ∈ range T, (loss i u).toReal := by
    rw [show F T u = _ from hdata.2.2.2]
    exact EReal.toReal_coe _
  have hzero : (F 0 (x 0)).toReal = psi 0 (x 0) := by simp [F]
  have hmin0 : IsMinOn (psi 0) V (x 0) := by
    intro v hv
    have h := hmin 0 (Nat.zero_le T) hv
    simpa only [sum_range_zero, add_zero, EReal.coe_le_coe_iff] using h
  have hmem : psi 0 (x 0) ∈ psi 0 '' V := ⟨x 0, hx 0 (Nat.zero_le T), rfl⟩
  have hbelow : BddBelow (psi 0 '' V) := by
    refine ⟨psi 0 (x 0), ?_⟩
    rintro v ⟨w, hw, rfl⟩
    exact hmin0 hw
  have hminimum : sInf (psi 0 '' V) = psi 0 (x 0) := by
    apply le_antisymm (csInf_le hbelow hmem)
    apply le_csInf ⟨_, hmem⟩
    rintro v ⟨w, hw, rfl⟩
    exact hmin0 hw
  have htel := Finset.sum_range_sub' (fun t => (F t (x t)).toReal) T
  rw [sum_sub_distrib, sum_add_distrib, htel, hterminal, hzero, hminimum]
  ring

theorem ftrl_regularizer_restriction_invariance
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d))) (hVX : V ⊆ X)
    (psi psi' : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (heq : ∀ t ≤ T, ∀ v ∈ X, psi t v = psi' t v) :
    let F := fun t v => (psi t v : EReal) + ∑ i ∈ Finset.range t, loss i v
    let F' := fun t v => (psi' t v : EReal) + ∑ i ∈ Finset.range t, loss i v
    (∀ t ≤ T, ∀ v ∈ X, F t v = F' t v) ∧
    (∀ t ≤ T, ∀ p ∈ V, IsMinOn (F t) V p ↔ IsMinOn (F' t) V p) ∧
    sInf (psi 0 '' V) = sInf (psi' 0 '' V) := by
  classical
  dsimp only
  have hF : ∀ t ≤ T, ∀ v ∈ X,
      (psi t v : EReal) + ∑ i ∈ range t, loss i v =
      (psi' t v : EReal) + ∑ i ∈ range t, loss i v := by
    intro t ht v hv
    rw [heq t ht v hv]
  refine ⟨hF, ?_, ?_⟩
  · intro t ht p hp
    constructor <;> intro hm v hv
    · change (psi' t p : EReal) + ∑ i ∈ range t, loss i p ≤
        (psi' t v : EReal) + ∑ i ∈ range t, loss i v
      rw [← hF t ht p (hVX hp), ← hF t ht v (hVX hv)]
      exact hm hv
    · change (psi t p : EReal) + ∑ i ∈ range t, loss i p ≤
        (psi t v : EReal) + ∑ i ∈ range t, loss i v
      rw [hF t ht p (hVX hp), hF t ht v (hVX hv)]
      exact hm hv
  · congr 1
    exact Set.image_congr (fun v hv => heq 0 (Nat.zero_le T) v (hVX hv))

theorem ftrl_terminal_regularizer_coupled_run
    (d T : ℕ)
    (X V : Set (EuclideanSpace ℝ (Fin d))) (hVX : V ⊆ X)
    (psi psi' : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (heq : ∀ t < T, ∀ v ∈ X, psi t v = psi' t v)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ t < T, x t ∈ V)
    (hmin : ∀ t < T, IsMinOn
      (fun v => (psi t v : EReal) + ∑ i ∈ Finset.range t, loss i v) V (x t))
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ V)
    (hzmin : IsMinOn
      (fun v => (psi' T v : EReal) + ∑ i ∈ Finset.range T, loss i v) V z) :
    let x' := fun t => if t = T then z else x t
    (∀ t < T, x' t = x t) ∧
    (∀ t ≤ T, x' t ∈ V ∧ IsMinOn
      (fun v => (psi' t v : EReal) + ∑ i ∈ Finset.range t, loss i v) V (x' t)) := by
  classical
  dsimp only
  refine ⟨?_, ?_⟩
  · intro t ht
    simp [ne_of_lt ht]
  · intro t ht
    by_cases he : t = T
    · subst t
      simpa using And.intro hz hzmin
    · have hlt : t < T := lt_of_le_of_ne ht he
      simp only [if_neg he]
      refine ⟨hx t hlt, ?_⟩
      intro v hv
      change (psi' t (x t) : EReal) + ∑ i ∈ range t, loss i (x t) ≤
        (psi' t v : EReal) + ∑ i ∈ range t, loss i v
      rw [← heq t hlt (x t) (hVX (hx t hlt)), ← heq t hlt v (hVX hv)]
      exact hmin t hlt hv


-- This private bridge starts with regularizers genuinely defined on the source domain X.
-- It constructs an extension, transports the supplied run and finite-use assumptions,
-- applies the sealed equality, and returns the equality entirely in subtype notation.
private theorem source_subtype_backtransport
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (r : ℕ → X → ℝ) (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (xs : ℕ → X) (u : X)
    (hx : ∀ t ≤ T, (xs t).val ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn
      (fun v : X => (r t v : EReal) + ∑ i ∈ range t, loss i v.val)
      {v : X | v.val ∈ V} (xs t))
    (hfinite : ∀ t ≤ T, (r t (xs t) : EReal) +
      ∑ i ∈ range t, loss i (xs t).val ≠ ⊤)
    (hplayed : ∀ t < T, loss t (xs t).val ≠ ⊤)
    (hcomp : ∀ t < T, loss t u.val ≠ ⊤) :
    let F := fun t (v : X) => (r t v : EReal) + ∑ i ∈ range t, loss i v.val
    (∑ t ∈ range T, ((loss t (xs t).val).toReal - (loss t u.val).toReal)) =
      r T u - sInf (r 0 '' {v : X | v.val ∈ V}) +
      (∑ t ∈ range T, ((F t (xs t)).toReal - (F (t+1) (xs (t+1))).toReal +
        (loss t (xs t).val).toReal)) +
      (F T (xs T)).toReal - (F T u).toReal := by
  classical
  let psi := extendRegularizer X r
  have hrestriction (t : ℕ) (v : X) : psi t v.val = r t v :=
    extendRegularizer_restrict X r t v
  have hminE : ∀ t ≤ T, IsMinOn
      (fun v => (psi t v : EReal) + ∑ i ∈ range t, loss i v) V (xs t).val := by
    intro t ht v hv
    change (psi t (xs t).val : EReal) + ∑ i ∈ range t, loss i (xs t).val ≤
      (psi t v : EReal) + ∑ i ∈ range t, loss i v
    let vX : X := ⟨v, hVX hv⟩
    have hm := hmin t ht (show vX ∈ {w : X | w.val ∈ V} from hv)
    change (r t (xs t) : EReal) + ∑ i ∈ range t, loss i (xs t).val ≤
      (r t vX : EReal) + ∑ i ∈ range t, loss i vX.val at hm
    change (psi t (xs t).val : EReal) + ∑ i ∈ range t, loss i (xs t).val ≤
      (psi t vX.val : EReal) + ∑ i ∈ range t, loss i vX.val
    simpa only [hrestriction t (xs t), hrestriction t vX] using hm
  have hfiniteE : ∀ t ≤ T, (psi t (xs t).val : EReal) +
      ∑ i ∈ range t, loss i (xs t).val ≠ ⊤ := by
    intro t ht
    simpa only [hrestriction] using hfinite t ht
  have himage : psi 0 '' V = r 0 '' {v : X | v.val ∈ V} := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, hVX hv⟩, hv, ?_⟩
      exact (hrestriction 0 ⟨v, hVX hv⟩).symm
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.val, hv, hrestriction 0 v⟩
  have h := lemma7_1_finite_values d T X V hVX hVclosed hV psi loss hbot
    (fun t => (xs t).val) u.val u.property hx hminE hfiniteE hplayed hcomp
  dsimp only at h ⊢
  simpa only [hrestriction, himage] using h

end BanditRL.OnlineFTRL
