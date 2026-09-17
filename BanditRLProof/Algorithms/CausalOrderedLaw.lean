import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Topologically ordered conditional tables and their actual joint PMF.
Interventions replace node tables before sampling the joint law. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false

abbrev Tables (V : Type*) (n : ℕ) := (i : Fin n) → (Fin i.val → V) → PMF V

def Tables.prefix {V : Type*} {n : ℕ} (p : Tables V (n+1)) : Tables V n :=
  fun i => p i.castSucc

noncomputable def joint {V : Type*} : {n : ℕ} → Tables V n → PMF (Fin n → V)
  | 0, _ => PMF.pure Fin.elim0
  | n+1, p => (joint p.prefix).bind fun h =>
      (p (Fin.last n) h).bind fun x => PMF.pure (Fin.snoc h x)

noncomputable def intervene {V : Type*} {n : ℕ} (p : Tables V n)
    (a : Fin n → Option V) : Tables V n := fun i h =>
  match a i with
  | none => p i h
  | some x => PMF.pure x

theorem intervene_none {V : Type*} {n : ℕ} (p : Tables V n) :
    intervene p (fun _ => none) = p := rfl

theorem intervene_at {V : Type*} {n : ℕ} (p : Tables V n)
    (a : Fin n → Option V) (i : Fin n) (x : V) (ha : a i = some x)
    (h : Fin i.val → V) : intervene p a i h = PMF.pure x := by
  simp [intervene, ha]

theorem joint_snoc {V : Type*} {n : ℕ} (p : Tables V (n+1))
    (h : Fin n → V) (x : V) :
    joint p (Fin.snoc h x) = joint p.prefix h * p (Fin.last n) h x := by
  classical
  simp only [joint, PMF.bind_apply, PMF.pure_apply, Fin.snoc_inj]
  simp only [mul_ite, mul_one, mul_zero]
  have step (a : Fin n → V) :
      (∑' y : V, if h = a ∧ x = y then p (Fin.last n) a y else 0) =
        if h = a then p (Fin.last n) a x else 0 := by
    by_cases ha : h = a
    · simp only [ha, true_and, if_true]
      rw [tsum_eq_single x]
      · simp
      · intro y hy
        simp [Ne.symm hy]
    · simp [ha]
  simp_rw [step]
  rw [tsum_eq_single h]
  · simp
  · intro a ha
    simp [Ne.symm ha]

def history {V : Type*} {n : ℕ} (x : Fin n → V) (i : Fin n) : Fin i.val → V :=
  fun j => x ⟨j.val, lt_trans j.isLt i.isLt⟩

theorem joint_factorization {V : Type*} {n : ℕ} (p : Tables V n) (x : Fin n → V) :
    joint p x = ∏ i : Fin n, p i (history x i) (x i) := by
  induction n with
  | zero =>
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    simp [joint, hx, PMF.pure_apply]
  | succ n ih =>
    conv_lhs => rw [← Fin.snoc_init_self x]
    rw [joint_snoc, ih, Fin.prod_univ_castSucc]
    rfl

theorem joint_normalized {V : Type*} {n : ℕ} (p : Tables V n) :
    ∑' x, joint p x = 1 := (joint p).tsum_coe

/-- Parent indices are strictly earlier in the topological order. -/
structure GraphModel (V : Type*) (n : ℕ) where
  parents : (i : Fin n) → Finset (Fin i.val)
  table : Tables V n
  local_table : ∀ i h h', (∀ j ∈ parents i, h j = h' j) → table i h = table i h'

noncomputable def GraphModel.doModel {V : Type*} {n : ℕ} (g : GraphModel V n)
    (a : Fin n → Option V) : GraphModel V n where
  parents i := if (a i).isSome then ∅ else g.parents i
  table := intervene g.table a
  local_table := by
    intro i h h' heq
    cases ha : a i with
    | none =>
      simp only [intervene, ha]
      apply g.local_table i h h'
      simpa [ha] using heq
    | some v => simp [intervene, ha]

theorem doModel_factorization {V : Type*} {n : ℕ} (g : GraphModel V n)
    (a : Fin n → Option V) (x : Fin n → V) :
    joint (g.doModel a).table x = ∏ i : Fin n,
      (match a i with
       | none => g.table i (history x i) (x i)
       | some v => if x i = v then 1 else 0) := by
  rw [joint_factorization]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> simp [GraphModel.doModel, intervene, ha, PMF.pure_apply]

theorem intervention_incompatible_zero {V : Type*} {n : ℕ} (g : GraphModel V n)
    (a : Fin n → Option V) (x : Fin n → V) (i : Fin n) (v : V)
    (ha : a i = some v) (hx : x i ≠ v) : joint (g.doModel a).table x = 0 := by
  rw [doModel_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [ha, hx]

end BanditRLProof.Causal

