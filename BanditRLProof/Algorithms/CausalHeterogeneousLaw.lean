import BanditRLProof.Algorithms.CausalHeterogeneous

/-! Native dependent joint factorization, independent of the common-alphabet target. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false

theorem nodeJoint_snoc {n : ℕ} {V : Fin (n+1) → Type*} (p : NodeTables V)
    (h : (i : Fin n) → V i.castSucc) (x : V (Fin.last n)) :
    nodeJoint p (Fin.snoc h x) = nodeJoint p.prefix h * p (Fin.last n) h x := by
  classical
  simp only [nodeJoint, PMF.bind_apply, PMF.pure_apply, Fin.snoc_inj]
  simp only [mul_ite, mul_one, mul_zero]
  have step (a : (i : Fin n) → V i.castSucc) :
      (∑' y : V (Fin.last n), if h = a ∧ x = y then p (Fin.last n) a y else 0) =
        if h = a then p (Fin.last n) a x else 0 := by
    by_cases ha : h = a
    · simp only [ha, true_and, if_true]
      rw [tsum_eq_single x]
      · simp
      · intro y hy; simp [Ne.symm hy]
    · simp [ha]
  simp_rw [step]
  rw [tsum_eq_single h]
  · simp
  · intro a ha; simp [Ne.symm ha]

theorem nodeJoint_factorization {n : ℕ} {V : Fin n → Type*} (p : NodeTables V)
    (x : (i : Fin n) → V i) :
    nodeJoint p x = ∏ i : Fin n, p i (nodeHistory x i) (x i) := by
  induction n with
  | zero =>
    have hx : x = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simp [nodeJoint, hx, PMF.pure_apply]
  | succ n ih =>
    conv_lhs => rw [← Fin.snoc_init_self x]
    rw [nodeJoint_snoc, ih, Fin.prod_univ_castSucc]
    rfl

theorem nodeJoint_normalized {n : ℕ} {V : Fin n → Type*} (p : NodeTables V) :
    ∑' x, nodeJoint p x = 1 := (nodeJoint p).tsum_coe

theorem nodeIntervention_factorization {n : ℕ} {V : Fin n → Type*} (g : NodeGraphModel V)
    (a : (i : Fin n) → Option (V i)) (x : (i : Fin n) → V i) :
    nodeJoint (nodeIntervene g.table a) x = ∏ i : Fin n,
      (match a i with
       | none => g.table i (nodeHistory x i) (x i)
       | some v => if x i = v then 1 else 0) := by
  rw [nodeJoint_factorization]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> simp [nodeIntervene, ha, PMF.pure_apply]

end BanditRLProof.Causal
