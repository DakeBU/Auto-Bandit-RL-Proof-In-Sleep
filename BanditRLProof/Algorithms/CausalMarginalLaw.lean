import BanditRLProof.Algorithms.CausalOrderedLaw

/-! Marginal laws derived from topologically ordered sampling. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false

theorem joint_map_init {V : Type*} {n : ℕ} (p : Tables V (n+1)) :
    (joint p).map Fin.init = joint p.prefix := by
  simp [joint, PMF.map_bind, PMF.pure_map, Fin.init_snoc]

def take {V : Type*} {m n : ℕ} (hm : m ≤ n) (x : Fin n → V) : Fin m → V :=
  fun i => x (i.castLE hm)

def Tables.restrict {V : Type*} {m n : ℕ} (p : Tables V n) (hm : m ≤ n) :
    Tables V m := fun i => p (i.castLE hm)

theorem joint_map_take {V : Type*} {m n : ℕ} (p : Tables V n) (hm : m ≤ n) :
    (joint p).map (take hm) = joint (p.restrict hm) := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    simp only [joint, PMF.pure_map]
    congr 1
  | succ n ih =>
    by_cases heq : m = n+1
    · subst m
      change (joint p).map id = joint p
      exact PMF.map_id _
    · have hmn : m ≤ n := by omega
      have hfun : take hm = take hmn ∘ (Fin.init : (Fin (n+1) → V) → _) := rfl
      rw [hfun, ← PMF.map_comp, joint_map_init, ih p.prefix hmn]
      rfl

abbrev GraphModel.ParentConfig {V : Type*} {n : ℕ} (g : GraphModel V n)
    (i : Fin n) := {j // j ∈ g.parents i} → V

def GraphModel.parentConfig {V : Type*} {n : ℕ} (g : GraphModel V n)
    (i : Fin n) (h : Fin i.val → V) : g.ParentConfig i := fun j => h j.val

noncomputable def GraphModel.parentTable {V : Type*} [Inhabited V] {n : ℕ}
    (g : GraphModel V n) (i : Fin n) (z : g.ParentConfig i) : PMF V :=
  g.table i (fun j => if hj : j ∈ g.parents i then z ⟨j, hj⟩ else default)

theorem GraphModel.table_eq_parentTable {V : Type*} [Inhabited V] {n : ℕ}
    (g : GraphModel V n) (i : Fin n) (h : Fin i.val → V) :
    g.table i h = g.parentTable i (g.parentConfig i h) := by
  apply g.local_table
  intro j hj
  simp [parentConfig, hj]

theorem joint_map_last_pair {V Z : Type*} {n : ℕ} (p : Tables V (n+1))
    (f : (Fin n → V) → Z) :
    (joint p).map (fun x => (f (Fin.init x), x (Fin.last n))) =
      (joint p.prefix).bind (fun h => (p (Fin.last n) h).map (fun y => (f h, y))) := by
  simp [joint, PMF.map, Function.comp_def]

theorem GraphModel.last_parent_joint {V : Type*} [Inhabited V] {n : ℕ}
    (g : GraphModel V (n+1)) :
    (joint g.table).map (fun x =>
      (g.parentConfig (Fin.last n) (Fin.init x), x (Fin.last n))) =
    ((joint g.table.prefix).map (g.parentConfig (Fin.last n))).bind
      (fun z => (g.parentTable (Fin.last n) z).map (fun y => (z,y))) := by
  rw [joint_map_last_pair, PMF.bind_map]
  congr 1
  funext h
  rw [g.table_eq_parentTable]
  rfl

theorem joint_map_node_pair {V Z : Type*} {n : ℕ} (p : Tables V n)
    (i : Fin n) (f : (Fin i.val → V) → Z) :
    (joint p).map (fun x => (f (history x i), x i)) =
      (joint (p.restrict (Nat.le_of_lt i.isLt))).bind
        (fun h => (p i h).map (fun y => (f h,y))) := by
  have hp := joint_map_last_pair (p.restrict (Nat.succ_le_of_lt i.isLt)) f
  rw [← joint_map_take, PMF.map_comp] at hp
  exact hp

theorem joint_map_history {V : Type*} {n : ℕ} (p : Tables V n) (i : Fin n) :
    (joint p).map (fun x => history x i) =
      joint (p.restrict (Nat.le_of_lt i.isLt)) := joint_map_take p _

noncomputable def GraphModel.parentLaw {V : Type*} {n : ℕ}
    (g : GraphModel V n) (a : Fin n → Option V) (i : Fin n) : PMF (g.ParentConfig i) :=
  (joint (g.doModel a).table).map (fun x => g.parentConfig i (history x i))

theorem GraphModel.parentLaw_prefix {V : Type*} {n : ℕ}
    (g : GraphModel V n) (a : Fin n → Option V) (i : Fin n) :
    g.parentLaw a i =
      (joint ((g.doModel a).table.restrict (Nat.le_of_lt i.isLt))).map
        (g.parentConfig i) := by
  rw [← joint_map_history, PMF.map_comp]
  rfl

theorem GraphModel.intervention_parent_joint {V : Type*} [Inhabited V] {n : ℕ}
    (g : GraphModel V n) (a : Fin n → Option V) (i : Fin n) (hi : a i = none) :
    (joint (g.doModel a).table).map (fun x => (g.parentConfig i (history x i),x i)) =
      (g.parentLaw a i).bind (fun z => (g.parentTable i z).map (fun y => (z,y))) := by
  rw [joint_map_node_pair, g.parentLaw_prefix, PMF.bind_map]
  congr 1
  funext h
  simp only [GraphModel.doModel, intervene, hi]
  rw [g.table_eq_parentTable]
  rfl

theorem paired_mass {Z V : Type*} (p : PMF Z) (k : Z → PMF V) (z : Z) (y : V) :
    (p.bind (fun w => (k w).map (fun v => (w,v)))) (z,y) = p z * k z y := by
  classical
  have inner (w : Z) : ((k w).map (fun v => (w,v))) (z,y) =
      if z = w then k w y else 0 := by
    rw [PMF.map_apply]
    by_cases hw : z = w
    · subst w
      simp only [Prod.mk.injEq, true_and]
      rw [tsum_eq_single y]
      · simp
      · intro v hv
        simp [Ne.symm hv]
    · simp [hw]
  rw [PMF.bind_apply]
  simp_rw [inner]
  rw [tsum_eq_single z]
  · simp
  · intro w hw
    simp [Ne.symm hw]

theorem GraphModel.intervention_parent_mass {V : Type*} [Inhabited V] {n : ℕ}
    (g : GraphModel V n) (a : Fin n → Option V) (i : Fin n) (hi : a i = none)
    (z : g.ParentConfig i) (y : V) :
    ((joint (g.doModel a).table).map
      (fun x => (g.parentConfig i (history x i),x i))) (z,y) =
      g.parentLaw a i z * g.parentTable i z y := by
  rw [g.intervention_parent_joint a i hi, paired_mass]

end BanditRLProof.Causal
