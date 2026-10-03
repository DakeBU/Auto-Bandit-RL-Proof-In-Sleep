import BanditRLProof.Algorithms.CausalMarginalLaw

/-! Genuinely dependent node laws and their common-alphabet encoding. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev NodeHistory {n : ℕ} (V : Fin n → Type*) (i : Fin n) :=
  (j : Fin i.val) → V ⟨j.val, lt_trans j.isLt i.isLt⟩

abbrev NodeTables {n : ℕ} (V : Fin n → Type*) :=
  (i : Fin n) → NodeHistory V i → PMF (V i)

def NodeTables.prefix {n : ℕ} {V : Fin (n+1) → Type*} (p : NodeTables V) :
    NodeTables (fun i : Fin n => V i.castSucc) := fun i => p i.castSucc

noncomputable def nodeJoint : {n : ℕ} → {V : Fin n → Type*} → NodeTables V → PMF ((i : Fin n) → V i)
  | 0, _, _ => PMF.pure (fun i => Fin.elim0 i)
  | n+1, _, p => (nodeJoint p.prefix).bind fun h =>
      (p (Fin.last n) h).bind fun x => PMF.pure (Fin.snoc h x)

structure NodeCodec {n : ℕ} (V : Fin n → Type*) (W : Type*) where
  encode : (i : Fin n) → V i → W
  decode : (i : Fin n) → W → V i
  decode_encode : ∀ i x, decode i (encode i x) = x

def NodeCodec.prefix {n : ℕ} {V : Fin (n+1) → Type*} {W : Type*}
    (c : NodeCodec V W) : NodeCodec (fun i : Fin n => V i.castSucc) W where
  encode i := c.encode i.castSucc
  decode i := c.decode i.castSucc
  decode_encode i := c.decode_encode i.castSucc

def NodeCodec.encodeAssignment {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (x : (i : Fin n) → V i) : Fin n → W := fun i => c.encode i (x i)

def NodeCodec.decodeAssignment {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (x : Fin n → W) : (i : Fin n) → V i := fun i => c.decode i (x i)

theorem NodeCodec.decode_encodeAssignment {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (x : (i : Fin n) → V i) :
    c.decodeAssignment (c.encodeAssignment x) = x := by
  funext i
  exact c.decode_encode i (x i)

noncomputable def NodeCodec.encodeTables {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (p : NodeTables V) : Tables W n := fun i h =>
  (p i (fun j => c.decode ⟨j.val, lt_trans j.isLt i.isLt⟩ (h j))).map (c.encode i)

theorem NodeCodec.encodeAssignment_snoc {n : ℕ} {V : Fin (n+1) → Type*} {W : Type*}
    (c : NodeCodec V W) (h : (i : Fin n) → V i.castSucc) (x : V (Fin.last n)) :
    c.encodeAssignment (Fin.snoc h x) = Fin.snoc (c.prefix.encodeAssignment h) (c.encode (Fin.last n) x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [encodeAssignment]
  · simp [encodeAssignment, NodeCodec.prefix]

theorem NodeCodec.joint_encodeTables {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (p : NodeTables V) :
    joint (c.encodeTables p) = (nodeJoint p).map c.encodeAssignment := by
  induction n with
  | zero =>
    simp only [joint, nodeJoint, PMF.pure_map]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [joint, nodeJoint, PMF.map_bind]
    change ((joint (c.prefix.encodeTables p.prefix)).bind _) = _
    rw [ih, PMF.bind_map]
    congr 1
    funext h
    have hdecode : (fun j : Fin n =>
        c.decode j.castSucc (c.prefix.encodeAssignment h j)) = h := by
      funext j
      exact c.decode_encode j.castSucc (h j)
    change ((p (Fin.last n) (fun j : Fin n =>
      c.decode j.castSucc (c.prefix.encodeAssignment h j))).map (c.encode (Fin.last n))).bind
      (fun x : W => PMF.pure (Fin.snoc (c.prefix.encodeAssignment h) x : Fin (n+1) → W)) = _
    rw [hdecode, PMF.bind_map, PMF.map_bind]
    congr 1
    funext x
    rw [PMF.pure_map]
    simp only [Function.comp_def, c.encodeAssignment_snoc]

theorem NodeCodec.decode_joint_encodeTables {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (p : NodeTables V) :
    (joint (c.encodeTables p)).map c.decodeAssignment = nodeJoint p := by
  rw [c.joint_encodeTables, PMF.map_comp]
  have h : c.decodeAssignment ∘ c.encodeAssignment = id := by
    funext x
    exact c.decode_encodeAssignment x
  rw [h, PMF.map_id]

/-- A finite common alphabet is constructed, not assumed: use the finite product.
Each node stores its value at its own coordinate and defaults elsewhere. -/
noncomputable def productNodeCodec {n : ℕ} (V : Fin n → Type*)
    [∀ i, Inhabited (V i)] : NodeCodec V ((i : Fin n) → V i) where
  encode i x := Function.update (fun j => (default : V j)) i x
  decode i w := w i
  decode_encode i x := by simp

noncomputable def nodeIntervene {n : ℕ} {V : Fin n → Type*} (p : NodeTables V)
    (a : (i : Fin n) → Option (V i)) : NodeTables V := fun i h =>
  match a i with
  | none => p i h
  | some x => PMF.pure x

def NodeCodec.encodeAction {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (a : (i : Fin n) → Option (V i)) : Fin n → Option W :=
  fun i => (a i).map (c.encode i)

theorem NodeCodec.encodeTables_intervene {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (p : NodeTables V) (a : (i : Fin n) → Option (V i)) :
    c.encodeTables (nodeIntervene p a) = intervene (c.encodeTables p) (c.encodeAction a) := by
  funext i h
  cases ha : a i <;> simp [encodeTables, nodeIntervene, intervene, encodeAction, ha, PMF.pure_map]

theorem NodeCodec.joint_intervene {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (p : NodeTables V) (a : (i : Fin n) → Option (V i)) :
    joint (intervene (c.encodeTables p) (c.encodeAction a)) =
      (nodeJoint (nodeIntervene p a)).map c.encodeAssignment := by
  rw [← c.encodeTables_intervene, c.joint_encodeTables]

structure NodeGraphModel {n : ℕ} (V : Fin n → Type*) where
  parents : (i : Fin n) → Finset (Fin i.val)
  table : NodeTables V
  local_table : ∀ i h h', (∀ j ∈ parents i, h j = h' j) → table i h = table i h'

noncomputable def NodeGraphModel.encodeGraph {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (g : NodeGraphModel V) (c : NodeCodec V W) : GraphModel W n where
  parents := g.parents
  table := c.encodeTables g.table
  local_table := by
    intro i h h' heq
    apply congrArg (fun p : PMF (V i) => p.map (c.encode i))
    apply g.local_table
    intro j hj
    rw [heq j hj]

theorem NodeGraphModel.intervention_joint_encoded {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (g : NodeGraphModel V) (c : NodeCodec V W) (a : (i : Fin n) → Option (V i)) :
    joint ((g.encodeGraph c).doModel (c.encodeAction a)).table =
      (nodeJoint (nodeIntervene g.table a)).map c.encodeAssignment :=
  c.joint_intervene g.table a

theorem NodeCodec.encoded_joint_valid {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (c : NodeCodec V W) (p : NodeTables V) (w : Fin n → W)
    (hw : w ∈ (joint (c.encodeTables p)).support) :
    c.encodeAssignment (c.decodeAssignment w) = w := by
  rw [c.joint_encodeTables, PMF.mem_support_map_iff] at hw
  obtain ⟨x, _, rfl⟩ := hw
  rw [c.decode_encodeAssignment]

def nodeHistory {n : ℕ} {V : Fin n → Type*} (x : (i : Fin n) → V i)
    (i : Fin n) : NodeHistory V i := fun j => x ⟨j.val, lt_trans j.isLt i.isLt⟩

abbrev NodeGraphModel.ParentConfig {n : ℕ} {V : Fin n → Type*}
    (g : NodeGraphModel V) (i : Fin n) :=
  (j : {j // j ∈ g.parents i}) → V ⟨j.val.val, lt_trans j.val.isLt i.isLt⟩

def NodeGraphModel.parentConfig {n : ℕ} {V : Fin n → Type*}
    (g : NodeGraphModel V) (i : Fin n) (h : NodeHistory V i) : g.ParentConfig i :=
  fun j => h j.val

def NodeGraphModel.encodeParent {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (g : NodeGraphModel V) (c : NodeCodec V W) (i : Fin n) (z : g.ParentConfig i) :
    (g.encodeGraph c).ParentConfig i :=
  fun j => c.encode ⟨j.val.val, lt_trans j.val.isLt i.isLt⟩ (z j)

def NodeGraphModel.decodeParent {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (g : NodeGraphModel V) (c : NodeCodec V W) (i : Fin n)
    (z : (g.encodeGraph c).ParentConfig i) : g.ParentConfig i :=
  fun j => c.decode ⟨j.val.val, lt_trans j.val.isLt i.isLt⟩ (z j)

theorem NodeGraphModel.decode_encodeParent {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (g : NodeGraphModel V) (c : NodeCodec V W) (i : Fin n) (z : g.ParentConfig i) :
    g.decodeParent c i (g.encodeParent c i z) = z := by
  funext j
  exact c.decode_encode _ _

noncomputable def NodeGraphModel.parentLaw {n : ℕ} {V : Fin n → Type*}
    (g : NodeGraphModel V) (a : (i : Fin n) → Option (V i)) (i : Fin n) :
    PMF (g.ParentConfig i) :=
  (nodeJoint (nodeIntervene g.table a)).map (fun x => g.parentConfig i (nodeHistory x i))

theorem NodeGraphModel.parentLaw_encoded {n : ℕ} {V : Fin n → Type*} {W : Type*}
    (g : NodeGraphModel V) (c : NodeCodec V W)
    (a : (i : Fin n) → Option (V i)) (i : Fin n) :
    (g.encodeGraph c).parentLaw (c.encodeAction a) i =
      (g.parentLaw a i).map (g.encodeParent c i) := by
  rw [GraphModel.parentLaw, g.intervention_joint_encoded, parentLaw, PMF.map_comp,
    PMF.map_comp]
  rfl

end BanditRLProof.Causal
