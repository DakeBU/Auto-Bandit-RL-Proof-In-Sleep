# Native heterogeneous causal sampling and expected simple regret

Source: Lattimore, Lattimore and Reid, *Causal Bandits: Learning Good Interventions via Causal Inference*, NIPS 2016, Algorithm 2 and Theorem 3; Proposition 4 for the uniform-design corollary. Source versions and hashes remain frozen in the causal contract. This extends the [common-alphabet performance chain](extended-topics-causal-sampling.md).

## Mathematical objects and algorithm

Node i has its own nonempty finite type V_i. A topologically ordered table takes a dependent strict-prefix history and returns a probability mass function on V_i. The native joint recursively draws this history and its last coordinate; it is defined before any encoding. Replacing a selected table with a point mass gives the actual intervention distribution. Its joint mass is the product of those replaced local table masses, and its total mass is one.

For a fixed covered allocation eta, every round draws action a from eta and then a full assignment from that intervention law. The finite product of these actual round laws is the sample law. The estimator uses only the observed reward bit and reward-parent configuration, together with the known parent marginals P_a and Q = sum_b eta_b P_b. Recording intervention coordinates adds only values already fixed by the chosen action. The formula is Y(P_a/Q) times the indicator P_a/Q <= B. The recommendation is the least maximizer of its sample average under the supplied action order.

## Representation proof and reusable interfaces

For any nodewise encoding with a left-inverse decoder, induction on the native joint proves that the encoded joint is its pushforward. Intervention replacement commutes with this construction. Projection to the reward parents gives the parent-law pushforward. Injectivity preserves masses, likelihood ratios, covered supports, weighted bits, second moments and the exact design cost m. Coverage transport is proved in the forward direction; no unproved equivalence is needed.

The product-measure pushforward identifies the full sample law, not only its single-round marginals. Statistics, estimates, fixed-order recommendations and simple regret agree on each encoded trajectory. The reward means and the expected regret agree by integration under these actual laws. For finite nonempty node types the proof constructs the common alphabet W = product_i V_i: encode a value by updating coordinate i in a fixed default tuple, and decode by projecting coordinate i. The final native theorem therefore asks for neither W nor a codec. The optimizer remains the attained native design-cost optimizer; no numerical solver or actual-regret dominance theorem is claimed.

## Performance endpoint and source delta

Let K be the number of actions, T > 0, L = log(2TK), m the exact covered design cost and B = sqrt(mT/L). The native actual expected simple regret satisfies

$$ E[R_T] \le (2\sqrt{2}+7)\sqrt{mL/T}+1/T, \qquad 0\le E[R_T]\le1. $$

The explicit rate constant 3 sqrt(2)+7 absorbs the residual using the proved lower bound L >= 1/2. Uniform sampling uses its actual m in the threshold and relaxes m to K only on the right side. The optimal-design corollary actually samples from the native optimal allocation. Confidence comes from the previously reviewed producer, with no tail/confidence assumption supplied by the caller.

The source's smaller displayed coefficient and good-event probability direction were explicitly repaired in that producer; transport does not remove these deltas. The source has a binary reward node. The interface allows any finite reward-node type with a binary readout, covering the literal binary source case and extending it to event readouts; it does not cover arbitrary real rewards. Each node is nonempty, the reward node is not intervened upon, and coverage and exact known parent marginals remain explicit. No separate native information-access type system or cross-model information-invariance theorem is claimed.

## Concrete heterogeneous check and remaining work

The canary has X in Fin 3, Y in Fin 2, X uniform under observation, and Pr(Y=1|X=x)=3/4 for x=2 and 1/4 otherwise. Its three ordered actions are observation, do(X=0), and do(X=2). Actual joint factorization and integration yield means 5/12, 1/4, and 3/4. Its uniform bound is instantiated for every T>0. This is an additional heterogeneous check, not a replacement for the frozen three-node noisy canary.

The four transport modules have independent blind/source acceptance with explicit deltas. The separate native-law and canary supplement also has independent blind/source acceptance with explicit deltas. Exact file and report hashes are recorded in runs/extended-topics-20260919/causal-heterogeneous-review.json. Focused compilation passes 3608 jobs with only standard Lean axioms on the printed endpoints; shared root (9029 jobs), Tests (9130 jobs), full harness (437 tests, 7 skips), local site and shared mapping checks pass. The mapping contains 27 reviewed declarations with verified generated destinations. The separate [exact noisy diagnostics](extended-topics-causal-noisy-diagnostics.md) now closes the original noisy canary's concentrated allocation/cost/bias/conditional-mean/T=1/uncovered obligations. Parallel-design allocation and its witness, remaining source screening and ICLR evidence remain open. The causal topic and all-ten-topic Goal are incomplete; no main merge or deployment is claimed.

## Exact Lean implementation

<details>
<summary>BanditRLProof/Algorithms/CausalHeterogeneous.lean</summary>

```lean
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

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CausalImportanceTransport.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalAllocation
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Importance ratios and design cost under injective finite-state encoding. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory
set_option autoImplicit false

variable {A Z U : Type*}

theorem mass_map_injective (p : PMF Z) (e : Z → U) (he : Function.Injective e) (z : Z) :
    mass (p.map e) (e z) = mass p z := by
  unfold mass
  apply congrArg ENNReal.toReal
  rw [PMF.map_apply, tsum_eq_single z]
  · simp
  · intro b hb
    simp [he.eq_iff, Ne.symm hb]

theorem ratio_map_injective (p q : PMF Z) (e : Z → U) (he : Function.Injective e) (z : Z) :
    ratio (p.map e) (q.map e) (e z) = ratio p q z := by
  simp only [ratio, mass_map_injective _ e he]

theorem mixture_map (eta : PMF A) (p : A → PMF Z) (e : Z → U) :
    mixture eta (fun a => (p a).map e) = (mixture eta p).map e := by
  simp only [mixture, PMF.map_bind]

theorem covers_map_injective (p : A → PMF Z) (q : PMF Z) (hc : Covers p q)
    (e : Z → U) (he : Function.Injective e) :
    Covers (fun a => (p a).map e) (q.map e) := by
  intro a u hu
  have hsupport : u ∈ ((p a).map e).support := by
    change ((p a).map e) u ≠ 0
    intro hzero
    exact hu (by simp [mass, hzero])
  rw [PMF.mem_support_map_iff] at hsupport
  obtain ⟨z, _, rfl⟩ := hsupport
  rw [mass_map_injective _ e he] at hu ⊢
  exact hc a z hu

theorem weightedBit_map_injective (p q : PMF Z) (e : Z → U) (he : Function.Injective e)
    (B : ℝ) (z : Z) (y : Bool) :
    weightedBit (p.map e) (q.map e) B (e z,y) = weightedBit p q B (z,y) := by
  simp only [weightedBit, ratio_map_injective _ _ e he]

variable [Fintype Z] [Fintype U] [MeasurableSpace Z] [MeasurableSingletonClass Z]
variable [MeasurableSpace U] [MeasurableSingletonClass U]

theorem secondMoment_map_injective (p q : PMF Z) (e : Z → U) (he : Function.Injective e) :
    secondMoment (p.map e) (q.map e) = secondMoment p q := by
  have hi := integral_map (μ := p.toMeasure) (φ := e)
    (f := fun u => ratio (p.map e) (q.map e) u)
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable
  rw [PMF.toMeasure_map e p Measurable.of_discrete] at hi
  simp only [ratio_map_injective _ _ e he, PMF.integral_eq_sum, smul_eq_mul] at hi
  exact hi

variable [Fintype A] [Nonempty A]

theorem designCost_map_injective (p : A → PMF Z) (eta : PMF A)
    (e : Z → U) (he : Function.Injective e) :
    designCost (fun a => (p a).map e) eta = designCost p eta := by
  unfold designCost
  simp only [mixture_map, secondMoment_map_injective _ _ e he]

end BanditRLProof.Causal

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CausalHeterogeneousSampling.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalHeterogeneous
import BanditRLProof.Algorithms.CausalImportanceTransport
import BanditRLProof.Algorithms.CausalAllocationRegret

/-! Native heterogeneous observations, estimates, and their actual sampling law. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {n : ℕ} {V : Fin n → Type*} {W A : Type*}
variable [∀ i, Fintype (V i)] [∀ i, MeasurableSpace (V i)]
variable [∀ i, MeasurableSingletonClass (V i)]
variable [Fintype W] [Inhabited W] [MeasurableSpace W] [MeasurableSingletonClass W]
variable [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def NodeGraphModel.roundLaw (g : NodeGraphModel V)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A) :
    PMF (A × ((i : Fin n) → V i)) :=
  eta.bind fun a => (nodeJoint (nodeIntervene g.table (actions a))).map fun x => (a,x)

noncomputable def NodeGraphModel.sampleLaw (g : NodeGraphModel V)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A) (T : ℕ) :
    Measure (Fin T → A × ((i : Fin n) → V i)) :=
  Measure.pi fun _ : Fin T => (g.roundLaw actions eta).toMeasure

instance NodeGraphModel.sampleLaw_isProbabilityMeasure (g : NodeGraphModel V)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A) (T : ℕ) :
    IsProbabilityMeasure (g.sampleLaw actions eta T) := by unfold sampleLaw; infer_instance

def NodeCodec.encodeRound (c : NodeCodec V W) (ax : A × ((i : Fin n) → V i)) :
    A × (Fin n → W) := (ax.1,c.encodeAssignment ax.2)

def NodeCodec.encodeSamples (c : NodeCodec V W) {T : ℕ}
    (w : Fin T → A × ((i : Fin n) → V i)) : Fin T → A × (Fin n → W) :=
  fun t => c.encodeRound (w t)

theorem NodeGraphModel.roundLaw_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A) :
    (g.roundLaw actions eta).map c.encodeRound =
      (g.encodeGraph c).roundLaw (fun a => c.encodeAction (actions a)) eta := by
  simp only [roundLaw, GraphModel.roundLaw, PMF.map_bind,
    g.intervention_joint_encoded, PMF.map_comp]
  rfl

theorem NodeGraphModel.sampleLaw_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A) (T : ℕ) :
    (g.sampleLaw actions eta T).map c.encodeSamples =
      (g.encodeGraph c).sampleLaw (fun a => c.encodeAction (actions a)) eta T := by
  unfold sampleLaw GraphModel.sampleLaw NodeCodec.encodeSamples
  rw [Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable)]
  congr 1
  funext t
  rw [PMF.toMeasure_map c.encodeRound _ Measurable.of_discrete, g.roundLaw_encoded]

def NodeGraphModel.observation (g : NodeGraphModel V) (i : Fin n) (rewardBit : V i → Bool)
    (ax : A × ((i : Fin n) → V i)) : g.ParentConfig i × Bool :=
  (g.parentConfig i (nodeHistory ax.2 i), rewardBit (ax.2 i))

noncomputable def NodeGraphModel.sampleWeightedBit (g : NodeGraphModel V)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (a : A) (B : ℝ) {T : ℕ} (t : Fin T)
    (w : Fin T → A × ((i : Fin n) → V i)) : ℝ :=
  weightedBit (g.parentLaw (actions a) i) (mixture eta (fun b => g.parentLaw (actions b) i))
    B (g.observation i rewardBit (w t))

noncomputable def NodeGraphModel.sampleEstimate (g : NodeGraphModel V)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (a : A) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((i : Fin n) → V i)) : ℝ :=
  (∑ t : Fin T, g.sampleWeightedBit actions eta i rewardBit a B t w) / T

theorem NodeGraphModel.sampleWeightedBit_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (a : A) (B : ℝ) {T : ℕ} (t : Fin T)
    (w : Fin T → A × ((i : Fin n) → V i)) :
    (g.encodeGraph c).sampleWeightedBit (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) eta i a B t (c.encodeSamples w) =
      g.sampleWeightedBit actions eta i rewardBit a B t w := by
  have he : Function.Injective (g.encodeParent c i) :=
    Function.LeftInverse.injective (g.decode_encodeParent c i)
  simp only [GraphModel.sampleWeightedBit, g.parentLaw_encoded, mixture_map]
  have ho : (g.encodeGraph c).observation (fun v => rewardBit (c.decode i v)) i
      (c.encodeSamples w t) =
      (g.encodeParent c i (g.observation i rewardBit (w t)).1,
        (g.observation i rewardBit (w t)).2) := by
    apply Prod.ext
    · rfl
    · exact congrArg rewardBit (c.decode_encode i ((w t).2 i))
  rw [ho, weightedBit_map_injective _ _ _ he]
  rfl

theorem NodeGraphModel.sampleEstimate_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (a : A) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((i : Fin n) → V i)) :
    (g.encodeGraph c).sampleEstimate (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) eta i a B (c.encodeSamples w) =
      g.sampleEstimate actions eta i rewardBit a B w := by
  simp only [GraphModel.sampleEstimate, sampleEstimate, g.sampleWeightedBit_encoded]

theorem NodeGraphModel.designCost_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (i : Fin n) → Option (V i)) (eta : PMF A) (i : Fin n) :
    designCost (fun a => (g.encodeGraph c).parentLaw (c.encodeAction (actions a)) i) eta =
      designCost (fun a => g.parentLaw (actions a) i) eta := by
  simp only [g.parentLaw_encoded]
  exact designCost_map_injective _ _ _ (Function.LeftInverse.injective (g.decode_encodeParent c i))

end BanditRLProof.Causal

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CausalHeterogeneousRegret.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalHeterogeneousSampling

/-! Actual expected simple regret on native heterogeneous finite DAGs. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {n : ℕ} {V : Fin n → Type*} {W A : Type*}
variable [∀ i, Fintype (V i)] [∀ i, Inhabited (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]
variable [Fintype W] [Inhabited W] [MeasurableSpace W] [MeasurableSingletonClass W]
variable [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def NodeGraphModel.rewardMean (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool) (a : A) : ℝ :=
  ∫ x, (if rewardBit (x i) then (1:ℝ) else 0) ∂(nodeJoint (nodeIntervene g.table (actions a))).toMeasure

theorem NodeGraphModel.rewardMean_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool)
    (a : A) (hi : actions a i = none) :
    (g.encodeGraph c).rewardMean (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) i a = g.rewardMean actions i rewardBit a := by
  rw [GraphModel.rewardMean_eq_integral _ _ _ _ _ (by simp [NodeCodec.encodeAction, hi]),
    g.intervention_joint_encoded,
    ← PMF.toMeasure_map c.encodeAssignment _ Measurable.of_discrete]
  rw [integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  simp only [NodeCodec.encodeAssignment, c.decode_encode]
  rfl

noncomputable def NodeGraphModel.sampleRecommendation (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((j : Fin n) → V j)) : A :=
  orderedArgmax (fun a => g.sampleEstimate actions eta i rewardBit a B w)

noncomputable def NodeGraphModel.simpleRegret (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((j : Fin n) → V j)) : ℝ :=
  g.rewardMean actions i rewardBit (FiniteRealArgmax.choose (g.rewardMean actions i rewardBit)) -
    g.rewardMean actions i rewardBit (g.sampleRecommendation actions eta i rewardBit B w)

theorem NodeGraphModel.sampleRecommendation_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (B : ℝ) {T : ℕ}
    (w : Fin T → A × ((j : Fin n) → V j)) :
    (g.encodeGraph c).sampleRecommendation (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) eta i B (c.encodeSamples w) =
      g.sampleRecommendation actions eta i rewardBit B w := by
  simp only [GraphModel.sampleRecommendation, sampleRecommendation, g.sampleEstimate_encoded]

theorem NodeGraphModel.simpleRegret_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none)
    (B : ℝ) {T : ℕ} (w : Fin T → A × ((j : Fin n) → V j)) :
    (g.encodeGraph c).simpleRegret (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) eta i B (c.encodeSamples w) =
      g.simpleRegret actions eta i rewardBit B w := by
  have hm : (g.encodeGraph c).rewardMean (fun v => rewardBit (c.decode i v))
      (fun a => c.encodeAction (actions a)) i = g.rewardMean actions i rewardBit :=
    funext fun a => g.rewardMean_encoded c actions i rewardBit a (hi a)
  simp only [GraphModel.simpleRegret, simpleRegret, hm, g.sampleRecommendation_encoded]

theorem NodeGraphModel.expected_simpleRegret_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none) (B : ℝ) (T : ℕ) :
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) =
      ∫ w, (g.encodeGraph c).simpleRegret (fun v => rewardBit (c.decode i v))
        (fun a => c.encodeAction (actions a)) eta i B w
        ∂(g.encodeGraph c).sampleLaw (fun a => c.encodeAction (actions a)) eta T := by
  rw [← g.sampleLaw_encoded c actions eta T,
    integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  simp only [g.simpleRegret_encoded c actions eta i rewardBit hi]

theorem NodeGraphModel.covers_encoded (g : NodeGraphModel V) (c : NodeCodec V W)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A) (i : Fin n)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i))) :
    Covers (fun a => (g.encodeGraph c).parentLaw (c.encodeAction (actions a)) i)
      (mixture eta (fun a => (g.encodeGraph c).parentLaw (c.encodeAction (actions a)) i)) := by
  simp only [g.parentLaw_encoded, mixture_map]
  exact covers_map_injective _ _ hc _ (Function.LeftInverse.injective (g.decode_encodeParent c i))

/-- Native finite-node theorem: no codec or common-alphabet premise is required. -/
theorem NodeGraphModel.expected_simpleRegret_source_bound (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i))) (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T)+1/(T:ℝ) := by
  let c := productNodeCodec V
  have hi' : ∀ a, c.encodeAction (actions a) i = none := by
    intro a
    simp [NodeCodec.encodeAction, hi a]
  have h := (g.encodeGraph c).expected_simpleRegret_source_bound
    (fun v => rewardBit (c.decode i v)) (fun a => c.encodeAction (actions a)) eta i hi'
    (g.covers_encoded c actions eta i hc) T hT
  dsimp only at h ⊢
  rw [g.designCost_encoded] at h
  rw [g.expected_simpleRegret_encoded c actions eta i rewardBit hi]
  exact h

theorem NodeGraphModel.expected_simpleRegret_bounds (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none) (B : ℝ) (T : ℕ) :
    0 ≤ (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ∧
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤ 1 := by
  let c := productNodeCodec V
  rw [g.expected_simpleRegret_encoded c actions eta i rewardBit hi]
  exact (g.encodeGraph c).expected_simpleRegret_bounds _ _ _ _ _ _

theorem NodeGraphModel.expected_simpleRegret_explicit_rate (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (eta : PMF A)
    (i : Fin n) (rewardBit : V i → Bool) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i))) (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (3*Real.sqrt 2+7)*Real.sqrt (m*L/T) := by
  have h := g.expected_simpleRegret_source_bound actions eta i rewardBit hi hc T hT
  have hr := sourceResidual_le_scale _ (designCost_ge_one _ eta hc)
    T (Fintype.card A) hT Fintype.card_pos
  dsimp only at h ⊢
  linarith

theorem NodeGraphModel.expected_simpleRegret_uniform (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool)
    (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype A
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((Fintype.card A:ℝ)*L/T)+1/(T:ℝ) := by
  have h := g.expected_simpleRegret_source_bound actions (PMF.uniformOfFintype A)
    i rewardBit hi (uniform_covers _) T hT
  dsimp only at h ⊢
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (uniform_designCost_le_card _)
    (sourceLog_pos T _ hT Fintype.card_pos).le

theorem NodeGraphModel.expected_simpleRegret_optimal (g : NodeGraphModel V)
    (actions : A → (j : Fin n) → Option (V j)) (i : Fin n) (rewardBit : V i → Bool)
    (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let p := fun a => g.parentLaw (actions a) i
    let eta := optimalAllocation p
    let m := designCost p eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret actions eta i rewardBit B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T)+1/(T:ℝ) :=
  g.expected_simpleRegret_source_bound actions _ i rewardBit hi (optimalAllocation_covers _) T hT

end BanditRLProof.Causal

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CausalHeterogeneousLaw.lean</summary>

```lean
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

```

</details>

<details>
<summary>Tests/CausalHeterogeneousCanary.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalHeterogeneousRegret
import BanditRLProof.Algorithms.CausalHeterogeneousLaw

/-! A three-valued parent and a two-valued noisy reward; a genuinely dependent state space. -/
namespace Tests.CausalHeterogeneousCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

abbrev Values (i : Fin 2) := Fin (if i = 0 then 3 else 2)
instance valuesSize_neZero (i : Fin 2) : NeZero (if i = 0 then 3 else 2) :=
  ⟨by split_ifs <;> decide⟩

noncomputable def noisyReward (x : Fin 3) : PMF (Fin 2) :=
  (PMF.bernoulli (if x = 2 then 3/4 else 1/4) (by split_ifs <;> norm_num [div_le_iff₀])).map
    (fun b => if b then 1 else 0)

noncomputable def tables : NodeTables Values := by
  refine Fin.cases (fun _ => PMF.uniformOfFintype (Fin 3)) ?_
  exact Fin.cases (fun h => noisyReward (h ⟨0, by decide⟩)) (fun k => Fin.elim0 k)

noncomputable def graph : NodeGraphModel Values where
  parents _ := Finset.univ
  table := tables
  local_table := by
    intro i h h' heq
    have hh : h = h' := funext fun j => heq j (Finset.mem_univ _)
    rw [hh]

def actions (a : Fin 3) : (i : Fin 2) → Option (Values i) := by
  refine Fin.cases (if a = 0 then none else some (if a = 1 then 0 else 2)) ?_
  exact Fin.cases none (fun k => Fin.elim0 k)

def rewardBit (x : Values 1) : Bool := decide (x = 1)

theorem reward_untouched (a : Fin 3) : actions a 1 = none := rfl

@[simp] theorem actions_zero (a : Fin 3) : actions a 0 =
    (if a = 0 then none else some (if a = 1 then 0 else 2)) := rfl

@[simp] theorem tables_zero (h : NodeHistory Values 0) :
    tables 0 h = PMF.uniformOfFintype (Fin 3) := rfl

@[simp] theorem tables_one (h : NodeHistory Values 1) :
    tables 1 h = noisyReward (h ⟨0, by decide⟩) := rfl

def assignmentEquiv : ((i : Fin 2) → Values i) ≃ Fin 3 × Fin 2 where
  toFun x := (x 0,x 1)
  invFun xy := by
    refine Fin.cases xy.1 ?_
    exact Fin.cases xy.2 (fun k => Fin.elim0 k)
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv xy := by rcases xy with ⟨x,y⟩; rfl

@[simp] theorem assignment_zero (xy : Fin 3 × Fin 2) :
    assignmentEquiv.symm xy 0 = xy.1 := rfl

@[simp] theorem assignment_one (xy : Fin 3 × Fin 2) :
    assignmentEquiv.symm xy 1 = xy.2 := rfl

theorem actual_joint (a : Fin 3) (x : (i : Fin 2) → Values i) :
    nodeJoint (nodeIntervene graph.table (actions a)) x =
      (if a = 0 then 1/3 else if x 0 = (if a = 1 then 0 else 2) then 1 else 0) *
        noisyReward (x 0) (x 1) := by
  rw [nodeIntervention_factorization]
  fin_cases a <;> norm_num [Fin.prod_univ_two, graph, reward_untouched, nodeHistory,
    PMF.uniformOfFintype_apply]
  · change PMF.uniformOfFintype (Fin 3) (x 0) * noisyReward (x 0) (x 1) = _
    norm_num [PMF.uniformOfFintype_apply]
  · rfl
  · rfl

theorem reward_means (a : Fin 3) : graph.rewardMean actions 1 rewardBit a =
    if a = 0 then 5/12 else if a = 1 then 1/4 else 3/4 := by
  rw [NodeGraphModel.rewardMean, PMF.integral_eq_sum, ← Equiv.sum_comp assignmentEquiv.symm]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    actual_joint, assignment_zero, assignment_one]
  dsimp [rewardBit, Values, noisyReward]
  fin_cases a <;>
    norm_num [rewardBit, noisyReward, PMF.map_apply,
      tsum_fintype, Fintype.sum_bool, PMF.bernoulli_apply, smul_eq_mul,
      ENNReal.toReal_mul, Fin.ext_iff, Values]

theorem uniform_actual_rate (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype (Fin 3)
    let m := designCost (fun a => graph.parentLaw (actions a) 1) eta
    let L := sourceLog T 3
    let B := sourceThreshold m T L
    (∫ w, graph.simpleRegret actions eta 1 rewardBit B w ∂graph.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (3*L/T)+1/(T:ℝ) := by
  simpa only [Fintype.card_fin] using graph.expected_simpleRegret_uniform actions
    1 rewardBit reward_untouched T hT

#print axioms actual_joint
#print axioms reward_means
#print axioms uniform_actual_rate
#print axioms NodeGraphModel.expected_simpleRegret_source_bound
#print axioms NodeGraphModel.expected_simpleRegret_explicit_rate

end Tests.CausalHeterogeneousCanary

```

</details>
