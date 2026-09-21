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
