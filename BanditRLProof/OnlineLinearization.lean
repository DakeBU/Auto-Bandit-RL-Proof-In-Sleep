import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineLearningRegret
/-!
# Causal convex-to-linear regret reduction
Orabona arXiv:1912.13213v10 Section 2.3, printed 22 / PDF 34.
An exogenous deterministic learner reads only finite past vector feedback.
The observed current loss supplies an actual support after the current output;
that vector is appended to the same recursion. Reconstructed output history
agrees with every played point. The linear comparator regret uses that same
learner and generated vector sequence. A universal OLO guarantee is an input
to performance transport; this module does not assert such a guarantee for
an arbitrary learner. Played legality suffices for the ambient comparison;
feasible/canonical adapters implement OCO on the shared domain. Properness
and global supports justify finite loss values before EReal.toReal. No bounded
V, randomized law, independence, executable oracle or universal optimality
claim. Time zero is source round one; T=0 is an algebraic extension. Causality
holds with common fixed policies and equal strict-past whole losses; external
policy selection is not given a probabilistic independence constraint.
These structural identities are library refinements, not numbered source results.
-/
noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace BanditRL.OnlineLinearization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev LinearPolicy := (t : ℕ) → (Fin t → E) → E
abbrev SupportPolicy := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)
def Feasible (V : Domain (E := E)) (A : LinearPolicy (E := E)) : Prop :=
  ∀ t h, A t h ∈ V.carrier
/-- Reconstruct all outputs from a finite strict-past vector history. -/
def outputHistory (A : LinearPolicy (E := E)) {t : ℕ} (h : Fin t → E) : Fin (t + 1) → E :=
  fun i => A i.val (fun j => h ⟨j.val, by omega⟩)
/-- The current support is appended only after the current output has been made. -/
def history (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) : (t : ℕ) → Fin t → E :=
  Nat.rec (motive := fun t => Fin t → E) Fin.elim0
    (fun t h => Fin.snoc h (p t (fun i => loss i.val) (outputHistory A h) (loss t)))
def output (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (t : ℕ) : E := A t (history A loss p t)
def selected (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (outputHistory A (history A loss p t)) (loss t)
def LegalFeedback (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected A loss p t ∈ SourceSubdifferential (loss t) (output A loss p t)
def linearRun (A : LinearPolicy (E := E)) (g : ℕ → E) (t : ℕ) : E :=
  A t (fun i => g i.val)
def linearLoss (g x : E) : ℝ := inner ℝ g x
def regret (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output A loss p t)).toReal - (loss t u).toReal)
theorem outputHistory_last (A : LinearPolicy (E := E)) (t : ℕ) (h : Fin t → E) :
    outputHistory A h (Fin.last t) = A t h := by
  rfl

theorem history_zero (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) :
    history A loss p 0 = Fin.elim0 := by
  rfl

theorem history_succ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) :
    history A loss p (t + 1) = Fin.snoc (history A loss p t) (selected A loss p t) := by
  rfl

theorem history_castSucc (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t) :
    history A loss p (t + 1) i.castSucc = history A loss p t i := by
  rw [history_succ, Fin.snoc_castSucc]

theorem history_selected (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t) :
    history A loss p t i = selected A loss p i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [history_succ, Fin.snoc_last, Fin.val_last]
    · rw [history_castSucc]
      exact ih j

theorem output_linear_run (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) :
    output A loss p t = linearRun A (selected A loss p) t := by
  unfold output linearRun
  congr 1
  funext i
  exact history_selected A loss p t i

theorem outputHistory_played (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin (t + 1)) :
    outputHistory A (history A loss p t) i = output A loss p i.val := by
  unfold outputHistory output
  congr 1
  funext j
  rw [history_selected, history_selected]

theorem output_mem (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) :
    output A loss p t ∈ V.carrier := by
  exact hA t (history A loss p t)

theorem history_prefix (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s) :
    history A loss p t = history A loss' p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun s hs => hloss s (Nat.lt_succ_of_lt hs))
    have hpast : (fun i : Fin t => loss i.val) = fun i : Fin t => loss' i.val := by
      funext i
      exact hloss i.val (Nat.lt_succ_of_lt i.isLt)
    rw [history_succ, history_succ]
    unfold selected
    rw [hh, hpast, hloss t (Nat.lt_succ_self t)]

theorem output_prefix (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s) :
    output A loss p t = output A loss' p t := by
  exact congrArg (A t) (history_prefix A loss loss' p t hloss)

theorem oracle_feedback (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (hp : BanditRL.OnlineSubgradientPolicy.OracleLaw V p) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback A loss p T := by
  intro t ht
  have hlast : outputHistory A (history A loss p t) (Fin.last t) ∈ V.carrier := by
    rw [outputHistory_last]
    exact hA t (history A loss p t)
  simpa only [selected, outputHistory_last, output] using
    hp t (fun i => loss i.val) (outputHistory A (history A loss p t)) (loss t)
      (hloss t ht) hlast

theorem canonical_feedback (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy T := by
  exact oracle_feedback V A hA loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy
    (BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal V) T hloss

theorem trajectory_finite_loss (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (t : ℕ) (ht : t < T) :
    loss t (output A loss p t) = ((loss t (output A loss p t)).toReal : EReal) := by
  exact BanditRL.OnlineSubgradientDescent.finite_loss V (loss t) (hloss t ht)
    (output A loss p t) (output_mem V A hA loss p t)

theorem support_gap (V : Domain (E := E)) (f : E → EReal) (hf : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f) (x g u : E) (hu : u ∈ V.carrier) (hg : g ∈ SourceSubdifferential f x) :
    (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u) := by
  simpa only [one_mul] using
    (BanditRL.OnlineSubgradientDescent.lemma_2_31 V f hf 1 (by norm_num) x u hu g hg).1

theorem linearLoss_gap (g x u : E) :
    linearLoss g x - linearLoss g u = inner ℝ g (x - u) := by
  exact (inner_sub_right g x u).symm

theorem regret_comparison (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback A loss p T) (u : E) (hu : u ∈ V.carrier) :
    regret A loss p u T ≤ BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (selected A loss p t)) (linearRun A (selected A loss p)) u T := by
  unfold regret
  rw [BanditRL.OnlineLearning.comparatorRegret_eq_sum]
  apply Finset.sum_le_sum
  intro t ht
  rw [linearLoss_gap, ← output_linear_run A loss p t]
  exact support_gap V (loss t) (hloss t (Finset.mem_range.mp ht))
    (output A loss p t) (selected A loss p t) u hu (hlegal t (Finset.mem_range.mp ht))

theorem regret_transfer (V : Domain (E := E)) (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback A loss p T) (B : (ℕ → E) → E → ℕ → ℝ) (hB : ∀ g u, u ∈ V.carrier → BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (g t)) (linearRun A g) u T ≤ B g u T) (u : E) (hu : u ∈ V.carrier) :
    regret A loss p u T ≤ B (selected A loss p) u T := by
  exact (regret_comparison V A loss p T hloss hlegal u hu).trans
    (hB (selected A loss p) u hu)

theorem canonical_regret_comparison (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (u : E) (hu : u ∈ V.carrier) :
    regret A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy u T ≤ BanditRL.OnlineLearning.comparatorRegret (fun t => linearLoss (selected A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy t)) (linearRun A (selected A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy)) u T := by
  exact regret_comparison V A loss BanditRL.OnlineSubgradientPolicy.canonicalPolicy T
    hloss (canonical_feedback V A hA loss T hloss) u hu

end BanditRL.OnlineLinearization
